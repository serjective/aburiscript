#include "parser.h"

#include "../cir/layout.h"
#include "../numeric_utils.h"
#include "../token_spelling.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

bool is_cxx_access_specifier(TokenType type) {
    return type == TokenType::PUBLIC_KW ||
           type == TokenType::PROTECTED_KW ||
           type == TokenType::PRIVATE_KW;
}

cir::RecordMemberAccess access_from_token(TokenType type) {
    switch (type) {
        case TokenType::PUBLIC_KW:
            return cir::RecordMemberAccess::Public;
        case TokenType::PROTECTED_KW:
            return cir::RecordMemberAccess::Protected;
        case TokenType::PRIVATE_KW:
            return cir::RecordMemberAccess::Private;
        default:
            return cir::RecordMemberAccess::Public;
    }
}

cir::RecordMemberAccess default_access_for(cir::RecordKind kind) {
    return kind == cir::RecordKind::Class
        ? cir::RecordMemberAccess::Private
        : cir::RecordMemberAccess::Public;
}

bool current_record_is_local(const collect::Session& session) {
    const cir::File& file = session.file();
    cir::DeclContextId context = session.current_decl_context();
    if (!context.valid() || !file.valid(context) ||
        file.decl_context(context).kind != cir::DeclContextKind::Record) {
        return false;
    }
    for (context = file.decl_context(context).parent;
         context.valid() && file.valid(context);
         context = file.decl_context(context).parent) {
        cir::DeclContextKind kind = file.decl_context(context).kind;
        if (kind == cir::DeclContextKind::Function ||
            kind == cir::DeclContextKind::Block) {
            return true;
        }
        if (kind == cir::DeclContextKind::Namespace ||
            kind == cir::DeclContextKind::TranslationUnit) {
            return false;
        }
    }
    return false;
}

bool constraint_references_parameter_outside_head(
    const collect::Session::TemplateInfo& info) {
    auto belongs_to_head = [&](const collect::Session::
                                   ConstraintParameterReference& reference) {
        return std::any_of(
            info.parameters.begin(),
            info.parameters.end(),
            [&](const collect::Session::TemplateParameter& parameter) {
                if (reference.parameter_entity.valid() &&
                    parameter.entity.valid()) {
                    return reference.parameter_entity == parameter.entity;
                }
                if (reference.parameter_type.valid() &&
                    parameter.type_param_type.valid()) {
                    return reference.parameter_type ==
                           parameter.type_param_type;
                }
                return !reference.parameter_entity.valid() &&
                       !reference.parameter_type.valid() &&
                       !parameter.entity.valid() &&
                       reference.parameter_kind == parameter.kind &&
                       reference.parameter_depth == parameter.depth &&
                       reference.parameter_index == parameter.index;
            });
    };
    for (const auto& constraint : info.introduced_constraints) {
        if (!constraint.normal_form.has_value()) {
            continue;
        }
        for (const auto& reference :
             constraint.normal_form->referenced_parameters) {
            if (!belongs_to_head(reference) &&
                reference.owning_template_entity.valid()) {
                return true;
            }
        }
    }
    return false;
}

} // namespace
// todo: obvious size reduction/refactor (albiet most are lambdas)
NodeId Parser::parse_record_specifier(cir::TypeId* type_out) {
    size_t begin = current_raw_index();
    Token keyword = current();
    cir::RecordKind kind = keyword.type == TokenType::UNION
        ? cir::RecordKind::Union
        : (keyword.type == TokenType::CLASS ? cir::RecordKind::Class
                                            : cir::RecordKind::Struct);
    if (!match(keyword.type)) {
        return parse_error_node("expected record specifier", begin, begin + 1);
    }

    std::string tag;

    auto declaration_flags_from_parser = [](const DeclarationParser& decl_parser) {
        collect::DeclFlags flags;
        flags.is_constexpr = decl_parser.is_constexpr;
        flags.is_consteval = decl_parser.is_consteval;
        flags.is_constinit = decl_parser.is_constinit;
        flags.is_inline = decl_parser.is_inline;
        flags.is_thread_local = decl_parser.is_thread_local;
        flags.is_extern = decl_parser.storage_class == StorageClass::Extern;
        flags.is_static = decl_parser.storage_class == StorageClass::Static;
        flags.is_auto_storage = decl_parser.storage_class == StorageClass::Auto;
        flags.is_register = decl_parser.storage_class == StorageClass::Register;
        flags.is_mutable = decl_parser.is_mutable;
        flags.is_friend = decl_parser.is_friend;
        flags.is_block_byref = decl_parser.is_block_byref;
        return flags;
    };

    struct LayoutAttrs {
        AttributeList attrs;
        bool is_packed = false;
        bool is_transparent_union = false;
        size_t alignment = 0;
        std::vector<NodeId> syntax;
    };

    auto merge_attrs = [](LayoutAttrs& dst, LayoutAttrs src) {
        dst.attrs.append(std::move(src.attrs));
        dst.is_packed = dst.is_packed || src.is_packed;
        dst.is_transparent_union =
            dst.is_transparent_union || src.is_transparent_union;
        dst.alignment = std::max(dst.alignment, src.alignment);
        dst.syntax.insert(dst.syntax.end(), src.syntax.begin(), src.syntax.end());
    };

    auto parse_layout_attributes = [&]() {
        LayoutAttrs attrs;
        ParsedAttributes parsed = try_parse_attributes();
        attrs.attrs = std::move(parsed.attrs);
        attrs.syntax = std::move(parsed.syntax);
        for (const ParsedAttribute& attr : attrs.attrs.attrs) {
            if (attr.kind == AttributeKind::Packed) {
                attrs.is_packed = true;
            } else if (attr.kind == AttributeKind::TransparentUnion) {
                attrs.is_transparent_union = true;
            } else if (attr.kind == AttributeKind::Aligned &&
                       !attr.args.empty() &&
                       attr.args.front().kind == AttributeArg::Kind::Integer &&
                       attr.args.front().int_value > 0) {
                attrs.alignment =
                    std::max(attrs.alignment,
                             static_cast<size_t>(attr.args.front().int_value));
            }
        }
        return attrs;
    };

    auto layout_options_from_attrs = [&](const LayoutAttrs& attrs) {
        collect::RecordLayoutOptions options;
        options.attrs = attrs.attrs;
        options.is_packed = attrs.is_packed;
        options.is_transparent_union = attrs.is_transparent_union;
        options.requested_alignment = attrs.alignment;
        options.pack_alignment = source_manager_
            ? source_manager_->getPackAlignment(keyword.loc)
            : 0;
        return options;
    };

    std::vector<NodeId> children;

    LayoutAttrs record_attrs = parse_layout_attributes();
    children.insert(children.end(), record_attrs.syntax.begin(), record_attrs.syntax.end());

    bool parses_explicit_class_specialization =
        explicit_class_template_specialization_parse_ &&
        !explicit_class_template_specialization_parse_->consumed;
    if (parses_explicit_class_specialization) {
        ParsedNestedName nested = parse_nested_name_specifier();
        if (nested.consumed_any) {
            ExplicitClassTemplateSpecializationParse& explicit_specialization =
                *explicit_class_template_specialization_parse_;
            explicit_specialization.has_error =
                explicit_specialization.has_error || nested.has_error;
            explicit_specialization.qualified_context = nested.scope.context;
            if (!nested.has_error &&
                !explicit_specialization.qualified_context.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "explicit class template specialization qualifier does not name a namespace",
                         keyword.loc);
                explicit_specialization.has_error = true;
            }
        }
    }

    struct QualifiedRecordContextExit {
        collect::Session* session = nullptr;
        ~QualifiedRecordContextExit() {
            if (session) {
                session->leave_scope();
            }
        }
    } qualified_record_context;
    bool has_qualified_record_name = false;
    bool qualified_replay_claims_record = false;
    if (lang_opts_.is_cxx_mode()) {
        ParsedNestedName nested = parse_nested_name_specifier();
        if (nested.consumed_any) {
            has_qualified_record_name = true;
            cir::DeclContextId inhabited_context =
                collect_session_.current_decl_context();

            bool replaying_this_member_class =
                replaying_deferred_member_class_begin_ == begin;
            if (!collect_session_.in_template_definition() &&
                !replaying_this_member_class &&
                inhabited_context.valid() &&
                collect_session_.file().decl_context(inhabited_context).kind ==
                    cir::DeclContextKind::Record) {
                diagnose(DiagnosticLevel::Error,
                         "qualified class definition cannot inhabit class scope",
                         keyword.loc);
            }
            if (nested.has_error || !nested.scope.context.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "qualified record definition qualifier does not name a class or namespace",
                         keyword.loc);
            } else {
                const cir::File& file = collect_session_.file();
                cir::DeclContextKind context_kind =
                    file.decl_context(nested.scope.context).kind;
                if (context_kind != cir::DeclContextKind::Record &&
                    context_kind != cir::DeclContextKind::Namespace &&
                    context_kind != cir::DeclContextKind::TranslationUnit) {
                    diagnose(DiagnosticLevel::Error,
                             "qualified record definition qualifier does not name a class or namespace",
                             keyword.loc);
                } else {
                    qualified_replay_claims_record =
                        is_identifier_token(current().type) &&
                        collect_session_
                            .current_instantiation_replay_will_claim_record(
                                current().value);
                    if (!qualified_replay_claims_record) {
                        collect::ScopeFlags flags =
                            context_kind == cir::DeclContextKind::Record
                                ? collect::ScopeFlags::RecordScope
                                : (collect::ScopeFlags::NamespaceScope |
                                   collect::ScopeFlags::FileScope);
                        collect_session_.enter_existing_context(
                            nested.scope.context,
                            flags);
                        qualified_record_context.session = &collect_session_;
                    }
                }
            }
        }
    }

    if (is_identifier_token(current().type)) {
        tag = current().value;
        consume();
    }
    std::string collect_tag = tag;
    cir::EntityId explicit_specialization_record_to_complete{};

    if (!collect_session_.in_template_definition() &&
        has_qualified_record_name && !qualified_replay_claims_record &&
        !tag.empty() && qualified_record_context.session) {
        const cir::File& file = collect_session_.file();
        const cir::Binding* prior = file.lookup_tag_binding(
            collect_session_.current_decl_context(),
            tag,
            /*include_parents=*/false);
        if (!prior || prior->entities.empty() ||
            !file.valid(prior->entities.back()) ||
            file.entity(prior->entities.back()).kind != cir::EntityKind::Record) {
            diagnose(DiagnosticLevel::Error,
                     "qualified class definition has no matching prior declaration",
                     keyword.loc);
        }
    }

    if (parses_explicit_class_specialization) {
        ExplicitClassTemplateSpecializationParse& explicit_specialization =
            *explicit_class_template_specialization_parse_;
        explicit_specialization.consumed = true;
        if (tag.empty()) {
            diagnose(DiagnosticLevel::Error,
                     "explicit class template specialization requires a template name",
                     keyword.loc);
            explicit_specialization.has_error = true;
        } else if (!check(TokenType::LESS_THAN)) {
            diagnose(DiagnosticLevel::Error,
                     "explicit class template specialization requires a template argument list",
                     keyword.loc);
            explicit_specialization.has_error = true;
        } else {
            struct AccessExemptionExit {
                collect::Session& session;
                ~AccessExemptionExit() {
                    session.leave_template_argument_access_exemption();
                }
            } access_exemption{collect_session_};
            collect_session_.enter_template_argument_access_exemption();
            const collect::Session::TemplateInfo* primary =
                collect_session_.template_info(explicit_specialization
                                                   .template_entity);
            if (!primary || !primary->is_class_template ||
                primary->name != tag) {
                diagnose(DiagnosticLevel::Error,
                         "no matching class template for explicit specialization",
                         keyword.loc);
                explicit_specialization.has_error = true;
                (void)parse_dependent_expression_template_argument_list(
                    keyword.loc);
            } else {
                std::vector<collect::Session::TemplateArgument> arguments;
                if (!parse_and_canonicalize_template_argument_list(
                        *primary,
                        arguments,
                        keyword.loc)) {
                    explicit_specialization.has_error = true;
                } else {
                    if (!check_non_function_template_associated_constraints(
                            *primary,
                            arguments,
                            keyword.loc,
                            collect_session_.lookup_generation())) {
                        explicit_specialization.has_error = true;
                    }
                    explicit_specialization.matched = true;
                    explicit_specialization.source_name = tag;
                    explicit_specialization.template_entity = primary->entity;
                    explicit_specialization.arguments = std::move(arguments);
                    std::string parsed_display_name =
                        collect_session_.template_display_name(
                            *primary,
                            explicit_specialization.arguments);

                    if (!explicit_specialization.is_partial_replay ||
                        explicit_specialization.display_name.empty()) {
                        explicit_specialization.display_name =
                            std::move(parsed_display_name);
                    }
                    collect_tag = explicit_specialization.display_name;
                    if (!explicit_specialization.is_partial_replay) {
                        std::string memo_key =
                            collect_session_.template_memo_key(
                                primary->entity,
                                explicit_specialization.arguments);
                        cir::EntityId cached =
                            collect_session_.cached_instantiation(memo_key);
                        const cir::RecordFacts* cached_facts =
                            cached.valid() &&
                                    collect_session_.file().valid(cached)
                                ? collect_session_.file().record_facts(cached)
                                : nullptr;
                        if (!cached.valid()) {

                            cir::EntityId shell = collect_session_
                                .create_incomplete_record_specialization(
                                    *primary,
                                    explicit_specialization.arguments,
                                    keyword.loc);
                            if (shell.valid()) {
                                collect_session_.remember_instantiation(
                                    memo_key, shell);
                                explicit_specialization_record_to_complete =
                                    shell;
                            }
                        } else if (cached_facts &&
                                   cached_facts->is_incomplete) {

                            explicit_specialization_record_to_complete =
                                cached;
                        }
                    }
                }
            }
        }
    }

    struct ExplicitClassSpecializationContextExit {
        collect::Session* session = nullptr;

        ~ExplicitClassSpecializationContextExit() {
            if (session) {
                session->leave_scope();
            }
        }
    } explicit_class_specialization_context;
    if (parses_explicit_class_specialization &&
        explicit_class_template_specialization_parse_->matched &&
        explicit_class_template_specialization_parse_->qualified_context
            .valid()) {
        cir::DeclContextId context =
            explicit_class_template_specialization_parse_->qualified_context;
        const cir::File& file = collect_session_.file();
        cir::DeclContextKind context_kind = file.decl_context(context).kind;
        if (context_kind != cir::DeclContextKind::Record &&
            context_kind != cir::DeclContextKind::Namespace &&
            context_kind != cir::DeclContextKind::TranslationUnit) {
            diagnose(DiagnosticLevel::Error,
                     "qualified class template specialization context is not a class or namespace",
                     keyword.loc);
            explicit_class_template_specialization_parse_->has_error = true;
        } else {
            collect_session_.enter_existing_context(
                context,
                context_kind == cir::DeclContextKind::Record
                    ? collect::ScopeFlags::RecordScope
                    : (collect::ScopeFlags::NamespaceScope |
                       collect::ScopeFlags::FileScope));
            explicit_class_specialization_context.session =
                &collect_session_;
        }
    }

    if (check(TokenType::ATTRIBUTE_KW)) {
        bool attrs_introduce_body = false;
        {
            RevertingTentativeParsingAction lookahead(*this);
            (void)try_parse_attributes();
            attrs_introduce_body =
                check(TokenType::LEFT_BRACE) ||
                (lang_opts_.is_cxx_mode() &&
                 (check(TokenType::COLON) ||
                  (is_identifier_token(current().type) &&
                   current().value == "final")));
        }
        if (attrs_introduce_body) {
            LayoutAttrs post_tag_attrs = parse_layout_attributes();
            children.insert(children.end(), post_tag_attrs.syntax.begin(),
                            post_tag_attrs.syntax.end());
            merge_attrs(record_attrs, std::move(post_tag_attrs));
        }
    }

    if (lang_opts_.is_cxx_mode()) {

        auto record_definition_ahead = [&]() {

            size_t offset = 0;
            while (is_identifier_token(peek(offset).type) &&
                   peek(offset).value == "final") {
                ++offset;
            }
            if (peek(offset).type == TokenType::LEFT_BRACE) {
                return true;
            }
            if (peek(offset).type != TokenType::COLON) {
                return false;
            }
            ++offset;

            int parens = 0;
            int brackets = 0;
            int angles = 0;
            for (;; ++offset) {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof) {
                    return false;
                }
                if (parens == 0 && brackets == 0 && angles == 0) {
                    if (type == TokenType::LEFT_BRACE) {
                        return true;
                    }
                    if (type == TokenType::SEMICOLON) {
                        return false;
                    }
                }
                switch (type) {
                    case TokenType::LEFT_PAREN:
                        ++parens;
                        break;
                    case TokenType::RIGHT_PAREN:
                        parens = std::max(0, parens - 1);
                        break;
                    case TokenType::LEFT_BRACKET:
                        ++brackets;
                        break;
                    case TokenType::RIGHT_BRACKET:
                        brackets = std::max(0, brackets - 1);
                        break;
                    case TokenType::LESS_THAN:
                        ++angles;
                        break;
                    case TokenType::GREATER_THAN:
                        angles = std::max(0, angles - 1);
                        break;
                    case TokenType::RIGHT_SHIFT:
                        angles = std::max(0, angles - 2);
                        break;
                    default:
                        break;
                }
            }
        };
        cir::EntityId member_owner = collect_session_.enclosing_record_for_context(
            collect_session_.current_decl_context());
        bool declared_in_member_scope = false;
        for (cir::DeclContextId declaration_context =
                 collect_session_.current_decl_context();
             declaration_context.valid() &&
             collect_session_.file().valid(declaration_context);
             declaration_context = collect_session_.file()
                                       .decl_context(declaration_context)
                                       .parent) {
            const cir::DeclContext& context =
                collect_session_.file().decl_context(declaration_context);
            if (context.kind == cir::DeclContextKind::Record) {
                declared_in_member_scope = context.owner == member_owner;
                break;
            }
            if (context.kind == cir::DeclContextKind::Function ||
                context.kind == cir::DeclContextKind::Block ||
                context.kind == cir::DeclContextKind::Namespace ||
                context.kind == cir::DeclContextKind::TranslationUnit) {
                break;
            }
        }
        bool has_enclosing_specialization = false;
        cir::DeclContextId owner_context =
            collect_session_.current_decl_context();
        while (owner_context.valid() &&
               collect_session_.file().valid(owner_context)) {
            const cir::DeclContext& context =
                collect_session_.file().decl_context(owner_context);
            if (context.kind == cir::DeclContextKind::Record &&
                context.owner.valid() &&
                collect_session_.file().template_specialization(context.owner)) {
                has_enclosing_specialization = true;
                break;
            }
            owner_context = context.parent;
        }
        bool defer_member_class =
            !tag.empty() && member_owner.valid() &&
            declared_in_member_scope &&
            has_enclosing_specialization &&
            collect_session_.is_instantiating() &&
            !collect_session_.validating_template_info() &&
            !collect_session_.current_instantiation_replay_will_claim_record(
                tag) &&
            replaying_deferred_member_class_begin_ != begin &&
            record_definition_ahead();
        if (defer_member_class) {
            collect::RecordDeclResult nested =
                collect_session_.begin_record_definition(kind,
                                                         collect_tag,
                                                         keyword.loc);
            size_t definition_end = skip_balanced_until_semicolon_or_brace();
            if (nested.entity.valid()) {
                uint64_t key = static_cast<uint64_t>(nested.entity.index);
                deferred_member_class_definitions_[key] =
                    DeferredMemberClassDefinition{nested.entity,
                                                  member_owner,
                                                  begin,
                                                  definition_end,
                                                  keyword.loc};
                collect_session_.track_speculative_rollback([this, key] {
                    deferred_member_class_definitions_.erase(key);
                });
            }
            if (type_out) {
                *type_out = nested.type;
            }
            std::string text = std::string(cir::record_kind_name(kind));
            text += ' ';
            text += tag;
            return make_node(NodeKind::RecordDecl,
                             begin,
                             definition_end,
                             children,
                             text_payload(std::move(text)),
                             nested.has_error ? NodeFlagHasError
                                              : NodeFlagNone);
        }

        bool header_has_error = false;
        bool is_final = false;
        size_t final_count = 0;
        while (is_identifier_token(peek(final_count).type) &&
               peek(final_count).value == "final") {
            ++final_count;
        }

        if (final_count > 0 &&
            (peek(final_count).type == TokenType::LEFT_BRACE ||
             peek(final_count).type == TokenType::COLON)) {
            is_final = true;
            for (size_t i = 0; i < final_count; ++i) {
                SrcLoc final_loc = current().loc;
                consume();
                if (i > 0) {
                    diagnose(DiagnosticLevel::Error,
                             "duplicate 'final' class property specifier",
                             final_loc);
                    header_has_error = true;
                }
            }
        }
        if (!tag.empty() && !explicit_member_record_specialization_ &&
            (check(TokenType::COLON) || check(TokenType::LEFT_BRACE))) {

            collect::RecordDeclResult class_head =
                collect_session_.declare_record_tag_in_current_scope(
                    kind,
                    collect_tag,
                    keyword.loc,
                    explicit_specialization_record_to_complete);
            header_has_error = header_has_error || class_head.has_error;
        }
        std::vector<collect::RecordBaseInput> bases;
        bool record_has_dependent_bases = false;
        collect::Session::AccessCaptureToken base_access_capture{};
        auto append_base = [&](collect::RecordBaseInput base) {
            if (!base.type.valid()) {
                return;
            }
            base.is_dependent = base.is_dependent ||
                collect_session_.in_template_definition() &&
                    collect_session_.is_dependent_type(base.type);
            record_has_dependent_bases =
                record_has_dependent_bases || base.is_dependent;
            if (!base.is_dependent) {

                (void)collect_session_.require_complete_class_type(
                    base.type,
                    base.loc,
                    cir::InstantiationDemandKind::BaseMemberList);
            }
            bases.push_back(std::move(base));
        };
        if (match(TokenType::COLON)) {
            base_access_capture = collect_session_.begin_access_capture();
            size_t base_begin = last_consumed_raw_index();
            auto parse_base_specifier =
                [&]() -> std::optional<collect::RecordBaseInput> {
                collect::RecordBaseInput base;
                base.loc = current_loc();
                bool saw_virtual = match(TokenType::VIRTUAL_KW);
                if (is_cxx_access_specifier(current().type)) {
                    base.declared_access = access_from_token(current().type);
                    consume();
                }
                if (!saw_virtual) {
                    saw_virtual = match(TokenType::VIRTUAL_KW);
                }
                base.is_virtual = saw_virtual;
                if (auto qualified = peek_cxx_qualified_type()) {
                    SrcLoc qualified_loc = current_loc();
                    for (size_t i = 0; i < qualified->tokens_to_consume; ++i) {
                        consume();
                    }
                    if (qualified->template_info) {
                        cir::EntityId instantiated = instantiate_template(
                            *qualified->template_info, qualified_loc);
                        if (instantiated.valid()) {
                            base.type = collect_session_.file()
                                .entity(instantiated).type;
                        } else {
                            header_has_error = true;
                        }
                    } else {
                        cir::TypeId checked = collect_session_
                            .lookup_qualified_type_name_checked(
                                qualified->terminal_context,
                                qualified->terminal_name,
                                qualified->terminal_loc);
                        base.type = checked.valid() ? checked
                                                    : qualified->type.type;
                    }
                } else if (check(TokenType::SCOPE_RESOLUTION) ||
                           (is_identifier_token(current().type) &&
                            (peek(1).type == TokenType::SCOPE_RESOLUTION ||
                             (peek(1).type == TokenType::LESS_THAN &&
                              template_id_precedes_scope(0))))) {
                    std::optional<cir::TypeRef> dependent_base =
                        parse_cxx_qualified_type_name(
                            TypeParseContext::type_only(
                                TypeParseContext::Origin::ClassOrDecltype));
                    if (dependent_base.has_value()) {
                        base.type = dependent_base->type;
                    } else {
                        header_has_error = true;
                    }
                } else if (const collect::Session::TemplateInfo* base_template =
                               lang_opts_.is_cxx_mode() &&
                                       is_identifier_token(current().type) &&
                                       peek(1).type == TokenType::LESS_THAN
                                   ? collect_session_.template_info_for_name(
                                         current().value)
                                   : nullptr;
                           base_template &&
                               (base_template->is_class_template ||
                                base_template->is_alias_template)) {

                    SrcLoc base_loc = current_loc();
                    consume();
                    cir::EntityId instantiated =
                        instantiate_template(*base_template, base_loc);
                    if (instantiated.valid()) {
                        base.type = collect_session_.file()
                            .entity(instantiated).type;
                    } else {
                        header_has_error = true;
                    }
                } else if (check(TokenType::DECLTYPE_KW)) {
                    DeclarationParser type_parser(
                        *this,
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::ClassOrDecltype));
                    cir::TypeRef parsed =
                        type_parser.parse_declaration(false, true);
                    base.type = parsed.type;
                    if (!base.type.valid()) {
                        header_has_error = true;
                    }
                } else if (is_identifier_token(current().type)) {
                    collect_session_.capture_type_parameter_pack_name(
                        current().value);
                    base.type =
                        collect_session_.lookup_type_name(current().value);
                    if (!base.type.valid()) {
                        diagnose(DiagnosticLevel::Error,
                                 "base specifier does not name a class",
                                 current_loc());
                        header_has_error = true;
                    }
                    consume();
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "expected a class name in the base clause",
                             current_loc());
                    header_has_error = true;
                    return std::nullopt;
                }
                return base;
            };
            auto base_specifier_may_contain_ellipsis = [&]() {
                int paren_depth = 0;
                int bracket_depth = 0;
                int angle_depth = 0;
                for (size_t offset = 0; true; ++offset) {
                    TokenType type = peek(offset).type;
                    if (type == TokenType::Eof) {
                        return false;
                    }
                    if (paren_depth == 0 && bracket_depth == 0 &&
                        angle_depth == 0 &&
                        (type == TokenType::COMMA ||
                         type == TokenType::LEFT_BRACE)) {
                        return false;
                    }
                    if (paren_depth == 0 && bracket_depth == 0 &&
                        angle_depth == 0 &&
                        type == TokenType::ELLIPSIS) {
                        return true;
                    }
                    switch (type) {
                        case TokenType::LEFT_PAREN:
                            ++paren_depth;
                            break;
                        case TokenType::RIGHT_PAREN:
                            if (paren_depth > 0) {
                                --paren_depth;
                            }
                            break;
                        case TokenType::LEFT_BRACKET:
                            ++bracket_depth;
                            break;
                        case TokenType::RIGHT_BRACKET:
                            if (bracket_depth > 0) {
                                --bracket_depth;
                            }
                            break;
                        case TokenType::LESS_THAN:
                            ++angle_depth;
                            break;
                        case TokenType::GREATER_THAN:
                            if (angle_depth > 0) {
                                --angle_depth;
                            }
                            break;
                        case TokenType::RIGHT_SHIFT:
                            if (angle_depth > 1) {
                                angle_depth -= 2;
                            } else {
                                angle_depth = 0;
                            }
                            break;
                        default:
                            break;
                    }
                }
            };
            do {
                bool handled_pack_expansion = false;
                if (base_specifier_may_contain_ellipsis()) {

                    collect::RecordBaseInput placeholder;
                    bool placeholder_parsed = false;
                    std::optional<PackExpansionPattern> pattern =
                        try_parse_pack_expansion_pattern([&] {
                            std::optional<collect::RecordBaseInput> parsed =
                                parse_base_specifier();
                            if (parsed.has_value()) {
                                placeholder = std::move(*parsed);
                                placeholder_parsed = true;
                            }
                        });
                    if (pattern.has_value()) {
                        handled_pack_expansion = true;
                        if (!pattern->has_pack_names()) {
                            diagnose(DiagnosticLevel::Error,
                                     "pack expansion pattern does not contain a template parameter pack",
                                     pattern->ellipsis_loc);
                            header_has_error = true;
                            cursor_ = pattern->after_ellipsis_cursor;
                            last_consumed_raw_end_ =
                                pattern->after_ellipsis_last_consumed_raw_end;
                        } else {
                            bool arity_dependent = false;
                            std::optional<size_t> element_count =
                                resolve_pack_expansion_element_count(
                                    *pattern, &arity_dependent);
                            if (arity_dependent) {
                                if (!placeholder_parsed ||
                                    !placeholder.type.valid() ||
                                    !collect_session_.file().valid(
                                        placeholder.type)) {
                                    placeholder.loc =
                                        pattern->ellipsis_loc.isInvalid()
                                            ? current_loc()
                                            : pattern->ellipsis_loc;
                                    placeholder.type =
                                        collect_session_.file()
                                            .dependent_type(
                                                "base pack expansion");
                                }
                                placeholder.is_dependent = true;
                                append_base(std::move(placeholder));
                                cursor_ = pattern->after_ellipsis_cursor;
                                last_consumed_raw_end_ =
                                    pattern
                                        ->after_ellipsis_last_consumed_raw_end;
                            } else {
                                replay_pack_expansion_elements(
                                    *pattern,
                                    element_count.value_or(0),
                                    [&](size_t) {
                                        std::optional<
                                            collect::RecordBaseInput>
                                            replayed =
                                                parse_base_specifier();
                                        if (replayed.has_value()) {
                                            append_base(
                                                std::move(*replayed));
                                        }
                                    });
                            }
                        }
                    }
                }
                if (!handled_pack_expansion) {
                    auto capture_scope = collect_session_
                        .begin_parameter_pack_pattern_capture();
                    std::optional<collect::RecordBaseInput> base =
                        parse_base_specifier();
                    std::vector<collect::Session::ParameterPackIdentity>
                        unexpanded_packs = collect_session_
                            .finish_parameter_pack_pattern_capture(
                                capture_scope);
                    if (base.has_value() && !unexpanded_packs.empty()) {
                        std::string pack_name =
                            unexpanded_packs.front().name.empty()
                                ? ""
                                : " '" + unexpanded_packs.front().name + "'";
                        diagnose(DiagnosticLevel::Error,
                                 "unexpanded template parameter pack" +
                                     pack_name +
                                     " is not supported yet",
                                 base->loc);
                        header_has_error = true;
                        base->type = collect_session_.file().unknown_type();
                    }
                    if (base.has_value()) {
                        append_base(std::move(*base));
                    }
                }
            } while (match(TokenType::COMMA));
            children.push_back(make_node(NodeKind::AmbiguousSyntax,
                                         base_begin,
                                         last_consumed_raw_end(),
                                         {},
                                         text_payload("base-clause")));
            collect_session_.suspend_access_capture(base_access_capture);
        }

        collect::RecordDeclResult record;
        if (!check(TokenType::LEFT_BRACE)) {

            record = check(TokenType::SEMICOLON)
                ? collect_session_.declare_record_tag_in_current_scope(
                      kind,
                      collect_tag,
                      keyword.loc,
                      explicit_specialization_record_to_complete)
                : collect_session_.declare_record_tag(kind,
                                                      collect_tag,
                                                      keyword.loc);
            if (type_out) {
                *type_out = record.type;
            }
            collect_session_.discard_access_capture(base_access_capture);

            std::string text = std::string(cir::record_kind_name(kind));
            if (!tag.empty()) {
                text += ' ';
                text += tag;
            }
            return make_node(NodeKind::RecordDecl,
                             begin,
                             last_consumed_raw_end(),
                             children,
                             text_payload(std::move(text)),
                             (record.has_error || header_has_error) ? NodeFlagHasError : NodeFlagNone);
        }

        record = explicit_member_record_specialization_
            ? collect_session_.begin_explicit_member_record_specialization(
                  kind,
                  collect_tag,
                  keyword.loc)
            : collect_session_.begin_record_definition(kind,
                                                       collect_tag,
                                                       keyword.loc,
                                                       explicit_specialization_record_to_complete);
        if (record.fold_duplicate_definition) {

            collect_session_.discard_access_capture(base_access_capture);
            if (match(TokenType::LEFT_BRACE)) {
                int depth = 1;
                while (depth > 0 && !at_end()) {
                    if (check(TokenType::LEFT_BRACE)) {
                        ++depth;
                    } else if (check(TokenType::RIGHT_BRACE)) {
                        --depth;
                    }
                    consume();
                }
            }
            if (type_out) {
                *type_out = record.type;
            }
            std::string text = std::string(cir::record_kind_name(kind));
            if (!tag.empty()) {
                text += ' ';
                text += tag;
            }
            return make_node(NodeKind::RecordDecl,
                             begin,
                             last_consumed_raw_end(),
                             children,
                             text_payload(std::move(text)),
                             header_has_error ? NodeFlagHasError
                                              : NodeFlagNone);
        }
        if (parses_explicit_class_specialization &&
            explicit_class_template_specialization_parse_->matched &&
            !explicit_class_template_specialization_parse_
                 ->is_partial_replay &&
            record.entity.valid()) {
            const collect::Session::TemplateInfo* primary =
                collect_session_.template_info(
                    explicit_class_template_specialization_parse_
                        ->template_entity);
            if (primary && primary->is_class_template) {
                collect_session_.remember_template_specialization(
                    record.entity,
                    *primary,
                    explicit_class_template_specialization_parse_->arguments);

                std::string memo_key = collect_session_.template_memo_key(
                    primary->entity,
                    explicit_class_template_specialization_parse_->arguments);
                cir::EntityId cached =
                    collect_session_.cached_instantiation(memo_key);
                if (!cached.valid()) {
                    collect_session_.remember_instantiation(memo_key,
                                                            record.entity);
                }
            }
        }
        collect_session_.note_current_instantiation_dependent_bases(
            record.entity,
            record_has_dependent_bases);
        collect_session_.enter_record_scope(record.entity, keyword.loc);
        struct LocalClassSeparateConstructScope {
            Parser& parser;
            bool previous = false;

            LocalClassSeparateConstructScope(Parser& parser,
                                             bool instantiate)
                : parser(parser),
                  previous(parser.instantiate_member_parameter_defaults_) {
                parser.instantiate_member_parameter_defaults_ =
                    previous || instantiate;
            }

            ~LocalClassSeparateConstructScope() {
                parser.instantiate_member_parameter_defaults_ = previous;
            }
        } local_class_separate_construct_scope(
            *this,
            current_record_is_local(collect_session_) &&
                collect_session_.is_instantiating());
        if (parses_explicit_class_specialization &&
            explicit_class_template_specialization_parse_->matched) {
            collect_session_.bind_record_injected_class_name(
                explicit_class_template_specialization_parse_->source_name,
                record.entity,
                keyword.loc);
        }
        collect_session_.set_current_record_pending_bases(bases);
        consume();

        std::vector<collect::RecordFieldInput> fields;
        std::vector<collect::RecordStaticDataMemberInput> static_data_members;
        std::vector<collect::RecordMethodInput> methods;
        bool has_friend_equality_declaration = false;
        cir::RecordMemberAccess current_access = default_access_for(kind);

        std::vector<PendingMemberBody> pending_bodies;
        std::vector<PendingMemberTemplate> pending_member_templates;
        struct PendingMethodConstraints {
            size_t method_index = 0;
            std::vector<collect::Session::TemplateInfo::IntroducedConstraint>
                constraints;
        };
        std::vector<PendingMethodConstraints> pending_method_constraints;
        auto retain_method_constraint =
            [&](size_t method_index,
                collect::RecordMethodInput& method,
                size_t constraint_begin,
                size_t constraint_end,
                std::optional<collect::Session::NormalizedConstraint> normal_form,
                std::optional<bool> value) {
                if (!normal_form.has_value()) {
                    method.constraint_satisfaction =
                        cir::ConstraintSatisfactionKind::Invalid;
                    return;
                }
                method.associated_constraint_fingerprint =
                    collect_session_.normalized_constraint_fingerprint(
                        *normal_form);
                method.constraint_satisfaction = value.has_value()
                    ? (*value
                           ? cir::ConstraintSatisfactionKind::Satisfied
                           : cir::ConstraintSatisfactionKind::Unsatisfied)
                    : cir::ConstraintSatisfactionKind::Dependent;
                collect::Session::TemplateInfo::IntroducedConstraint
                    constraint{
                        collect::Session::TemplateInfo::
                            IntroducedConstraintKind::FunctionTrailingRequires,
                        constraint_begin,
                        constraint_end};
                constraint.normal_form = std::move(normal_form);
                pending_method_constraints.push_back(
                    PendingMethodConstraints{method_index,
                                             {std::move(constraint)}});
            };
        auto parse_member_function_tail =
            [&](collect::RecordMethodInput& method,
                std::vector<NodeId>& member_children,
                bool is_constructor,
                std::vector<ParsedParam> body_params,
                bool declared_through_function_type) {
            bool parsed_body = false;
            while (is_identifier_token(current().type) &&
                   (current().value == "override" ||
                    current().value == "final")) {
                Token specifier = current();
                consume();
                bool& fact = specifier.value == "override"
                    ? method.is_override
                    : method.is_final;
                if (fact) {
                    diagnose(DiagnosticLevel::Error,
                             "duplicate '" + std::string(specifier.value) +
                                 "' virt-specifier",
                             specifier.loc);
                }
                fact = true;
            }
            bool forbidden_typedef_definition =
                declared_through_function_type &&
                (check(TokenType::LEFT_BRACE) ||
                 check(TokenType::TRY_KW) ||
                 (check(TokenType::ASSIGN) &&
                  (peek(1).type == TokenType::DEFAULT ||
                   peek(1).type == TokenType::DELETE)));
            if (forbidden_typedef_definition) {
                diagnose(DiagnosticLevel::Error,
                         "a member function declared through a function type "
                         "alias cannot be defined",
                         current_loc());
            }
            size_t init_begin = 0;
            size_t init_end = 0;
            if (is_constructor && match(TokenType::COLON)) {

                init_begin = current_raw_index();
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
                    }
                    if (type == TokenType::RIGHT_PAREN ||
                        type == TokenType::RIGHT_BRACE) {
                        --depth;
                    }
                    previous = type;
                    consume();
                }
                init_end = current_raw_index();
            }

            if (match(TokenType::ASSIGN)) {
                SrcLoc suffix_loc = last_consumed_loc();
                if (match(TokenType::DEFAULT)) {
                    method.is_defaulted = true;
                } else if (match(TokenType::DELETE)) {
                    method.is_deleted = true;
                } else if (check(TokenType::INTEGER_CONST) && current().value == "0") {
                    consume();
                    method.is_pure = true;
                } else {
                    ParsedExpr suffix = parse_expression(PrecLevel::ASSIGNMENT);
                    member_children.push_back(suffix.syntax);
                    diagnose(DiagnosticLevel::Error,
                             "C++ function declaration suffixes are not supported",
                             suffix_loc);
                }
            }

            bool forbidden_pure_definition =
                method.is_pure &&
                (check(TokenType::LEFT_BRACE) || check(TokenType::TRY_KW));
            if (forbidden_pure_definition) {
                diagnose(DiagnosticLevel::Error,
                         "a pure-specifier cannot be combined with a function definition",
                         current_loc());
            }

            if (check(TokenType::TRY_KW)) {
                size_t body_begin = current_raw_index();
                size_t body_end = skip_function_try_block_tokens();
                bool supported_constructor_try = is_constructor &&
                    !forbidden_typedef_definition &&
                    !forbidden_pure_definition;
                member_children.push_back(make_node(NodeKind::DeferredBody,
                                                    body_begin,
                                                    body_end,
                                                    {},
                                                    text_payload("member body"),
                                                    supported_constructor_try
                                                        ? NodeFlagNone
                                                        : NodeFlagHasError));
                if (supported_constructor_try) {
                    PendingMemberBody pending;
                    pending.method_index = methods.size();
                    pending.body_begin = body_begin;
                    pending.body_end = body_end;
                    pending.is_constructor_function_try = true;
                    pending.params = std::move(body_params);
                    pending_bodies.push_back(std::move(pending));
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "function try blocks are supported only for "
                             "constructors",
                             loc_for_index(body_begin));
                }
                parsed_body = true;
            } else if (check(TokenType::LEFT_BRACE)) {

                size_t body_begin = current_raw_index();
                size_t body_end = skip_balanced_until_semicolon_or_brace();
                member_children.push_back(make_node(NodeKind::DeferredBody,
                                                    body_begin,
                                                    body_end,
                                                    {},
                                                    text_payload("member body"),
                                                    forbidden_pure_definition
                                                        ? NodeFlagHasError
                                                        : NodeFlagNone));
                if (!forbidden_typedef_definition &&
                    !forbidden_pure_definition) {
                    PendingMemberBody pending;
                    pending.method_index = methods.size();
                    pending.body_begin = body_begin;
                    pending.body_end = body_end;
                    pending.init_begin = init_begin;
                    pending.init_end = init_end;
                    pending.params = std::move(body_params);
                    pending_bodies.push_back(std::move(pending));
                }
                parsed_body = true;
            } else if (init_begin != init_end) {
                diagnose(DiagnosticLevel::Error,
                         "constructor member initializers require a body",
                         loc_for_index(init_begin));
            }
            return parsed_body;
        };

        struct ParsedRecordExceptionSpec {
            cir::FunctionExceptionSpec spec;
            bool has_explicit = false;
            bool deferred = false;
            size_t operand_begin = 0;
            size_t operand_end = 0;
            SrcLoc operand_loc{};
            cir::DeclContextId declaration_context{};
            uint64_t lookup_generation = 0;
        };
        auto parse_special_member_exception_spec =
            [&](std::vector<NodeId>& member_children) {
                ParsedRecordExceptionSpec result;
                if (check(TokenType::THROW_KW)) {
                    result.has_explicit = true;
                    SrcLoc throw_loc = current_loc();
                    consume();
                    if (!match(TokenType::LEFT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected '(' after 'throw'",
                                 throw_loc);
                    } else if (match(TokenType::RIGHT_PAREN)) {

                        result.spec =
                            cir::FunctionExceptionSpecKind::NonThrowing;
                    } else {
                        diagnose(DiagnosticLevel::Error,
                                 "dynamic exception specifications are not supported; use 'noexcept' instead",
                                 throw_loc);
                        int depth = 1;
                        while (!at_end() && depth > 0) {
                            TokenType type = current().type;
                            consume();
                            if (type == TokenType::LEFT_PAREN) ++depth;
                            if (type == TokenType::RIGHT_PAREN) --depth;
                        }
                    }
                    return result;
                }
                if (!match(TokenType::NOEXCEPT_KW)) {
                    return result;
                }
                result.has_explicit = true;
                result.spec = cir::FunctionExceptionSpecKind::NonThrowing;
                if (match(TokenType::LEFT_PAREN)) {
                    result.operand_begin = current_raw_index();
                    result.operand_loc = current_loc();
                    result.declaration_context =
                        collect_session_.current_decl_context();
                    result.lookup_generation =
                        collect_session_.lookup_generation();
                    result.deferred = should_defer_complete_class_region();
                    size_t diagnostic_watermark = diagnostics_.size();
                    if (result.deferred) {
                        collect_session_.begin_speculative_parse();
                    }
                    ParsedExpr operand =
                        parse_conditional_expression();
                    result.operand_end = current_raw_index();
                    if (result.deferred) {
                        collect_session_.rollback_speculative_parse();
                        diagnostics_.resize(diagnostic_watermark);
                    }
                    member_children.push_back(operand.syntax);
                    if (!match(TokenType::RIGHT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ')' after noexcept specifier operand",
                                 current_loc());
                    }
                    if (result.deferred) {
                        result.spec = cir::FunctionExceptionSpecKind::PotentiallyThrowing;
                    } else {
                        result.spec = collect_session_.evaluate_noexcept_spec(
                            operand.sem, last_consumed_loc());
                    }
                }
                return result;
            };

        auto skip_balanced_prefix_parentheses = [&](size_t offset) {
            if (peek(offset).type != TokenType::LEFT_PAREN) {
                return offset;
            }
            int depth = 0;
            do {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof) {
                    return offset;
                }
                if (type == TokenType::LEFT_PAREN) {
                    ++depth;
                } else if (type == TokenType::RIGHT_PAREN) {
                    --depth;
                }
                ++offset;
            } while (depth > 0);
            return offset;
        };

        auto skip_member_prefix_attributes =
            [&](size_t offset) {
                while (true) {
                    if (peek(offset).type == TokenType::ATTRIBUTE_KW) {
                        ++offset;
                        offset = skip_balanced_prefix_parentheses(offset);
                        continue;
                    }
                    if (peek(offset).type == TokenType::ALIGNAS) {
                        ++offset;
                        offset = skip_balanced_prefix_parentheses(offset);
                        continue;
                    }
                    if (peek(offset).type != TokenType::LEFT_BRACKET ||
                        peek(offset + 1).type != TokenType::LEFT_BRACKET) {
                        break;
                    }
                    offset += 2;
                    int paren_depth = 0;
                    int brace_depth = 0;
                    int bracket_depth = 0;
                    while (true) {
                        TokenType type = peek(offset).type;
                        if (type == TokenType::Eof) {
                            return offset;
                        }
                        if (type == TokenType::RIGHT_BRACKET &&
                            peek(offset + 1).type ==
                                TokenType::RIGHT_BRACKET &&
                            paren_depth == 0 && brace_depth == 0 &&
                            bracket_depth == 0) {
                            offset += 2;
                            break;
                        }
                        if (type == TokenType::LEFT_PAREN) {
                            ++paren_depth;
                        } else if (type == TokenType::RIGHT_PAREN &&
                                   paren_depth > 0) {
                            --paren_depth;
                        } else if (type == TokenType::LEFT_BRACE) {
                            ++brace_depth;
                        } else if (type == TokenType::RIGHT_BRACE &&
                                   brace_depth > 0) {
                            --brace_depth;
                        } else if (type == TokenType::LEFT_BRACKET) {
                            ++bracket_depth;
                        } else if (type == TokenType::RIGHT_BRACKET &&
                                   bracket_depth > 0) {
                            --bracket_depth;
                        }
                        ++offset;
                    }
                }
                return offset;
            };

        auto skip_cxx_special_member_prefix = [&](size_t offset) {
            while (true) {
                size_t after_attributes =
                    skip_member_prefix_attributes(offset);
                if (after_attributes != offset) {
                    offset = after_attributes;
                    continue;
                }
                TokenType type = peek(offset).type;
                if (type == TokenType::INLINE ||
                    type == TokenType::CONSTEXPR_KW ||
                    type == TokenType::CONSTEVAL_KW ||
                    type == TokenType::CONSTINIT_KW ||
                    type == TokenType::STATIC) {
                    ++offset;
                    continue;
                }
                if (type != TokenType::EXPLICIT_KW) {
                    break;
                }
                ++offset;
                offset = skip_balanced_prefix_parentheses(offset);
            }
            return offset;
        };

        struct ParsedSpecialMemberPrefix {
            collect::DeclFlags flags;
            LayoutAttrs attrs;
            ParsedExplicitSpecifier explicit_specifier;
            bool invalid_static = false;
            bool has_error = false;

            bool is_explicit() const {
                return explicit_specifier.effective_value();
            }
        };

        auto parse_special_member_prefix = [&](LayoutAttrs initial_attrs) {
            ParsedSpecialMemberPrefix result;
            result.attrs = std::move(initial_attrs);
            while (true) {
                size_t attribute_begin = current_raw_index();
                LayoutAttrs next_attrs = parse_layout_attributes();
                if (current_raw_index() != attribute_begin) {
                    merge_attrs(result.attrs, std::move(next_attrs));
                    continue;
                }
                if (match(TokenType::INLINE)) {
                    result.flags.is_inline = true;
                } else if (match(TokenType::CONSTEXPR_KW)) {
                    result.flags.is_constexpr = true;
                } else if (match(TokenType::CONSTEVAL_KW)) {
                    result.flags.is_consteval = true;
                } else if (match(TokenType::CONSTINIT_KW)) {
                    result.flags.is_constinit = true;
                } else if (match(TokenType::STATIC)) {
                    result.invalid_static = true;
                } else if (check(TokenType::EXPLICIT_KW)) {
                    if (result.explicit_specifier.present()) {
                        diagnose(DiagnosticLevel::Error,
                                 "duplicate explicit specifier",
                                 current_loc());
                        result.has_error = true;
                    }
                    result.explicit_specifier = parse_explicit_specifier();
                    result.has_error = result.has_error ||
                        result.explicit_specifier.has_error;
                } else {
                    break;
                }
            }
            return result;
        };

        auto parse_special_member = [&](size_t member_begin,
                                        bool leading_virtual,
                                        const LayoutAttrs& leading_attrs) -> bool {
            size_t lookahead = skip_cxx_special_member_prefix(0);

            size_t structor_name_offset = lookahead;
            size_t structor_parentheses = 0;
            while (peek(structor_name_offset).type ==
                   TokenType::LEFT_PAREN) {
                ++structor_parentheses;
                ++structor_name_offset;
            }
            auto skip_standard_attribute_lists = [&](size_t offset) {
                while (peek(offset).type == TokenType::LEFT_BRACKET &&
                       peek(offset + 1).type == TokenType::LEFT_BRACKET) {
                    offset += 2;
                    int paren_depth = 0;
                    int brace_depth = 0;
                    int bracket_depth = 0;
                    bool closed = false;
                    for (size_t guard = 0; guard < 4096; ++guard) {
                        TokenType type = peek(offset).type;
                        if (type == TokenType::Eof) {
                            break;
                        }
                        if (type == TokenType::RIGHT_BRACKET &&
                            peek(offset + 1).type ==
                                TokenType::RIGHT_BRACKET &&
                            paren_depth == 0 && brace_depth == 0 &&
                            bracket_depth == 0) {
                            offset += 2;
                            closed = true;
                            break;
                        }
                        if (type == TokenType::LEFT_PAREN) {
                            ++paren_depth;
                        } else if (type == TokenType::RIGHT_PAREN &&
                                   paren_depth > 0) {
                            --paren_depth;
                        } else if (type == TokenType::LEFT_BRACE) {
                            ++brace_depth;
                        } else if (type == TokenType::RIGHT_BRACE &&
                                   brace_depth > 0) {
                            --brace_depth;
                        } else if (type == TokenType::LEFT_BRACKET) {
                            ++bracket_depth;
                        } else if (type == TokenType::RIGHT_BRACKET &&
                                   bracket_depth > 0) {
                            --bracket_depth;
                        }
                        ++offset;
                    }
                    if (!closed) {
                        break;
                    }
                }
                return offset;
            };
            auto structor_suffix_matches = [&](size_t suffix_offset) {
                suffix_offset = skip_standard_attribute_lists(suffix_offset);
                for (size_t index = 0; index < structor_parentheses; ++index) {
                    if (peek(suffix_offset + index).type !=
                        TokenType::RIGHT_PAREN) {
                        return false;
                    }
                }
                suffix_offset += structor_parentheses;
                return peek(suffix_offset).type == TokenType::LEFT_PAREN;
            };
            bool starts_constructor =
                !tag.empty() &&
                peek(structor_name_offset).type == TokenType::IDENTIFIER &&
                peek(structor_name_offset).value == tag &&
                structor_suffix_matches(structor_name_offset + 1);
            bool starts_destructor =
                !tag.empty() &&
                peek(structor_name_offset).type == TokenType::BITWISE_NOT &&
                peek(structor_name_offset + 1).type == TokenType::IDENTIFIER &&
                peek(structor_name_offset + 1).value == tag &&
                structor_suffix_matches(structor_name_offset + 2);
            if (!starts_constructor && !starts_destructor) {
                return false;
            }

            ParsedSpecialMemberPrefix prefix =
                parse_special_member_prefix(leading_attrs);
            collect::DeclFlags& flags = prefix.flags;
            ParsedExplicitSpecifier& explicit_specifier =
                prefix.explicit_specifier;

            for (size_t index = 0; index < structor_parentheses; ++index) {
                consume();
            }
            bool is_destructor = match(TokenType::BITWISE_NOT);
            if (is_destructor && flags.is_consteval) {
                diagnose(DiagnosticLevel::Error,
                         "a destructor cannot be declared 'consteval'",
                         loc_for_index(member_begin));
            }
            if (starts_constructor && leading_virtual) {
                diagnose(DiagnosticLevel::Error,
                         "a constructor cannot be declared 'virtual'",
                         loc_for_index(member_begin));
            }
            if (prefix.invalid_static) {
                diagnose(DiagnosticLevel::Error,
                         starts_constructor
                             ? "a constructor cannot be declared 'static'"
                             : "a destructor cannot be declared 'static'",
                         loc_for_index(member_begin));
            }
            size_t name_begin = current_raw_index();
            if (!is_identifier_token(current().type)) {
                diagnose(DiagnosticLevel::Error, "expected special member name", current_loc());
                skip_until_statement_boundary();
                return true;
            }
            std::string member_name = is_destructor ? "~" + std::string(current().value) : std::string(current().value);
            SrcLoc member_loc = current().loc;
            consume();
            LayoutAttrs name_attrs = parse_layout_attributes();
            if (structor_parentheses != 0) {
                for (size_t index = 0; index < structor_parentheses;
                     ++index) {
                    if (!match(TokenType::RIGHT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ')' around special member name",
                                 current_loc());
                        break;
                    }
                }
            }
            NodeId name_node = make_node(NodeKind::Name,
                                         name_begin,
                                         last_consumed_raw_end(),
                                         {},
                                         text_payload(member_name));
            std::vector<NodeId> member_children = prefix.attrs.syntax;
            member_children.push_back(name_node);
            member_children.insert(member_children.end(),
                                   name_attrs.syntax.begin(),
                                   name_attrs.syntax.end());

            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error, "expected parameter list in special member declaration", current_loc());
                skip_until_statement_boundary();
                return true;
            }
            bool is_variadic = false;
            std::vector<ParsedParam> params = parse_parameter_list(
                false,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberParameter),
                &is_variadic);
            collect::Session::TemplateInfo abbreviated_info;
            DeclarationParser abbreviated_invention(*this);
            abbreviated_invention.abbreviated_template_target =
                &abbreviated_info;
            for (size_t parameter_index = 0;
                 parameter_index < params.size();
                 ++parameter_index) {
                ParsedParam& param = params[parameter_index];
                ParsedDeclarator parameter;
                parameter.type = param.type;
                parameter.type_ref = param.type_ref;
                parameter.loc = param.loc;
                rewrite_abbreviated_function_parameter(
                    abbreviated_invention,
                    parameter,
                    param.is_parameter_pack,
                    static_cast<uint32_t>(parameter_index),
                    param.abbreviated_type_constraints,
                    param.loc);
                param.type = parameter.type;
                param.type_ref = parameter.type_ref;
            }
            bool is_abbreviated_template = !abbreviated_info
                .invented_function_parameters.empty();
            if (is_abbreviated_template &&
                !lang_opts_.is_cxx20_or_later()) {
                diagnose(DiagnosticLevel::Error,
                         "abbreviated function templates require C++20",
                         member_loc);
            }
            if (is_destructor && is_abbreviated_template) {
                diagnose(DiagnosticLevel::Error,
                         "a destructor cannot be an abbreviated function template",
                         member_loc);
                is_abbreviated_template = false;
            }
            std::vector<cir::TypeRef> param_types;
            std::vector<uint8_t> parameter_pack_flags;
            bool has_parameter_pack = false;
            param_types.reserve(params.size());
            parameter_pack_flags.reserve(params.size());
            for (const ParsedParam& param : params) {
                if (param.syntax != InvalidNodeId) {
                    member_children.push_back(param.syntax);
                }
                if (param.is_parameter_pack_expansion_sentinel) {
                    continue;
                }
                param_types.push_back(param.type_ref);
                uint8_t pack_flag = param.is_parameter_pack ? 1 : 0;
                parameter_pack_flags.push_back(pack_flag);
                has_parameter_pack = has_parameter_pack || pack_flag != 0;
            }
            if (!has_parameter_pack) {
                parameter_pack_flags.clear();
            }
            if (is_destructor &&
                (!param_types.empty() || is_variadic)) {
                diagnose(DiagnosticLevel::Error,
                         "destructor declaration cannot have parameters",
                         member_loc);
            }

            ParsedRecordExceptionSpec exception_spec =
                parse_special_member_exception_spec(member_children);

            cir::TypeRef void_type =
                collect_session_.type_ref(collect_session_.file().builtin_type(cir::BuiltinTypeKind::Void));
            cir::TypeId function_type =
                collect_session_.function_type(
                    void_type,
                    param_types,
                    is_variadic,
                    true,
                    false,
                    std::move(exception_spec.spec),
                    parameter_pack_flags);

            collect::RecordMethodInput method;
            method.name = member_name;
            method.type = function_type;
            method.params = param_inputs_from_parsed_params(
                params,
                /*move_runtime_fragments=*/false);
            method.loc = member_loc;
            method.declared_access = current_access;
            method.flags = flags;
            method.attrs = prefix.attrs.attrs;
            method.attrs.append(name_attrs.attrs);
            method.is_virtual = leading_virtual && is_destructor;
            method.is_constructor = !is_destructor;
            method.is_destructor = is_destructor;
            method.is_function_template = is_abbreviated_template;
            method.has_explicit_exception_spec =
                exception_spec.has_explicit;
            method.has_deferred_noexcept_operand = exception_spec.deferred;
            method.noexcept_operand_begin = exception_spec.operand_begin;
            method.noexcept_operand_end = exception_spec.operand_end;
            method.noexcept_operand_loc = exception_spec.operand_loc;
            method.noexcept_declaration_context =
                exception_spec.declaration_context;
            method.noexcept_lookup_generation =
                exception_spec.lookup_generation;
            method.is_explicit = prefix.is_explicit();
            method.explicit_specifier = explicit_specifier.kind;
            method.explicit_expression_begin =
                explicit_specifier.expression_begin;
            method.explicit_expression_end = explicit_specifier.expression_end;
            method.explicit_value_expression =
                explicit_specifier.value_expression;
            method.explicit_declaration_context =
                explicit_specifier.declaration_context;
            method.explicit_lookup_generation =
                explicit_specifier.lookup_generation;
            if (is_destructor && explicit_specifier.present()) {
                diagnose(DiagnosticLevel::Error,
                         "a destructor cannot have an explicit specifier",
                         explicit_specifier.loc);
            }
            size_t method_index = methods.size();
            size_t trailing_requires_constraint_begin = 0;
            size_t trailing_requires_constraint_end = 0;
            std::optional<collect::Session::NormalizedConstraint>
                trailing_requires_normal_form;
            if (match(TokenType::REQUIRES_KW)) {
                SrcLoc requires_loc = last_consumed_loc();
                std::optional<bool> constraint_value;
                collect::Session::NormalizedConstraint normal_form;
                bool valid = parse_and_validate_constraint_expression(
                    requires_loc,
                    trailing_requires_constraint_begin,
                    trailing_requires_constraint_end,
                    &constraint_value,
                    &normal_form);
                if (method.is_virtual) {
                    diagnose(DiagnosticLevel::Error,
                             "a virtual function cannot have an associated requires-clause",
                             requires_loc);
                }
                if (valid) {
                    retain_method_constraint(method_index,
                                             method,
                                             trailing_requires_constraint_begin,
                                             trailing_requires_constraint_end,
                                             normal_form,
                                             constraint_value);
                    trailing_requires_normal_form = std::move(normal_form);
                } else {
                    method.constraint_satisfaction =
                        cir::ConstraintSatisfactionKind::Invalid;
                }
            }
            bool parsed_body = parse_member_function_tail(method,
                                                          member_children,
                                                          method.is_constructor,
                                                          std::move(params),
                                                          false);
            method.has_deferred_definition = parsed_body;
            collect_session_.declare_record_method_shell(record.entity,
                                                         method);
            methods.push_back(std::move(method));

            if (is_abbreviated_template) {
                abbreviated_info.name = member_name;
                abbreviated_info.pattern_type = function_type;
                abbreviated_info.explicit_specifier =
                    explicit_specifier.kind;
                abbreviated_info.explicit_expression_begin =
                    explicit_specifier.expression_begin;
                abbreviated_info.explicit_expression_end =
                    explicit_specifier.expression_end;
                abbreviated_info.explicit_value_expression =
                    explicit_specifier.value_expression;
                if (trailing_requires_normal_form.has_value()) {
                    record_trailing_function_requires_clause(
                        abbreviated_info,
                        trailing_requires_constraint_begin,
                        trailing_requires_constraint_end,
                        std::move(trailing_requires_normal_form));
                }
                std::optional<PendingMemberBody> template_body;
                if (parsed_body && !pending_bodies.empty() &&
                    pending_bodies.back().method_index == method_index) {
                    template_body = std::move(pending_bodies.back());
                    pending_bodies.pop_back();
                }
                abbreviated_info.has_definition = template_body.has_value();
                PendingMemberTemplate pending;
                pending.method_index = method_index;
                pending.info = std::move(abbreviated_info);
                pending.body = std::move(template_body);
                pending.loc = member_loc;
                pending_member_templates.push_back(std::move(pending));
            }

            children.push_back(make_node(NodeKind::FunctionDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         member_children,
                                         text_payload(member_name),
                                         parsed_body ? NodeFlagHasError : NodeFlagNone));

            if (!parsed_body && !match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after class member declaration",
                         current_loc());
                skip_until_statement_boundary();
            }
            return true;
        };

        auto template_head_end_offset_from =
            [&](size_t start) -> std::optional<size_t> {
            if (peek(start).type != TokenType::TEMPLATE ||
                peek(start + 1).type != TokenType::LESS_THAN) {
                return std::nullopt;
            }
            size_t offset = start + 1;
            int depth = 0;
            int paren_depth = 0;
            int bracket_depth = 0;
            int brace_depth = 0;
            while (true) {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof) {
                    return std::nullopt;
                }
                bool inside_group =
                    paren_depth > 0 || bracket_depth > 0 || brace_depth > 0;
                if (type == TokenType::LEFT_PAREN) {
                    ++paren_depth;
                } else if (type == TokenType::RIGHT_PAREN &&
                           paren_depth > 0) {
                    --paren_depth;
                } else if (type == TokenType::LEFT_BRACKET) {
                    ++bracket_depth;
                } else if (type == TokenType::RIGHT_BRACKET &&
                           bracket_depth > 0) {
                    --bracket_depth;
                } else if (type == TokenType::LEFT_BRACE) {
                    ++brace_depth;
                } else if (type == TokenType::RIGHT_BRACE &&
                           brace_depth > 0) {
                    --brace_depth;
                } else if (!inside_group && type == TokenType::LESS_THAN) {
                    ++depth;
                } else if (!inside_group &&
                           type == TokenType::GREATER_THAN) {
                    --depth;
                    ++offset;
                    if (depth == 0) {
                        return offset;
                    }
                    continue;
                } else if (!inside_group &&
                           type == TokenType::RIGHT_SHIFT) {
                    depth -= 2;
                    ++offset;
                    if (depth <= 0) {
                        return offset;
                    }
                    continue;
                }
                ++offset;
            }
        };
        auto template_head_end_offset = [&]() -> std::optional<size_t> {
            return template_head_end_offset_from(0);
        };
        enum class FriendTemplateStart {
            None,
            Class,
            Function,
        };
        auto friend_template_start_after_head =
            [&](std::optional<size_t> after_head) {
                if (!after_head.has_value()) {
                    return FriendTemplateStart::None;
                }
                if (peek(*after_head).type == TokenType::FRIEND_KW) {
                    TokenType target = peek(*after_head + 1).type;
                    return target == TokenType::CLASS ||
                                   target == TokenType::STRUCT
                        ? FriendTemplateStart::Class
                        : FriendTemplateStart::Function;
                }
                if (peek(*after_head).type != TokenType::REQUIRES_KW) {
                    return FriendTemplateStart::None;
                }

                RevertingTentativeParsingAction tentative(
                    *this, TentativeMode::CollectBacked);
                Token template_token = current();
                consume();
                collect::Session::TemplateInfo probe;
                if (!parse_cxx_template_head(probe,
                                             template_token.loc) ||
                    !check(TokenType::FRIEND_KW)) {
                    return FriendTemplateStart::None;
                }
                TokenType target = peek(1).type;
                return target == TokenType::CLASS ||
                               target == TokenType::STRUCT
                    ? FriendTemplateStart::Class
                    : FriendTemplateStart::Function;
            };

        auto template_member_decl_has_static_specifier =
            [&](size_t offset) -> bool {
            enum class RequiresExpressionPrefix {
                None,
                AfterRequires,
                InParameterList,
                AwaitingBody,
            };
            int paren_depth = 0;
            int bracket_depth = 0;
            int brace_depth = 0;
            int angle_depth = 0;
            int requires_parameter_outer_paren_depth = 0;
            std::vector<int> paren_angle_depths;
            std::vector<int> bracket_angle_depths;
            bool saw_requires_clause = false;
            RequiresExpressionPrefix requires_expression_prefix =
                RequiresExpressionPrefix::None;
            while (true) {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof) {
                    return false;
                }
                if (brace_depth > 0) {
                    if (type == TokenType::LEFT_BRACE) {
                        ++brace_depth;
                    } else if (type == TokenType::RIGHT_BRACE) {
                        --brace_depth;
                    }
                    ++offset;
                    continue;
                }
                bool at_top_level =
                    paren_depth == 0 &&
                    bracket_depth == 0 &&
                    brace_depth == 0 &&
                    angle_depth == 0;
                if (at_top_level && type == TokenType::SEMICOLON) {
                    return false;
                }
                if (at_top_level &&
                    type == TokenType::STATIC) {
                    return true;
                }

                if (brace_depth == 0 &&
                    requires_expression_prefix ==
                        RequiresExpressionPrefix::None &&
                    type == TokenType::REQUIRES_KW) {
                    if (!saw_requires_clause && at_top_level) {
                        saw_requires_clause = true;
                    } else if (saw_requires_clause) {
                        requires_expression_prefix =
                            RequiresExpressionPrefix::AfterRequires;
                    }
                    ++offset;
                    continue;
                }

                if (requires_expression_prefix ==
                    RequiresExpressionPrefix::AfterRequires) {
                    if (type == TokenType::LEFT_PAREN) {
                        requires_parameter_outer_paren_depth = paren_depth;
                        requires_expression_prefix =
                            RequiresExpressionPrefix::InParameterList;
                    } else if (type == TokenType::LEFT_BRACE) {
                        ++brace_depth;
                        requires_expression_prefix =
                            RequiresExpressionPrefix::None;
                        ++offset;
                        continue;
                    } else {
                        requires_expression_prefix =
                            RequiresExpressionPrefix::None;
                    }
                } else if (requires_expression_prefix ==
                           RequiresExpressionPrefix::AwaitingBody) {
                    if (type == TokenType::LEFT_BRACE) {
                        ++brace_depth;
                        requires_expression_prefix =
                            RequiresExpressionPrefix::None;
                        ++offset;
                        continue;
                    }
                    requires_expression_prefix =
                        RequiresExpressionPrefix::None;
                }

                if (type == TokenType::LEFT_BRACE) {
                    if (at_top_level) {
                        return false;
                    }
                    ++brace_depth;
                }
                if (type == TokenType::LEFT_PAREN) {
                    paren_angle_depths.push_back(angle_depth);
                    ++paren_depth;
                } else if (type == TokenType::RIGHT_PAREN) {
                    if (paren_depth > 0) {
                        --paren_depth;
                        angle_depth = paren_angle_depths.back();
                        paren_angle_depths.pop_back();
                    }
                    if (requires_expression_prefix ==
                            RequiresExpressionPrefix::InParameterList &&
                        paren_depth ==
                            requires_parameter_outer_paren_depth) {
                        requires_expression_prefix =
                            RequiresExpressionPrefix::AwaitingBody;
                    }
                } else if (type == TokenType::LEFT_BRACKET) {
                    bracket_angle_depths.push_back(angle_depth);
                    ++bracket_depth;
                } else if (type == TokenType::RIGHT_BRACKET) {
                    if (bracket_depth > 0) {
                        --bracket_depth;
                        angle_depth = bracket_angle_depths.back();
                        bracket_angle_depths.pop_back();
                    }
                } else if (type == TokenType::LESS_THAN) {
                    ++angle_depth;
                } else if (type == TokenType::GREATER_THAN) {
                    if (angle_depth > 0) {
                        --angle_depth;
                    }
                } else if (type == TokenType::RIGHT_SHIFT) {
                    angle_depth = angle_depth > 1 ? angle_depth - 2 : 0;
                }
                ++offset;
            }
        };

        auto template_member_decl_may_have_function_declarator =
            [&](size_t offset) -> bool {
            int angle_depth = 0;
            while (true) {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof ||
                    (angle_depth == 0 &&
                     (type == TokenType::SEMICOLON ||
                      type == TokenType::LEFT_BRACE ||
                      (type == TokenType::ASSIGN &&
                       (offset == 0 ||
                        peek(offset - 1).type !=
                            TokenType::OPERATOR_KW))))) {
                    return false;
                }
                if (angle_depth == 0 && type == TokenType::LEFT_PAREN) {
                    return true;
                }
                if (type == TokenType::LESS_THAN) {
                    ++angle_depth;
                } else if (type == TokenType::GREATER_THAN) {
                    if (angle_depth > 0) {
                        --angle_depth;
                    }
                } else if (type == TokenType::RIGHT_SHIFT) {
                    angle_depth = angle_depth > 1 ? angle_depth - 2 : 0;
                }
                ++offset;
            }
        };

        auto template_member_decl_is_deduction_guide =
            [&](size_t offset) -> bool {
            if (peek(offset).type == TokenType::EXPLICIT_KW) {
                ++offset;
                if (peek(offset).type == TokenType::LEFT_PAREN) {
                    int depth = 0;
                    do {
                        TokenType type = peek(offset).type;
                        if (type == TokenType::Eof) {
                            return false;
                        }
                        if (type == TokenType::LEFT_PAREN) {
                            ++depth;
                        } else if (type == TokenType::RIGHT_PAREN) {
                            --depth;
                        }
                        ++offset;
                    } while (depth > 0);
                }
            }
            if (!is_identifier_token(peek(offset).type) ||
                peek(offset + 1).type != TokenType::LEFT_PAREN) {
                return false;
            }
            ++offset;
            int depth = 0;
            do {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof) {
                    return false;
                }
                if (type == TokenType::LEFT_PAREN) {
                    ++depth;
                } else if (type == TokenType::RIGHT_PAREN) {
                    --depth;
                }
                ++offset;
            } while (depth > 0);
            return peek(offset).type == TokenType::ARROW;
        };

        enum class TemplatedSpecialMemberKind {
            None,
            Constructor,
            Destructor,
            Conversion,
        };

        auto templated_special_member_kind_after_head =
            [&](size_t offset) -> TemplatedSpecialMemberKind {
            auto classify_at =
                [&](size_t candidate,
                    bool scanning_constraint) -> TemplatedSpecialMemberKind {
                auto starts_conversion_operator = [&](size_t operator_offset) {
                    if (peek(operator_offset).type !=
                        TokenType::OPERATOR_KW) {
                        return false;
                    }
                    TokenType conversion_type =
                        peek(operator_offset + 1).type;
                    return is_type_start(conversion_type) ||
                        conversion_type == TokenType::IDENTIFIER ||
                        conversion_type == TokenType::SCOPE_RESOLUTION ||
                        conversion_type == TokenType::TYPENAME ||
                        conversion_type == TokenType::DECLTYPE_KW;
                };
                candidate = skip_cxx_special_member_prefix(candidate);
                if (!tag.empty() &&
                    peek(candidate).type == TokenType::IDENTIFIER &&
                    peek(candidate).value == tag &&
                    peek(candidate + 1).type == TokenType::LEFT_PAREN) {
                    return TemplatedSpecialMemberKind::Constructor;
                }
                if (!tag.empty() &&
                    peek(candidate).type == TokenType::BITWISE_NOT &&
                    peek(candidate + 1).type == TokenType::IDENTIFIER &&
                    peek(candidate + 1).value == tag) {
                    return TemplatedSpecialMemberKind::Destructor;
                }
                if (peek(candidate).type == TokenType::OPERATOR_KW &&
                    (!scanning_constraint ||
                     starts_conversion_operator(candidate))) {
                    return TemplatedSpecialMemberKind::Conversion;
                }
                while (peek(candidate).type == TokenType::LEFT_PAREN) {
                    ++candidate;
                }
                return peek(candidate).type == TokenType::OPERATOR_KW &&
                        (!scanning_constraint ||
                         starts_conversion_operator(candidate))
                    ? TemplatedSpecialMemberKind::Conversion
                    : TemplatedSpecialMemberKind::None;
            };

            TemplatedSpecialMemberKind direct =
                classify_at(offset, /*scanning_constraint=*/false);
            if (direct != TemplatedSpecialMemberKind::None ||
                peek(offset).type != TokenType::REQUIRES_KW) {
                return direct;
            }

            auto constructor_suffix_follows = [&](size_t candidate) {
                candidate = skip_cxx_special_member_prefix(candidate);
                if (peek(candidate).type != TokenType::IDENTIFIER ||
                    peek(candidate).value != tag ||
                    peek(candidate + 1).type != TokenType::LEFT_PAREN) {
                    return false;
                }
                size_t tail = candidate + 1;
                int depth = 0;
                do {
                    TokenType type = peek(tail).type;
                    if (type == TokenType::Eof) {
                        return false;
                    }
                    if (type == TokenType::LEFT_PAREN) {
                        ++depth;
                    } else if (type == TokenType::RIGHT_PAREN) {
                        --depth;
                    }
                    ++tail;
                } while (depth > 0);
                tail = skip_member_prefix_attributes(tail);
                TokenType suffix = peek(tail).type;
                return suffix == TokenType::NOEXCEPT_KW ||
                    suffix == TokenType::THROW_KW ||
                    suffix == TokenType::REQUIRES_KW ||
                    suffix == TokenType::COLON ||
                    suffix == TokenType::LEFT_BRACE ||
                    suffix == TokenType::TRY_KW ||
                    suffix == TokenType::SEMICOLON ||
                    suffix == TokenType::ASSIGN;
            };

            int paren_depth = 0;
            int bracket_depth = 0;
            int brace_depth = 0;
            bool requires_expression_pending = false;
            for (++offset; ; ++offset) {
                TokenType type = peek(offset).type;
                if (type == TokenType::Eof ||
                    (paren_depth == 0 && bracket_depth == 0 &&
                     brace_depth == 0 && type == TokenType::SEMICOLON)) {
                    return TemplatedSpecialMemberKind::None;
                }
                bool at_top_level =
                    paren_depth == 0 && bracket_depth == 0 &&
                    brace_depth == 0;
                if (at_top_level) {
                    TemplatedSpecialMemberKind candidate =
                        classify_at(offset, /*scanning_constraint=*/true);
                    if (candidate == TemplatedSpecialMemberKind::Constructor) {
                        if (constructor_suffix_follows(offset)) {
                            return candidate;
                        }
                    } else if (candidate !=
                               TemplatedSpecialMemberKind::None) {
                        return candidate;
                    }
                    if (type == TokenType::REQUIRES_KW) {
                        requires_expression_pending = true;
                    } else if (type == TokenType::LEFT_BRACE) {
                        if (!requires_expression_pending) {
                            return TemplatedSpecialMemberKind::None;
                        }
                        requires_expression_pending = false;
                    }
                }
                if (type == TokenType::LEFT_PAREN) {
                    ++paren_depth;
                } else if (type == TokenType::RIGHT_PAREN &&
                           paren_depth > 0) {
                    --paren_depth;
                } else if (type == TokenType::LEFT_BRACKET) {
                    ++bracket_depth;
                } else if (type == TokenType::RIGHT_BRACKET &&
                           bracket_depth > 0) {
                    --bracket_depth;
                } else if (type == TokenType::LEFT_BRACE) {
                    ++brace_depth;
                } else if (type == TokenType::RIGHT_BRACE &&
                           brace_depth > 0) {
                    --brace_depth;
                }
            }
        };

        auto parse_member_function_template_tail =
            [&](collect::RecordMethodInput& method,
                std::vector<NodeId>& member_children,
                size_t member_begin,
                bool allow_pure_specifier,
                bool allow_inline_body,
                size_t method_index,
                std::vector<ParsedParam> body_params,
                std::optional<PendingMemberBody>* captured_body) -> bool {
            bool has_error = false;
            bool parsed_body = false;
            size_t init_begin = 0;
            size_t init_end = 0;
            if (method.is_constructor && check(TokenType::TRY_KW) &&
                allow_inline_body) {
                size_t body_begin = current_raw_index();
                size_t body_end = skip_function_try_block_tokens();
                member_children.push_back(make_node(NodeKind::DeferredBody,
                                                    body_begin,
                                                    body_end,
                                                    {},
                                                    text_payload("member body")));
                if (captured_body) {
                    PendingMemberBody pending;
                    pending.method_index = method_index;
                    pending.body_begin = body_begin;
                    pending.body_end = body_end;
                    pending.is_constructor_function_try = true;
                    pending.params = std::move(body_params);
                    *captured_body = std::move(pending);
                }
                parsed_body = true;
            } else if (method.is_constructor && match(TokenType::COLON)) {

                init_begin = current_raw_index();
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
                    }
                    if (type == TokenType::RIGHT_PAREN ||
                        type == TokenType::RIGHT_BRACE) {
                        --depth;
                    }
                    previous = type;
                    consume();
                }
                init_end = current_raw_index();
                if (check(TokenType::LEFT_BRACE) && allow_inline_body) {
                    size_t body_begin = current_raw_index();
                    size_t body_end = skip_balanced_until_semicolon_or_brace();
                    member_children.push_back(make_node(NodeKind::DeferredBody,
                                                        init_begin,
                                                        body_end,
                                                        {},
                                                        text_payload("member body")));
                    if (captured_body) {
                        PendingMemberBody pending;
                        pending.method_index = method_index;
                        pending.body_begin = body_begin;
                        pending.body_end = body_end;
                        pending.init_begin = init_begin;
                        pending.init_end = init_end;
                        pending.params = std::move(body_params);
                        *captured_body = std::move(pending);
                    }
                    parsed_body = true;
                } else if (check(TokenType::LEFT_BRACE)) {
                    size_t body_begin = current_raw_index();
                    size_t body_end = skip_balanced_until_semicolon_or_brace();
                    member_children.push_back(make_node(NodeKind::DeferredBody,
                                                        init_begin,
                                                        body_end,
                                                        {},
                                                        text_payload("member body"),
                                                        NodeFlagHasError));
                    diagnose(DiagnosticLevel::Error,
                             "inline constructor and conversion member template bodies are not supported yet",
                             loc_for_index(body_begin));
                    has_error = true;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "constructor member initializers require a body",
                             loc_for_index(init_begin));
                    has_error = true;
                }
            } else if (check(TokenType::LEFT_BRACE) && allow_inline_body) {
                size_t body_begin = current_raw_index();
                size_t body_end = skip_balanced_until_semicolon_or_brace();
                member_children.push_back(make_node(NodeKind::DeferredBody,
                                                    body_begin,
                                                    body_end,
                                                    {},
                                                    text_payload("member body")));
                if (captured_body) {
                    PendingMemberBody pending;
                    pending.method_index = method_index;
                    pending.body_begin = body_begin;
                    pending.body_end = body_end;
                    pending.params = std::move(body_params);
                    *captured_body = std::move(pending);
                }
                parsed_body = true;
            } else if (check(TokenType::LEFT_BRACE) || check(TokenType::TRY_KW)) {
                size_t body_begin = current_raw_index();
                size_t body_end = check(TokenType::TRY_KW)
                    ? skip_function_try_block_tokens()
                    : skip_balanced_until_semicolon_or_brace();
                member_children.push_back(make_node(NodeKind::DeferredBody,
                                                    body_begin,
                                                    body_end,
                                                    {},
                                                    text_payload("member body"),
                                                    NodeFlagHasError));
                diagnose(DiagnosticLevel::Error,
                         "inline constructor and conversion member template bodies are not supported yet",
                         loc_for_index(body_begin));
                has_error = true;
            } else if (check(TokenType::ASSIGN)) {
                SrcLoc suffix_loc = current_loc();
                consume();
                if (match(TokenType::DELETE)) {
                    method.is_deleted = true;
                } else if (match(TokenType::DEFAULT)) {
                    method.is_defaulted = true;
                } else if (allow_pure_specifier &&
                           check(TokenType::INTEGER_CONST) &&
                           current().value == "0") {
                    consume();
                    method.is_pure = true;
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "unsupported member function template declaration suffix",
                             suffix_loc);
                    skip_until_statement_boundary();
                    has_error = true;
                }
            }

            if (method.is_pure &&
                (check(TokenType::LEFT_BRACE) || check(TokenType::TRY_KW))) {
                size_t body_begin = current_raw_index();
                size_t body_end = skip_balanced_until_semicolon_or_brace();
                member_children.push_back(make_node(NodeKind::DeferredBody,
                                                    body_begin,
                                                    body_end,
                                                    {},
                                                    text_payload("member body"),
                                                    NodeFlagHasError));
                diagnose(DiagnosticLevel::Error,
                         "a pure-specifier cannot be combined with a function definition",
                         loc_for_index(body_begin));
                parsed_body = true;
                has_error = true;
            }

            if (!has_error && !parsed_body && !match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after member function template declaration",
                         current_loc());
                skip_until_statement_boundary();
                has_error = true;
            }
            (void)member_begin;
            return has_error;
        };

        auto parse_record_conversion_type_id = [&]() {
            return parse_conversion_type_id();
        };

        auto parse_templated_special_member =
            [&](size_t member_begin,
                TemplatedSpecialMemberKind kind) -> bool {
            Token template_token = current();
            consume();
            collect::Session::TemplateInfo info;
            if (!parse_cxx_template_head(info, template_token.loc)) {
                skip_balanced_until_semicolon_or_brace();
                children.push_back(make_node(NodeKind::UnknownDecl,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {},
                                             text_payload("template"),
                                             NodeFlagHasError));
                return true;
            }

            LayoutAttrs leading_member_attrs = parse_layout_attributes();
            size_t function_definition_begin = current_raw_index();
            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(info, template_token.loc);

            ParsedSpecialMemberPrefix prefix =
                parse_special_member_prefix(std::move(leading_member_attrs));
            collect::DeclFlags& flags = prefix.flags;
            ParsedExplicitSpecifier& explicit_specifier =
                prefix.explicit_specifier;
            bool declaration_has_error = prefix.has_error;

            if (kind == TemplatedSpecialMemberKind::Destructor) {
                diagnose(DiagnosticLevel::Error,
                         "destructor shall not be a member template",
                         current_loc());
                collect_session_.finish_template_header(std::move(header_scope));
                skip_until_statement_boundary();
                children.push_back(make_node(NodeKind::UnknownDecl,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {},
                                             text_payload("template"),
                                             NodeFlagHasError));
                return true;
            }

            std::vector<NodeId> member_children = prefix.attrs.syntax;
            std::string member_name;
            SrcLoc member_loc = current_loc();
            std::vector<ParsedParam> params;
            bool member_is_const = false;
            bool member_is_volatile = false;
            cir::FunctionRefQualifierKind member_ref_qualifier =
                cir::FunctionRefQualifierKind::None;
            bool has_trailing_requires_clause = false;
            bool trailing_requires_has_error = false;
            size_t trailing_requires_constraint_begin = 0;
            size_t trailing_requires_constraint_end = 0;
            std::optional<collect::Session::NormalizedConstraint>
                trailing_requires_normal_form;
            std::optional<bool> trailing_requires_value;
            cir::TypeRef return_type =
                collect_session_.type_ref(collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Void));

            if (kind == TemplatedSpecialMemberKind::Constructor) {
                size_t name_begin = current_raw_index();
                if (!check(TokenType::IDENTIFIER) || current().value != tag) {
                    diagnose(DiagnosticLevel::Error,
                             "expected constructor template declaration",
                             current_loc());
                    collect_session_.finish_template_header(std::move(header_scope));
                    skip_until_statement_boundary();
                    children.push_back(make_node(NodeKind::UnknownDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 {},
                                                 text_payload("template"),
                                                 NodeFlagHasError));
                    return true;
                }
                member_name = current().value;
                member_loc = current().loc;
                consume();
                member_children.push_back(make_node(NodeKind::Name,
                                                    name_begin,
                                                    last_consumed_raw_end(),
                                                    {},
                                                    text_payload(member_name)));
            } else {
                size_t conversion_parentheses = 0;
                while (match(TokenType::LEFT_PAREN)) {
                    ++conversion_parentheses;
                }
                size_t name_begin = current_raw_index();
                Token operator_token = current();
                consume();
                auto [conversion_type, conversion_syntax] =
                    parse_record_conversion_type_id();
                return_type = conversion_type;
                cir::TypeId resolved_conversion_type =
                    collect_session_.file().resolved_type(return_type.type);
                if (collect_session_.file().valid(resolved_conversion_type)) {
                    cir::TypeKind conversion_kind =
                        collect_session_.file().type(resolved_conversion_type).kind;
                    declaration_has_error = declaration_has_error ||
                        conversion_kind == cir::TypeKind::Function ||
                        conversion_kind == cir::TypeKind::Array;
                }
                if (collect_session_.contains_auto_type(return_type.type)) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "conversion function template cannot have a deduced return type",
                        operator_token.loc);
                    declaration_has_error = true;
                }
                member_name = "operator " +
                    collect_session_.file().format_type(conversion_type);
                member_loc = operator_token.loc;
                if (conversion_syntax != InvalidNodeId) {
                    member_children.push_back(conversion_syntax);
                }
                member_children.push_back(make_node(NodeKind::Name,
                                                    name_begin,
                                                    last_consumed_raw_end(),
                                                    {},
                                                    text_payload(member_name)));
                for (size_t index = 0; index < conversion_parentheses;
                     ++index) {
                    if (!match(TokenType::RIGHT_PAREN)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ')' around conversion-function-id",
                                 current_loc());
                        declaration_has_error = true;
                        break;
                    }
                }
            }

            if (prefix.invalid_static) {
                diagnose(DiagnosticLevel::Error,
                         kind == TemplatedSpecialMemberKind::Conversion
                             ? "conversion function must be a non-static member function"
                             : "a constructor cannot be declared 'static'",
                         member_loc);
                declaration_has_error = true;
            }

            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected parameter list in member function template declaration",
                         current_loc());
                collect_session_.finish_template_header(std::move(header_scope));
                skip_until_statement_boundary();
                children.push_back(make_node(NodeKind::UnknownDecl,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {},
                                             text_payload("template"),
                                             NodeFlagHasError));
                return true;
            }
            bool is_variadic = false;
            params = parse_parameter_list(
                false,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberParameter),
                &is_variadic);
            DeclarationParser abbreviated_invention(*this);
            abbreviated_invention.abbreviated_template_target = &info;
            for (size_t parameter_index = 0;
                 parameter_index < params.size();
                 ++parameter_index) {
                ParsedParam& param = params[parameter_index];
                ParsedDeclarator parameter;
                parameter.type = param.type;
                parameter.type_ref = param.type_ref;
                parameter.loc = param.loc;
                rewrite_abbreviated_function_parameter(
                    abbreviated_invention,
                    parameter,
                    param.is_parameter_pack,
                    static_cast<uint32_t>(parameter_index),
                    param.abbreviated_type_constraints,
                    param.loc);
                param.type = parameter.type;
                param.type_ref = parameter.type_ref;
            }
            std::vector<cir::TypeRef> param_types;
            std::vector<uint8_t> parameter_pack_flags;
            bool has_parameter_pack = false;
            param_types.reserve(params.size());
            parameter_pack_flags.reserve(params.size());
            for (const ParsedParam& param : params) {
                if (param.syntax != InvalidNodeId) {
                    member_children.push_back(param.syntax);
                }
                if (param.is_parameter_pack_expansion_sentinel) {
                    continue;
                }
                param_types.push_back(param.type_ref);
                uint8_t pack_flag = param.is_parameter_pack ? 1 : 0;
                parameter_pack_flags.push_back(pack_flag);
                has_parameter_pack = has_parameter_pack || pack_flag != 0;
            }
            if (!has_parameter_pack) {
                parameter_pack_flags.clear();
            }
            if (kind == TemplatedSpecialMemberKind::Conversion &&
                (!param_types.empty() || is_variadic)) {
                diagnose(DiagnosticLevel::Error,
                         "conversion function template cannot have parameters",
                         member_loc);
                declaration_has_error = true;
            }

            if (kind == TemplatedSpecialMemberKind::Conversion) {
                while (true) {
                    if (match(TokenType::CONST)) {
                        member_is_const = true;
                    } else if (match(TokenType::VOLATILE)) {
                        member_is_volatile = true;
                    } else if (match(TokenType::BITWISE_AND)) {
                        member_ref_qualifier =
                            cir::FunctionRefQualifierKind::LValue;
                    } else if (match(TokenType::LOGICAL_AND)) {
                        member_ref_qualifier =
                            cir::FunctionRefQualifierKind::RValue;
                    } else {
                        break;
                    }
                }
                if (match(TokenType::ARROW)) {
                    SrcLoc arrow_loc = last_consumed_loc();
                    DeclarationParser trailing_type_parser(
                        *this,
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::TrailingReturnType));
                    (void)trailing_type_parser.parse_declaration(false, true);
                    if (trailing_type_parser.type_syntax != InvalidNodeId) {
                        member_children.push_back(
                            trailing_type_parser.type_syntax);
                    }
                    diagnose(DiagnosticLevel::Error,
                             "conversion function cannot use a trailing return type",
                             arrow_loc);
                    declaration_has_error = true;
                }
            }

            ParsedRecordExceptionSpec exception_spec =
                parse_special_member_exception_spec(member_children);

            if (match(TokenType::REQUIRES_KW)) {
                SrcLoc requires_loc = last_consumed_loc();
                has_trailing_requires_clause = true;
                collect::Session::NormalizedConstraint normal_form;
                trailing_requires_has_error =
                    !parse_and_validate_constraint_expression(
                        requires_loc,
                        trailing_requires_constraint_begin,
                        trailing_requires_constraint_end,
                        &trailing_requires_value,
                        &normal_form);
                if (!trailing_requires_has_error) {
                    trailing_requires_normal_form = std::move(normal_form);
                }
            }

            cir::TypeId function_type =
                collect_session_.function_type(return_type,
                                               param_types,
                                               is_variadic,
                                               true,
                                               member_is_const,
                                               std::move(exception_spec.spec),
                                               parameter_pack_flags,
                                               member_ref_qualifier,
                                               member_is_volatile);
            collect_session_.finish_template_header(std::move(header_scope));

            collect::RecordMethodInput method;
            method.name = member_name;
            method.type = function_type;
            if (kind == TemplatedSpecialMemberKind::Conversion) {
                method.operator_function.kind =
                    cir::OperatorFunctionKind::Conversion;
                method.operator_function.conversion_type = return_type;
            }
            method.params = param_inputs_from_parsed_params(
                params,
                /*move_runtime_fragments=*/false);
            method.loc = member_loc;
            method.declared_access = current_access;
            method.flags = flags;
            method.attrs = prefix.attrs.attrs;
            method.is_function_template = true;
            method.is_conversion_function =
                kind == TemplatedSpecialMemberKind::Conversion;
            method.is_constructor =
                kind == TemplatedSpecialMemberKind::Constructor;
            method.is_explicit = prefix.is_explicit();
            method.has_explicit_exception_spec =
                exception_spec.has_explicit;
            method.has_deferred_noexcept_operand = exception_spec.deferred;
            method.noexcept_operand_begin = exception_spec.operand_begin;
            method.noexcept_operand_end = exception_spec.operand_end;
            method.noexcept_operand_loc = exception_spec.operand_loc;
            method.noexcept_declaration_context =
                exception_spec.declaration_context;
            method.noexcept_lookup_generation =
                exception_spec.lookup_generation;
            method.explicit_specifier = explicit_specifier.kind;
            method.explicit_expression_begin =
                explicit_specifier.expression_begin;
            method.explicit_expression_end = explicit_specifier.expression_end;
            method.explicit_value_expression =
                explicit_specifier.value_expression;
            method.explicit_declaration_context =
                explicit_specifier.declaration_context;
            method.explicit_lookup_generation =
                explicit_specifier.lookup_generation;
            size_t method_index = methods.size();
            if (has_trailing_requires_clause &&
                !trailing_requires_has_error) {
                retain_method_constraint(
                    method_index,
                    method,
                    trailing_requires_constraint_begin,
                    trailing_requires_constraint_end,
                    trailing_requires_normal_form,
                    trailing_requires_value);
            }
            std::optional<PendingMemberBody> pending_body;
            bool tail_has_error = parse_member_function_template_tail(
                method,
                member_children,
                member_begin,
                /*allow_pure_specifier=*/false,
                /*allow_inline_body=*/
                    kind == TemplatedSpecialMemberKind::Constructor ||
                    kind == TemplatedSpecialMemberKind::Conversion,
                method_index,
                std::move(params),
                &pending_body);
            bool has_error = declaration_has_error ||
                             trailing_requires_has_error || tail_has_error;

            collect_session_.declare_record_method_shell(record.entity,
                                                         method);
            cir::OperatorFunctionIdentity operator_function =
                method.operator_function;
            methods.push_back(std::move(method));
            if (!has_error) {
                info.name = member_name;
                info.operator_function = operator_function;
                info.pattern_type = function_type;
                info.definition_begin = function_definition_begin;
                info.explicit_specifier = explicit_specifier.kind;
                info.explicit_expression_begin =
                    explicit_specifier.expression_begin;
                info.explicit_expression_end =
                    explicit_specifier.expression_end;
                info.explicit_value_expression =
                    explicit_specifier.value_expression;
                if (has_trailing_requires_clause) {
                    record_trailing_function_requires_clause(
                        info,
                        trailing_requires_constraint_begin,
                        trailing_requires_constraint_end,
                        std::move(trailing_requires_normal_form));
                }
                info.has_definition = pending_body.has_value();
                PendingMemberTemplate pending;
                pending.method_index = method_index;
                pending.info = std::move(info);
                pending.body = std::move(pending_body);
                pending.loc = template_token.loc;
                pending_member_templates.push_back(std::move(pending));
            }

            children.push_back(make_node(NodeKind::FunctionDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         member_children,
                                         text_payload(member_name),
                                         has_error ? NodeFlagHasError
                                                   : NodeFlagNone));
            return true;
        };

        auto parse_nonstatic_member_function_template =
            [&](size_t member_begin) -> bool {
            Token template_token = current();
            consume();
            collect::Session::TemplateInfo info;
            if (!parse_cxx_template_head(info, template_token.loc)) {
                skip_balanced_until_semicolon_or_brace();
                children.push_back(make_node(NodeKind::UnknownDecl,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {},
                                             text_payload("template"),
                                             NodeFlagHasError));
                return true;
            }

            LayoutAttrs leading_member_attrs = parse_layout_attributes();
            size_t function_definition_begin = current_raw_index();

            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(info, template_token.loc);
            DeclarationParser member_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberDeclSpecifier));
            member_parser.abbreviated_template_target = &info;
            member_parser.allow_cxx_member_declarator_ids = true;
            cir::TypeRef member_base_type =
                member_parser.parse_declaration(false, true);
            NodeId member_type = member_parser.type_syntax;
            collect::DeclFlags flags = declaration_flags_from_parser(member_parser);
            member_parser.reset_declarator_parsing_state();
            member_parser.allow_cxx_member_declarator_ids = true;
            ParsedDeclarator declarator =
                member_parser.parse_declarator(member_base_type, true);
            LayoutAttrs declarator_attrs = parse_layout_attributes();
            collect_session_.finish_template_header(std::move(header_scope));

            std::vector<NodeId> member_children = leading_member_attrs.syntax;
            if (member_type != InvalidNodeId) {
                member_children.push_back(member_type);
            }
            if (declarator.syntax != InvalidNodeId) {
                member_children.push_back(declarator.syntax);
            }
            member_children.insert(member_children.end(),
                                   declarator_attrs.syntax.begin(),
                                   declarator_attrs.syntax.end());

            bool has_error = false;
            if (!declarator.is_function || declarator.name.empty()) {
                diagnose(DiagnosticLevel::Error,
                         "expected member function template declaration",
                         declarator.loc.isInvalid()
                             ? loc_for_index(member_begin)
                             : declarator.loc);
                has_error = true;
            }
            has_error =
                validate_symbolic_operator_membership(declarator, flags) ||
                has_error;
            collect::RecordMethodInput method;
            method.name = declarator.name;
            method.type = declarator.type;
            method.operator_function = declarator.operator_function;
            method.params = param_inputs_from_parsed_params(
                declarator.params,
                /*move_runtime_fragments=*/false);
            method.loc = declarator.loc.isInvalid()
                ? loc_for_index(member_begin)
                : declarator.loc;
            method.declared_access = current_access;
            method.flags = flags;
            method.is_static = flags.is_static;
            method.attrs = leading_member_attrs.attrs;
            method.is_function_template = true;
            method.has_explicit_exception_spec =
                declarator.has_noexcept_specifier;
            method.has_deferred_noexcept_operand =
                declarator.has_deferred_noexcept_operand;
            method.noexcept_operand_begin = declarator.noexcept_operand_begin;
            method.noexcept_operand_end = declarator.noexcept_operand_end;
            method.noexcept_operand_loc = declarator.noexcept_operand_loc;
            method.noexcept_declaration_context =
                declarator.noexcept_declaration_context;
            method.noexcept_lookup_generation =
                declarator.noexcept_lookup_generation;
            method.attrs.append(member_parser.leading_attrs);
            method.attrs.append(declarator.attrs);
            method.attrs.append(declarator_attrs.attrs);

            size_t method_index = methods.size();
            if (declarator.has_trailing_requires_clause) {
                retain_method_constraint(
                    method_index,
                    method,
                    declarator.trailing_requires_constraint_begin,
                    declarator.trailing_requires_constraint_end,
                    declarator.trailing_requires_normal_form,
                    declarator.trailing_requires_value);
            }
            std::optional<PendingMemberBody> pending_body;
            has_error = parse_member_function_template_tail(
                method,
                member_children,
                member_begin,
                /*allow_pure_specifier=*/true,
                /*allow_inline_body=*/true,
                method_index,
                std::move(declarator.params),
                &pending_body) || has_error;
            if (pending_body.has_value() &&
                declarator.has_placeholder_type_constraint) {
                pending_body->has_placeholder_return_type_constraint = true;
                pending_body->placeholder_return_type_constraint_begin =
                    declarator.placeholder_type_constraint_begin;
                pending_body->placeholder_return_type_constraint_end =
                    declarator.placeholder_type_constraint_end;
                pending_body->placeholder_return_type_constraint_loc =
                    declarator.placeholder_type_constraint_loc;
            }

            collect_session_.declare_record_method_shell(record.entity,
                                                         method);
            methods.push_back(std::move(method));
            if (!has_error) {
                info.name = declarator.name;
                info.operator_function = declarator.operator_function;
                info.pattern_type = declarator.type;
                info.definition_begin = function_definition_begin;
                record_trailing_function_requires_clause(info, declarator);
                info.has_definition = pending_body.has_value();
                PendingMemberTemplate pending;
                pending.method_index = method_index;
                pending.info = std::move(info);
                pending.body = std::move(pending_body);
                pending.loc = template_token.loc;
                pending_member_templates.push_back(std::move(pending));
            }

            children.push_back(make_node(NodeKind::FunctionDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         member_children,
                                         text_payload(declarator.name),
                                         has_error ? NodeFlagHasError : NodeFlagNone));
            return true;
        };

        auto parse_friend_class_template_declaration =
            [&](size_t member_begin) -> bool {
            Token template_token = current();
            consume();
            collect::Session::TemplateInfo friend_info;
            bool has_error =
                !parse_cxx_template_head(friend_info, template_token.loc);
            auto has_default_template_argument =
                [&](auto& self,
                    const std::vector<
                        collect::Session::TemplateParameter>& parameters)
                    -> bool {
                for (const collect::Session::TemplateParameter& parameter :
                     parameters) {
                    if (parameter.default_argument.has_value()) {
                        return true;
                    }
                    if (parameter.kind ==
                            collect::Session::TemplateParameterKind::
                                Template &&
                        self(self, parameter.nested_parameters())) {
                        return true;
                    }
                }
                return false;
            };
            if (has_default_template_argument(
                    has_default_template_argument,
                    friend_info.parameters)) {
                diagnose(
                    DiagnosticLevel::Error,
                    "default template arguments are not allowed in friend class template declarations",
                    template_token.loc);
                has_error = true;
            }
            if (!match(TokenType::FRIEND_KW)) {
                diagnose(DiagnosticLevel::Error,
                         "expected friend class template declaration",
                         current_loc());
                has_error = true;
            }
            cir::RecordKind friend_record_kind = cir::RecordKind::Struct;
            if (match(TokenType::CLASS)) {
                friend_record_kind = cir::RecordKind::Class;
            } else if (match(TokenType::STRUCT)) {
                friend_record_kind = cir::RecordKind::Struct;
            } else {
                diagnose(DiagnosticLevel::Error,
                         "expected class template friend type",
                         current_loc());
                has_error = true;
            }
            SrcLoc friend_loc = current_loc();
            std::string friend_name;
            cir::DeclContextId nominated_friend_context{};
            auto starts_qualified_primary_friend_template = [&]() {
                if (!check(TokenType::SCOPE_RESOLUTION) &&
                    (!is_identifier_token(current().type) ||
                     peek(1).type != TokenType::SCOPE_RESOLUTION)) {
                    return false;
                }
                RevertingTentativeParsingAction tentative(
                    *this, TentativeMode::CollectBacked);
                ParsedNestedName nested = parse_nested_name_specifier();
                if (nested.has_error ||
                    nested.depends_on_template_parameter ||
                    !nested.scope.context.valid() ||
                    !is_identifier_token(current().type) ||
                    peek(1).type == TokenType::LESS_THAN) {
                    return false;
                }
                const cir::File& file = collect_session_.file();
                cir::DeclContextKind kind =
                    file.decl_context(nested.scope.context).kind;
                return kind == cir::DeclContextKind::Record ||
                       kind == cir::DeclContextKind::Namespace ||
                       kind == cir::DeclContextKind::TranslationUnit;
            };
            if (!has_error &&
                starts_qualified_primary_friend_template()) {
                ParsedNestedName nested = parse_nested_name_specifier();
                if (nested.has_error || !nested.scope.context.valid() ||
                    !is_identifier_token(current().type)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected qualified friend class template name",
                             current_loc());
                    has_error = true;
                } else {
                    nominated_friend_context = nested.scope.context;
                    friend_name = current().value;
                    consume();
                }
            }
            auto starts_dependent_member_friend_type = [&]() {
                if (check(TokenType::SCOPE_RESOLUTION)) {
                    return true;
                }
                if (!is_identifier_token(current().type)) {
                    return false;
                }
                return peek(1).type == TokenType::SCOPE_RESOLUTION ||
                       (peek(1).type == TokenType::LESS_THAN &&
                        template_id_precedes_scope(0));
            };
            if (friend_name.empty() && !has_error &&
                starts_dependent_member_friend_type()) {
                collect::Session::InstantiationScope header_scope =
                    collect_session_.begin_template_header(friend_info,
                                                           template_token.loc);
                std::optional<cir::TypeRef> friend_type =
                    parse_cxx_qualified_type_name(
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::FriendTypeSpecifier));
                collect_session_.finish_template_header(
                    std::move(header_scope));
                if (!friend_type.has_value() || !friend_type->valid()) {
                    diagnose(DiagnosticLevel::Error,
                             "expected dependent member friend type",
                             current_loc());
                    has_error = true;
                } else {
                    collect_session_.add_pending_dependent_member_friend_type(
                        record.entity,
                        *friend_type,
                        friend_info.parameters,
                        friend_loc);
                }
                if (!match(TokenType::SEMICOLON)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ';' after dependent member friend declaration",
                             current_loc());
                    skip_until_statement_boundary();
                    has_error = true;
                }
                children.push_back(make_node(NodeKind::RecordDecl,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {},
                                             text_payload("friend"),
                                             has_error ? NodeFlagHasError
                                                       : NodeFlagNone));
                return true;
            }
            if (friend_name.empty() &&
                is_identifier_token(current().type)) {
                friend_name = current().value;
                consume();
            } else if (friend_name.empty()) {
                diagnose(DiagnosticLevel::Error,
                         "expected friend class template name",
                         current_loc());
                has_error = true;
            }
            if (check(TokenType::LESS_THAN)) {
                diagnose(
                    DiagnosticLevel::Error,
                    "friend declarations shall not declare partial specializations",
                    current_loc());
                has_error = true;
                skip_balanced_until_semicolon_or_brace();
            } else if (check(TokenType::LEFT_BRACE)) {
                diagnose(
                    DiagnosticLevel::Error,
                    "a friend class template shall not be defined in a class",
                    current_loc());
                has_error = true;
                skip_balanced_until_semicolon_or_brace();
                match(TokenType::SEMICOLON);
            } else if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after friend class template declaration",
                         current_loc());
                skip_until_statement_boundary();
                has_error = true;
            }
            if (!friend_name.empty() && !has_error) {
                const cir::File& file = collect_session_.file();
                cir::DeclContextId friend_context =
                    nominated_friend_context;
                if (!friend_context.valid()) {
                    for (cir::DeclContextId context =
                             collect_session_.current_decl_context();
                         context.valid();
                         context = file.decl_context(context).parent) {
                        cir::DeclContextKind kind =
                            file.decl_context(context).kind;
                        if (kind == cir::DeclContextKind::Namespace ||
                            kind == cir::DeclContextKind::TranslationUnit) {
                            friend_context = context;
                            break;
                        }
                    }
                }
                const collect::Session::TemplateInfo* target =
                    friend_context.valid()
                        ? collect_session_.template_info_in_context(
                              friend_context,
                              friend_name,
                              /*include_parents=*/
                                  !nominated_friend_context.valid())
                        : collect_session_.template_info_for_name(friend_name);
                cir::EntityId target_entity{};
                if (!target) {
                    collect::Session::TemplateInfo hidden_info =
                        friend_info;
                    hidden_info.name = friend_name;
                    hidden_info.is_class_template = true;
                    hidden_info.record_kind = friend_record_kind;
                    target_entity =
                        collect_session_.declare_hidden_friend_class_template(
                            std::move(hidden_info),
                            friend_context,
                            friend_loc);
                } else if (!target->is_class_template ||
                           target->is_partial_specialization) {
                    diagnose(DiagnosticLevel::Error,
                             "friend class template target is not a primary class template",
                             friend_loc);
                    has_error = true;
                } else if (!collect_session_.template_heads_equivalent(
                               friend_info,
                               *target)) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "friend class template parameter list does not match target template",
                        template_token.loc);
                    has_error = true;
                } else {
                    target_entity = target->entity;
                }
                if (target_entity.valid() && !has_error) {
                    collect_session_.add_pending_friend_class_template(
                        record.entity,
                        target_entity);
                }
            }
            children.push_back(make_node(NodeKind::RecordDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         {},
                                         text_payload(friend_name),
                                         has_error ? NodeFlagHasError
                                                   : NodeFlagNone));
            return true;
        };

        auto parse_dependent_member_friend_function_declaration =
            [&](size_t member_begin) -> bool {
            Token template_token = current();
            consume();
            collect::Session::TemplateInfo friend_info;
            bool has_error =
                !parse_cxx_template_head(friend_info, template_token.loc);
            if (!match(TokenType::FRIEND_KW)) {
                diagnose(DiagnosticLevel::Error,
                         "expected friend function template declaration",
                         current_loc());
                has_error = true;
            }

            size_t function_definition_begin = current_raw_index();
            collect::Session::InstantiationScope header_scope =
                collect_session_.begin_template_header(friend_info,
                                                       template_token.loc);
            DeclarationParser friend_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberDeclSpecifier));
            friend_parser.allow_cxx_member_declarator_ids = true;
            cir::TypeRef return_type =
                friend_parser.parse_declaration(false, true);
            NodeId return_type_syntax = friend_parser.type_syntax;
            ParsedDeclarator declarator =
                friend_parser.parse_declarator(return_type, true);
            collect_session_.finish_template_header(std::move(header_scope));

            std::vector<NodeId> member_children;
            if (return_type_syntax != InvalidNodeId) {
                member_children.push_back(return_type_syntax);
            }
            if (declarator.syntax != InvalidNodeId) {
                member_children.push_back(declarator.syntax);
            }

            bool friend_definition = check(TokenType::LEFT_BRACE);
            bool handled_friend_definition = false;
            if (!declarator.is_function || !declarator.has_name ||
                (!declarator.dependent_qualifier_type.type.valid() &&
                 !declarator.type.valid())) {
                diagnose(
                    DiagnosticLevel::Error,
                    "unsupported friend function template declaration",
                    declarator.loc.isInvalid() ? current_loc()
                                               : declarator.loc);
                has_error = true;
            } else if (!declarator.dependent_qualifier_type.type.valid()) {
                if (friend_definition &&
                    declarator.qualified_context.valid()) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "a friend function definition must have an unqualified name",
                        declarator.loc);
                    has_error = true;
                    skip_balanced_until_semicolon_or_brace();
                    handled_friend_definition = true;
                } else if (friend_definition) {
                    const cir::File& file = collect_session_.file();
                    cir::DeclContextId friend_context =
                        declarator.qualified_context;
                    if (!friend_context.valid()) {
                        for (cir::DeclContextId context =
                                 collect_session_.current_decl_context();
                             context.valid();
                             context = file.decl_context(context).parent) {
                            cir::DeclContextKind kind =
                                file.decl_context(context).kind;
                            if (kind == cir::DeclContextKind::Namespace ||
                                kind ==
                                    cir::DeclContextKind::TranslationUnit) {
                                friend_context = context;
                                break;
                            }
                        }
                    }
                    size_t definition_end =
                        skip_balanced_until_semicolon_or_brace();
                    collect::Session::TemplateInfo hidden_info =
                        friend_info;
                    hidden_info.name = declarator.name;
                    hidden_info.operator_function = declarator.operator_function;
                    hidden_info.pattern_type = declarator.type;
                    record_trailing_function_requires_clause(hidden_info,
                                                             declarator);
                    bool references_enclosing_parameter =
                        constraint_references_parameter_outside_head(
                            hidden_info);
                    hidden_info.has_definition = true;
                    hidden_info.definition_begin = function_definition_begin;
                    hidden_info.definition_end = definition_end;
                    hidden_info.lexical_context = friend_context;
                    cir::EntityId owner_template{};
                    std::vector<collect::Session::TemplateArgument>
                        owner_arguments;
                    if (collect_session_.template_arguments_for_record(
                            record.entity,
                            &owner_template,
                            &owner_arguments)) {
                        const collect::Session::TemplateInfo* owner_info =
                            collect_session_.template_info(owner_template);
                        if (owner_info && owner_info->is_class_template &&
                            !owner_arguments.empty()) {
                            collect::Session::TemplateArgumentBindings
                                owner_bindings;
                            if (collect_session_
                                    .bind_template_arguments_to_parameters(
                                        owner_info->parameters,
                                        owner_arguments,
                                        owner_bindings)) {
                                hidden_info.enclosing_instantiation_bindings
                                    .push_back(
                                        {owner_info->parameters,
                                         std::move(owner_bindings)});
                            }
                        }
                    }
                    std::vector<collect::ParamInput> hidden_params =
                        param_inputs_from_parsed_params(
                            declarator.params,
                            /*move_runtime_fragments=*/false);
                    cir::EntityId hidden =
                        collect_session_
                            .declare_hidden_friend_function_template(
                                std::move(hidden_info),
                                friend_context,
                                declarator.loc,
                                &hidden_params,
                                record.entity,
                                references_enclosing_parameter
                                    ? record.entity
                                    : cir::EntityId{});
                    if (hidden.valid()) {
                        collect_session_
                            .add_pending_friend_function_template(
                                record.entity,
                                hidden);
                        handled_friend_definition = true;
                    } else {
                        diagnose(
                            DiagnosticLevel::Error,
                            "unsupported friend function template definition",
                            declarator.loc);
                        has_error = true;
                    }
                } else {
                    const cir::File& file = collect_session_.file();
                    cir::DeclContextId friend_context =
                        declarator.qualified_context;
                    if (!friend_context.valid()) {
                        for (cir::DeclContextId context =
                                 collect_session_.current_decl_context();
                             context.valid();
                             context = file.decl_context(context).parent) {
                            cir::DeclContextKind kind =
                                file.decl_context(context).kind;
                            if (kind == cir::DeclContextKind::Namespace ||
                                kind ==
                                    cir::DeclContextKind::TranslationUnit) {
                                friend_context = context;
                                break;
                            }
                        }
                    }

                    std::vector<const collect::Session::TemplateInfo*>
                        candidates =
                            collect_session_
                                .function_template_infos_for_name(
                                    friend_context,
                                    declarator.name,
                                    /*include_parents=*/true);
                    const collect::Session::TemplateInfo* selected = nullptr;
                    bool ambiguous = false;
                    collect::Session::TemplateInfo friend_candidate =
                        friend_info;
                    friend_candidate.name = declarator.name;
                    friend_candidate.operator_function =
                        declarator.operator_function;
                    friend_candidate.pattern_type = declarator.type;
                    record_trailing_function_requires_clause(friend_candidate,
                                                             declarator);
                    bool references_enclosing_parameter =
                        constraint_references_parameter_outside_head(
                            friend_candidate);
                    if (references_enclosing_parameter) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "a friend function template declaration whose constraint depends on an enclosing template parameter shall be a definition",
                            declarator.trailing_requires_loc.isInvalid()
                                ? declarator.loc
                                : declarator.trailing_requires_loc);
                        has_error = true;
                    } else {
                        for (const collect::Session::TemplateInfo* candidate :
                             candidates) {
                            if (!candidate ||
                                !collect_session_
                                     .function_template_declarations_correspond(
                                         friend_candidate,
                                         *candidate)) {
                                continue;
                            }
                            if (selected) {
                                ambiguous = true;
                                break;
                            }
                            selected = candidate;
                        }
                    }
                    if (references_enclosing_parameter) {

                    } else if (ambiguous) {
                        diagnose(DiagnosticLevel::Error,
                                 "ambiguous friend function template target",
                                 declarator.loc);
                        has_error = true;
                    } else if (!selected) {
                        collect::Session::TemplateInfo hidden_info =
                            friend_info;
                        hidden_info.name = declarator.name;
                        hidden_info.operator_function = declarator.operator_function;
                        hidden_info.pattern_type = declarator.type;
                        record_trailing_function_requires_clause(hidden_info,
                                                                 declarator);
                        hidden_info.has_definition = false;
                        cir::EntityId hidden =
                            collect_session_
                                .declare_hidden_friend_function_template(
                                    std::move(hidden_info),
                                    friend_context,
                                    declarator.loc,
                                    nullptr,
                                    record.entity);
                        if (hidden.valid()) {
                            collect_session_
                                .add_pending_friend_function_template(
                                    record.entity,
                                    hidden);
                        } else {
                            diagnose(
                                DiagnosticLevel::Error,
                                "unsupported friend function template declaration",
                                declarator.loc);
                            has_error = true;
                        }
                    } else {
                        collect_session_.add_pending_friend_function_template(
                            record.entity,
                            selected->entity);
                    }
                }
            } else if (!friend_definition) {
                collect_session_
                    .add_pending_dependent_member_friend_function(
                        record.entity,
                        declarator.dependent_qualifier_type,
                        declarator.name,
                        declarator.type_ref,
                        friend_info.parameters,
                        declarator.loc);
            }
            if (friend_definition) {
                if (!handled_friend_definition) {
                    diagnose(DiagnosticLevel::Error,
                             "friend definitions inside the class are not supported yet",
                             current_loc());
                    skip_balanced_until_semicolon_or_brace();
                    has_error = true;
                }
            } else if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after friend declaration",
                         current_loc());
                skip_until_statement_boundary();
                has_error = true;
            }
            children.push_back(make_node(NodeKind::FunctionDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         std::move(member_children),
                                         text_payload(declarator.name),
                                         has_error ? NodeFlagHasError
                                                   : NodeFlagNone));
            return true;
        };

        auto parse_dependent_member_friend_function_template_declaration =
            [&](size_t member_begin) -> bool {
            Token outer_template_token = current();
            consume();
            collect::Session::TemplateInfo friend_info;
            bool has_error =
                !parse_cxx_template_head(friend_info, outer_template_token.loc);

            collect::Session::InstantiationScope outer_scope =
                collect_session_.begin_template_header(friend_info,
                                                       outer_template_token.loc);
            Token member_template_token = current();
            if (!match(TokenType::TEMPLATE)) {
                diagnose(DiagnosticLevel::Error,
                         "expected member template friend declaration",
                         current_loc());
                has_error = true;
            }
            collect::Session::TemplateInfo member_info;
            if (!parse_cxx_template_head(member_info,
                                         member_template_token.loc)) {
                has_error = true;
            }
            if (!match(TokenType::FRIEND_KW)) {
                diagnose(DiagnosticLevel::Error,
                         "expected friend member template declaration",
                         current_loc());
                has_error = true;
            }

            collect::Session::InstantiationScope member_scope =
                collect_session_.begin_template_header(member_info,
                                                       member_template_token.loc);
            DeclarationParser friend_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberDeclSpecifier));
            friend_parser.allow_cxx_member_declarator_ids = true;
            cir::TypeRef return_type =
                friend_parser.parse_declaration(false, true);
            NodeId return_type_syntax = friend_parser.type_syntax;
            ParsedDeclarator declarator =
                friend_parser.parse_declarator(return_type, true);
            collect_session_.finish_template_header(std::move(member_scope));
            collect_session_.finish_template_header(std::move(outer_scope));

            std::vector<NodeId> member_children;
            if (return_type_syntax != InvalidNodeId) {
                member_children.push_back(return_type_syntax);
            }
            if (declarator.syntax != InvalidNodeId) {
                member_children.push_back(declarator.syntax);
            }

            bool friend_definition = check(TokenType::LEFT_BRACE);
            if (!declarator.is_function || !declarator.has_name ||
                !declarator.dependent_qualifier_type.type.valid()) {
                diagnose(
                    DiagnosticLevel::Error,
                    "unsupported friend member template declaration",
                    declarator.loc.isInvalid() ? current_loc()
                                               : declarator.loc);
                has_error = true;
            } else if (!friend_definition) {
                collect_session_
                    .add_pending_dependent_member_friend_function_template(
                        record.entity,
                        declarator.dependent_qualifier_type,
                        declarator.name,
                        declarator.type_ref,
                        friend_info.parameters,
                        member_info.parameters,
                        declarator.loc);
            }
            if (friend_definition) {
                diagnose(DiagnosticLevel::Error,
                         "friend definitions inside the class are not supported yet",
                         current_loc());
                skip_balanced_until_semicolon_or_brace();
                has_error = true;
            } else if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after friend declaration",
                         current_loc());
                skip_until_statement_boundary();
                has_error = true;
            }
            children.push_back(make_node(NodeKind::FunctionDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         std::move(member_children),
                                         text_payload(declarator.name),
                                         has_error ? NodeFlagHasError
                                                   : NodeFlagNone));
            return true;
        };

        auto parse_conversion_member = [&](size_t member_begin,
                                           bool leading_virtual,
                                           const LayoutAttrs& leading_attrs) -> bool {
            size_t lookahead = skip_cxx_special_member_prefix(0);
            size_t conversion_parentheses = 0;
            while (peek(lookahead).type == TokenType::LEFT_PAREN) {
                ++conversion_parentheses;
                ++lookahead;
            }
            if (peek(lookahead).type != TokenType::OPERATOR_KW) {
                return false;
            }

            ParsedSpecialMemberPrefix prefix =
                parse_special_member_prefix(leading_attrs);
            collect::DeclFlags& flags = prefix.flags;
            ParsedExplicitSpecifier& explicit_specifier =
                prefix.explicit_specifier;
            bool declaration_has_error = prefix.has_error;

            for (size_t index = 0; index < conversion_parentheses; ++index) {
                consume();
            }
            size_t name_begin = current_raw_index();
            Token operator_token = current();
            consume();
            auto [conversion_type, conversion_syntax] =
                parse_record_conversion_type_id();
            cir::TypeId resolved_conversion_type =
                collect_session_.file().resolved_type(conversion_type.type);
            if (collect_session_.file().valid(resolved_conversion_type)) {
                cir::TypeKind conversion_kind =
                    collect_session_.file().type(resolved_conversion_type).kind;
                declaration_has_error = declaration_has_error ||
                    conversion_kind == cir::TypeKind::Function ||
                    conversion_kind == cir::TypeKind::Array;
            }
            std::string member_name = "operator " +
                collect_session_.file().format_type(conversion_type);
            std::vector<NodeId> member_children = prefix.attrs.syntax;
            if (conversion_syntax != InvalidNodeId) {
                member_children.push_back(conversion_syntax);
            }
            member_children.push_back(make_node(NodeKind::Name,
                                                name_begin,
                                                last_consumed_raw_end(),
                                                {},
                                                text_payload(member_name)));

            for (size_t index = 0; index < conversion_parentheses; ++index) {
                if (!match(TokenType::RIGHT_PAREN)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ')' around conversion-function-id",
                             current_loc());
                    declaration_has_error = true;
                    break;
                }
            }

            if (prefix.invalid_static) {
                diagnose(DiagnosticLevel::Error,
                         "conversion function must be a non-static member function",
                         operator_token.loc);
                declaration_has_error = true;
            }

            if (!match(TokenType::LEFT_PAREN)) {
                diagnose(DiagnosticLevel::Error,
                         "expected parameter list in conversion function declaration",
                         current_loc());
                skip_until_statement_boundary();
                return true;
            }
            bool is_variadic = false;
            std::vector<ParsedParam> params = parse_parameter_list(
                false,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberParameter),
                &is_variadic);
            std::vector<cir::TypeRef> param_types;
            param_types.reserve(params.size());
            for (const ParsedParam& param : params) {
                if (param.syntax != InvalidNodeId) {
                    member_children.push_back(param.syntax);
                }
                if (param.is_parameter_pack_expansion_sentinel) {
                    continue;
                }
                param_types.push_back(param.type_ref);
            }
            if (!param_types.empty() || is_variadic) {
                diagnose(DiagnosticLevel::Error,
                         "conversion function cannot have parameters",
                         operator_token.loc);
                declaration_has_error = true;
            }

            bool member_is_const = false;
            bool member_is_volatile = false;
            cir::FunctionRefQualifierKind member_ref_qualifier =
                cir::FunctionRefQualifierKind::None;
            while (true) {
                if (match(TokenType::CONST)) {
                    member_is_const = true;
                } else if (match(TokenType::VOLATILE)) {
                    member_is_volatile = true;
                } else if (match(TokenType::BITWISE_AND)) {
                    member_ref_qualifier =
                        cir::FunctionRefQualifierKind::LValue;
                } else if (match(TokenType::LOGICAL_AND)) {
                    member_ref_qualifier =
                        cir::FunctionRefQualifierKind::RValue;
                } else {
                    break;
                }
            }

            ParsedRecordExceptionSpec exception_spec =
                parse_special_member_exception_spec(member_children);
            if (match(TokenType::ARROW)) {
                SrcLoc arrow_loc = last_consumed_loc();
                DeclarationParser trailing_type_parser(
                    *this,
                    TypeParseContext::type_only(
                        TypeParseContext::Origin::TrailingReturnType));
                (void)trailing_type_parser.parse_declaration(false, true);
                if (trailing_type_parser.type_syntax != InvalidNodeId) {
                    member_children.push_back(trailing_type_parser.type_syntax);
                }
                diagnose(DiagnosticLevel::Error,
                         "conversion function cannot use a trailing return type",
                         arrow_loc);
                declaration_has_error = true;
            }

            cir::TypeId function_type =
                collect_session_.function_type(conversion_type,
                                               param_types,
                                               false,
                                               true,
                                               member_is_const,
                                               std::move(exception_spec.spec),
                                               {},
                                               member_ref_qualifier,
                                               member_is_volatile);
            collect::RecordMethodInput method;
            method.name = member_name;
            method.type = function_type;
            method.operator_function.kind =
                cir::OperatorFunctionKind::Conversion;
            method.operator_function.conversion_type = conversion_type;
            method.params = param_inputs_from_parsed_params(
                params,
                /*move_runtime_fragments=*/false);
            method.loc = operator_token.loc;
            method.declared_access = current_access;
            method.flags = flags;
            method.attrs = prefix.attrs.attrs;
            method.is_virtual = leading_virtual;
            method.has_explicit_exception_spec =
                exception_spec.has_explicit;
            method.has_deferred_noexcept_operand = exception_spec.deferred;
            method.noexcept_operand_begin = exception_spec.operand_begin;
            method.noexcept_operand_end = exception_spec.operand_end;
            method.noexcept_operand_loc = exception_spec.operand_loc;
            method.noexcept_declaration_context =
                exception_spec.declaration_context;
            method.noexcept_lookup_generation =
                exception_spec.lookup_generation;
            method.is_explicit = prefix.is_explicit();
            method.is_conversion_function = true;
            method.explicit_specifier = explicit_specifier.kind;
            method.explicit_expression_begin =
                explicit_specifier.expression_begin;
            method.explicit_expression_end = explicit_specifier.expression_end;
            method.explicit_value_expression =
                explicit_specifier.value_expression;
            method.explicit_declaration_context =
                explicit_specifier.declaration_context;
            method.explicit_lookup_generation =
                explicit_specifier.lookup_generation;
            size_t method_index = methods.size();
            if (match(TokenType::REQUIRES_KW)) {
                SrcLoc requires_loc = last_consumed_loc();
                size_t constraint_begin = 0;
                size_t constraint_end = 0;
                std::optional<bool> constraint_value;
                collect::Session::NormalizedConstraint normal_form;
                bool valid = parse_and_validate_constraint_expression(
                    requires_loc,
                    constraint_begin,
                    constraint_end,
                    &constraint_value,
                    &normal_form);
                if (leading_virtual) {
                    diagnose(DiagnosticLevel::Error,
                             "a virtual function cannot have an associated requires-clause",
                             requires_loc);
                }
                if (valid) {
                    retain_method_constraint(method_index,
                                             method,
                                             constraint_begin,
                                             constraint_end,
                                             std::move(normal_form),
                                             constraint_value);
                } else {
                    method.constraint_satisfaction =
                        cir::ConstraintSatisfactionKind::Invalid;
                }
            }
            bool parsed_body = parse_member_function_tail(method,
                                                          member_children,
                                                          false,
                                                          std::move(params),
                                                          false);
            method.has_deferred_definition = parsed_body;
            collect_session_.declare_record_method_shell(record.entity,
                                                         method);
            methods.push_back(std::move(method));

            children.push_back(make_node(NodeKind::FunctionDecl,
                                         member_begin,
                                         last_consumed_raw_end(),
                                         member_children,
                                         text_payload(member_name),
                                         declaration_has_error
                                             ? NodeFlagHasError
                                             : NodeFlagNone));

            if (!parsed_body && !match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after conversion function declaration",
                         current_loc());
                skip_until_statement_boundary();
            }
            return true;
        };

        while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
            collect_session_.set_current_record_member_access(current_access);
            size_t member_begin = current_raw_index();
            if (match(TokenType::SEMICOLON)) {
                continue;
            }

            if (check(TokenType::STATIC_ASSERT)) {
                ParsedDecl assert_decl = parse_static_assert_declaration();
                if (assert_decl.syntax != InvalidNodeId) {
                    children.push_back(assert_decl.syntax);
                }
                continue;
            }

            if (std::optional<ParsedDecl> deduction_guide =
                    try_parse_cxx_deduction_guide_declaration(
                        nullptr, SrcLoc{}, member_begin)) {
                if (deduction_guide->syntax != InvalidNodeId) {
                    children.push_back(deduction_guide->syntax);
                }
                continue;
            }

            bool leading_virtual = match(TokenType::VIRTUAL_KW);
            if (is_cxx_access_specifier(current().type) &&
                peek(1).type == TokenType::COLON) {
                if (leading_virtual) {
                    diagnose(DiagnosticLevel::Error,
                             "expected member declaration after 'virtual'",
                             current_loc());
                }
                Token access_token = current();
                current_access = access_from_token(access_token.type);
                collect_session_.set_current_record_member_access(
                    current_access);
                consume();
                consume();
                children.push_back(make_node(NodeKind::AmbiguousSyntax,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {},
                                             text_payload(std::string(access_token.value) + ":")));
                continue;
            }

            if (check(TokenType::USING)) {
                if (leading_virtual) {
                    diagnose(DiagnosticLevel::Error,
                             "expected member declaration after 'virtual'",
                             current_loc());
                }
                ParsedDecl using_decl = parse_cxx_using_declaration();
                if (using_decl.syntax != InvalidNodeId) {
                    children.push_back(using_decl.syntax);
                }
                continue;
            }

            if (check(TokenType::TEMPLATE)) {
                if (leading_virtual) {
                    diagnose(DiagnosticLevel::Error,
                             "expected member declaration after 'virtual'",
                             current_loc());
                }
                std::optional<size_t> after_head = template_head_end_offset();
                TokenType after_head_type =
                    after_head.has_value() ? peek(*after_head).type
                                           : TokenType::UNKNOWN;
                FriendTemplateStart friend_template_start =
                    friend_template_start_after_head(after_head);
                TemplatedSpecialMemberKind special_member_kind =
                    after_head.has_value()
                        ? templated_special_member_kind_after_head(*after_head)
                        : TemplatedSpecialMemberKind::None;
                bool starts_special_member_template =
                    special_member_kind != TemplatedSpecialMemberKind::None;
                bool starts_existing_template_declaration =
                    after_head_type == TokenType::STATIC ||
                    after_head_type == TokenType::TEMPLATE ||
                    after_head_type == TokenType::USING ||
                    after_head_type == TokenType::STRUCT ||
                    after_head_type == TokenType::UNION ||
                    after_head_type == TokenType::CLASS ||
                    after_head_type == TokenType::ENUM;
                bool starts_friend_class_template =
                    friend_template_start == FriendTemplateStart::Class;
                std::optional<size_t> after_member_template_head =
                    after_head_type == TokenType::TEMPLATE
                        ? template_head_end_offset_from(*after_head)
                        : std::nullopt;
                bool starts_friend_member_function_template =
                    after_member_template_head.has_value() &&
                    peek(*after_member_template_head).type ==
                        TokenType::FRIEND_KW;
                bool starts_friend_function_template =
                    friend_template_start != FriendTemplateStart::None;
                bool starts_deduction_guide =
                    after_head.has_value() &&
                    template_member_decl_is_deduction_guide(*after_head);
                bool starts_virtual_member_template =
                    after_head.has_value() &&
                    after_head_type == TokenType::VIRTUAL_KW;
                bool starts_friend_template =
                    starts_friend_class_template ||
                    starts_friend_member_function_template ||
                    starts_friend_function_template;
                bool may_have_function_declarator =
                    after_head.has_value() &&
                    template_member_decl_may_have_function_declarator(
                        *after_head);
                bool starts_static_function_template =
                    may_have_function_declarator &&
                    template_member_decl_has_static_specifier(*after_head);
                if (current_record_is_local(collect_session_)) {
                    diagnose(
                        DiagnosticLevel::Error,
                        starts_friend_template
                            ? "a friend template shall not be declared in a local class"
                            : "a local class shall not have member templates",
                        current_loc());
                    skip_balanced_until_semicolon_or_brace();
                    match(TokenType::SEMICOLON);
                    continue;
                }
                if (starts_virtual_member_template) {
                    diagnose(DiagnosticLevel::Error,
                             "a member function template shall not be declared virtual",
                             current_loc());
                    skip_balanced_until_semicolon_or_brace();
                    match(TokenType::SEMICOLON);
                    continue;
                }
                bool use_existing_template_path =
                    !after_head.has_value() ||
                    starts_deduction_guide ||
                    (!starts_special_member_template &&
                     (!may_have_function_declarator ||
                      (starts_existing_template_declaration &&
                       !starts_static_function_template)));
                if (starts_friend_class_template) {
                    parse_friend_class_template_declaration(member_begin);
                } else if (starts_friend_member_function_template) {
                    parse_dependent_member_friend_function_template_declaration(
                        member_begin);
                } else if (starts_friend_function_template) {
                    parse_dependent_member_friend_function_declaration(
                        member_begin);
                } else if (use_existing_template_path) {
                    ParsedDecl templated_decl = parse_cxx_template_declaration();
                    if (templated_decl.syntax != InvalidNodeId) {
                        children.push_back(templated_decl.syntax);
                    }
                } else if (starts_special_member_template) {
                    parse_templated_special_member(member_begin,
                                                   special_member_kind);
                } else {
                    parse_nonstatic_member_function_template(member_begin);
                }
                continue;
            }

            LayoutAttrs leading_member_attrs = parse_layout_attributes();
            if (match(TokenType::VIRTUAL_KW)) {
                if (leading_virtual) {
                    diagnose(DiagnosticLevel::Error,
                             "duplicate 'virtual' specifier",
                             last_consumed_loc());
                }
                leading_virtual = true;

                merge_attrs(leading_member_attrs,
                            parse_layout_attributes());
            }

            if (parse_special_member(member_begin,
                                     leading_virtual,
                                     leading_member_attrs)) {
                continue;
            }

            if (parse_conversion_member(member_begin,
                                        leading_virtual,
                                        leading_member_attrs)) {
                continue;
            }

            if (!is_type_start(current().type) &&
                !(lang_opts_.enable_cpp_reflection &&
                  check(TokenType::SPLICE_OPEN)) &&
                !starts_cxx_qualified_name()) {
                diagnose(DiagnosticLevel::Error, "expected class member declaration", current_loc());
                skip_until_statement_boundary();
                continue;
            }

            bool member_starts_friend = check(TokenType::FRIEND_KW);
            size_t friend_type_replay_cursor = cursor_;
            size_t friend_type_replay_last_consumed_raw_end =
                last_consumed_raw_end_;
            collect::Session::ParameterPackPatternCaptureScope
                friend_type_pack_capture;
            if (member_starts_friend) {
                friend_type_pack_capture =
                    collect_session_
                        .begin_parameter_pack_pattern_capture();
            }
            DeclarationParser member_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberDeclSpecifier));
            member_parser.allow_cxx_member_declarator_ids = true;
            member_parser.allow_friend_type_specifier = member_starts_friend;
            cir::TypeRef member_base_type = member_parser.parse_declaration(false, true);
            NodeId member_type = member_parser.type_syntax;
            std::vector<collect::Session::ParameterPackIdentity>
                friend_type_packs;
            if (member_starts_friend) {
                friend_type_packs =
                    collect_session_
                        .finish_parameter_pack_pattern_capture(
                            friend_type_pack_capture);
            }
            collect::DeclFlags flags = declaration_flags_from_parser(member_parser);
            bool friend_has_storage_class =
                flags.is_friend &&
                (member_parser.storage_class != StorageClass::None ||
                 flags.is_thread_local || flags.is_mutable);
            if (friend_has_storage_class) {
                diagnose(DiagnosticLevel::Error,
                         "a storage-class specifier is not allowed in a friend declaration",
                         loc_for_index(member_begin));
            } else if (flags.is_extern) {
                diagnose(DiagnosticLevel::Error,
                         "a class member cannot be declared 'extern'",
                         loc_for_index(member_begin));
            }
            if (flags.is_thread_local && !flags.is_static) {
                diagnose(DiagnosticLevel::Error,
                         "a thread_local class member must also be static",
                         loc_for_index(member_begin));
            }
            if (leading_virtual && flags.is_static) {
                diagnose(DiagnosticLevel::Error,
                         "'virtual' is not allowed on static member declarations",
                         loc_for_index(member_begin));
            }
            if (flags.is_friend) {
                auto add_class_friend_type = [&](cir::TypeRef type_ref,
                                                 bool pack_expansion = false) {
                    collect_session_.add_pending_class_friend_type(
                        record.entity,
                        type_ref,
                        pack_expansion,
                        loc_for_index(member_begin));
                };
                auto diagnose_unexpanded_friend_type_pack =
                    [&](const std::vector<
                            collect::Session::ParameterPackIdentity>& packs,
                        SrcLoc loc) {
                    if (!packs.empty()) {
                        diagnose(DiagnosticLevel::Error,
                                 "unexpanded template parameter pack '" +
                                     packs.front().name +
                                     "' is not supported yet",
                                 loc);
                    }
                };

                auto process_friend_type_specifier =
                    [&](cir::TypeRef type_ref,
                        const std::vector<
                            collect::Session::ParameterPackIdentity>& packs,
                        size_t replay_cursor,
                        size_t replay_last_consumed_raw_end,
                        size_t replay_end_cursor,
                        bool has_ellipsis,
                        SrcLoc ellipsis_loc,
                        size_t continuation_cursor,
                        size_t continuation_last_consumed_raw_end) {
                    if (!has_ellipsis) {
                        if (!packs.empty()) {
                            diagnose_unexpanded_friend_type_pack(
                                packs,
                                current_loc());
                        } else {
                            add_class_friend_type(type_ref);
                        }
                        return;
                    }
                    std::optional<
                        std::vector<collect::Session::TemplateArgument>>
                        elements =
                            collect_session_.template_type_pack_arguments(
                                type_ref.type);
                    if (!elements.has_value()) {
                        if (!collect_session_.type_contains_type_parameter_pack(
                                type_ref.type)) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "pack expansion pattern does not contain a template parameter pack",
                                ellipsis_loc);
                        } else if (!packs.empty()) {
                            std::optional<size_t> element_count;
                            bool dependent = false;
                            for (const collect::Session::
                                     ParameterPackIdentity& pack : packs) {
                                std::optional<size_t> pack_count =
                                    collect_session_
                                        .parameter_pack_element_count(pack);
                                if (!pack_count.has_value()) {
                                    dependent = true;
                                    break;
                                }
                                if (element_count.has_value() &&
                                    *element_count != *pack_count) {
                                    diagnose(
                                        DiagnosticLevel::Error,
                                        "pack expansion contains packs with different lengths",
                                        ellipsis_loc);
                                    *element_count = std::min(
                                        *element_count,
                                        *pack_count);
                                } else if (!element_count.has_value()) {
                                    element_count = *pack_count;
                                }
                            }
                            if (!dependent) {
                                size_t count = element_count.value_or(0);
                                for (size_t i = 0; i < count; ++i) {
                                    cursor_ = replay_cursor;
                                    last_consumed_raw_end_ =
                                        replay_last_consumed_raw_end;
                                    auto replay_scope =
                                        collect_session_
                                            .begin_parameter_pack_element_replay(
                                                packs,
                                                i);
                                    DeclarationParser replay_parser(
                                        *this,
                                        TypeParseContext::type_only(
                                            TypeParseContext::Origin::FriendTypeSpecifier));
                                    replay_parser
                                        .allow_cxx_member_declarator_ids =
                                        true;
                                    replay_parser
                                        .allow_friend_type_specifier = true;
                                    cir::TypeRef replay_type =
                                        replay_parser.parse_declaration(false,
                                                                        true);
                                    collect_session_
                                        .finish_parameter_pack_element_replay(
                                            replay_scope);
                                    if (cursor_ != replay_end_cursor) {
                                        diagnose(
                                            DiagnosticLevel::Error,
                                            "could not replay friend type pack expansion pattern",
                                            ellipsis_loc);
                                        cursor_ = replay_end_cursor;
                                    }
                                    add_class_friend_type(replay_type);
                                }
                            } else {
                                add_class_friend_type(type_ref, true);
                            }
                        }
                    } else {
                        for (const collect::Session::TemplateArgument& element :
                             *elements) {
                            if (element.kind ==
                                cir::TemplateArgumentKind::Type) {
                                add_class_friend_type(element.type);
                            }
                        }
                    }
                    cursor_ = continuation_cursor;
                    last_consumed_raw_end_ =
                        continuation_last_consumed_raw_end;
                };
                if (check(TokenType::ELLIPSIS) ||
                    check(TokenType::COMMA) ||
                    check(TokenType::SEMICOLON)) {
                    std::vector<NodeId> friend_type_nodes;
                    friend_type_nodes.push_back(member_type);
                    size_t friend_type_replay_end_cursor = cursor_;
                    bool first_has_ellipsis = false;
                    SrcLoc first_ellipsis_loc{};
                    if (check(TokenType::ELLIPSIS)) {
                        first_has_ellipsis = true;
                        first_ellipsis_loc = current_loc();
                        consume();
                    }
                    process_friend_type_specifier(
                        member_base_type,
                        friend_type_packs,
                        friend_type_replay_cursor,
                        friend_type_replay_last_consumed_raw_end,
                        friend_type_replay_end_cursor,
                        first_has_ellipsis,
                        first_ellipsis_loc,
                        cursor_,
                        last_consumed_raw_end_);
                    while (match(TokenType::COMMA)) {
                        size_t list_item_replay_cursor = cursor_;
                        size_t list_item_replay_last_consumed_raw_end =
                            last_consumed_raw_end_;
                        auto list_item_capture =
                            collect_session_
                                .begin_parameter_pack_pattern_capture();
                        DeclarationParser list_item_parser(
                            *this,
                            TypeParseContext::type_only(
                                TypeParseContext::Origin::FriendTypeSpecifier));
                        list_item_parser.allow_cxx_member_declarator_ids =
                            true;
                        list_item_parser.allow_friend_type_specifier = true;
                        cir::TypeRef list_item_type =
                            list_item_parser.parse_declaration(false, true);
                        if (list_item_parser.type_syntax != InvalidNodeId) {
                            friend_type_nodes.push_back(
                                list_item_parser.type_syntax);
                        }
                        std::vector<
                            collect::Session::ParameterPackIdentity>
                            list_item_packs =
                            collect_session_
                                .finish_parameter_pack_pattern_capture(
                                    list_item_capture);
                        size_t list_item_replay_end_cursor = cursor_;
                        bool list_item_has_ellipsis = false;
                        SrcLoc list_item_ellipsis_loc{};
                        if (check(TokenType::ELLIPSIS)) {
                            list_item_has_ellipsis = true;
                            list_item_ellipsis_loc = current_loc();
                            consume();
                        }
                        process_friend_type_specifier(
                            list_item_type,
                            list_item_packs,
                            list_item_replay_cursor,
                            list_item_replay_last_consumed_raw_end,
                            list_item_replay_end_cursor,
                            list_item_has_ellipsis,
                            list_item_ellipsis_loc,
                            cursor_,
                            last_consumed_raw_end_);
                    }
                    if (!match(TokenType::SEMICOLON)) {
                        diagnose(DiagnosticLevel::Error,
                                 "expected ';' after friend declaration",
                                 current_loc());
                    }
                    children.push_back(make_node(NodeKind::RecordDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 std::move(friend_type_nodes)));
                    continue;
                }

                member_parser.reset_declarator_parsing_state();
                member_parser.allow_cxx_member_declarator_ids = true;
                ParsedDeclarator friend_declarator =
                    member_parser.parse_declarator(member_base_type, true);
                auto friend_context_for =
                    [&](const ParsedDeclarator& declarator) {
                    cir::DeclContextId friend_context =
                        declarator.qualified_context;
                    if (friend_context.valid()) {
                        return friend_context;
                    }
                    const cir::File& file = collect_session_.file();
                    if (current_record_is_local(collect_session_)) {
                        for (cir::DeclContextId context =
                                 collect_session_.current_decl_context();
                             context.valid();
                             context = file.decl_context(context).parent) {
                            cir::DeclContextKind kind =
                                file.decl_context(context).kind;
                            if (kind == cir::DeclContextKind::Block ||
                                kind == cir::DeclContextKind::Function) {
                                return context;
                            }
                        }
                        return cir::DeclContextId{};
                    }
                    for (cir::DeclContextId context =
                             collect_session_.current_decl_context();
                         context.valid();
                         context = file.decl_context(context).parent) {
                        cir::DeclContextKind kind =
                            file.decl_context(context).kind;
                        if (kind == cir::DeclContextKind::Namespace ||
                            kind == cir::DeclContextKind::TranslationUnit) {
                            return context;
                        }
                    }
                    return cir::DeclContextId{};
                };
                auto explicit_template_id_is_followed_by_parameter_list =
                    [&]() {
                    if (!check(TokenType::LESS_THAN)) {
                        return false;
                    }
                    int angle_depth = 0;
                    size_t offset = 0;
                    while (true) {
                        TokenType type = peek(offset).type;
                        if (type == TokenType::Eof ||
                            type == TokenType::SEMICOLON ||
                            type == TokenType::LEFT_BRACE) {
                            return false;
                        }
                        if (type == TokenType::LESS_THAN) {
                            ++angle_depth;
                        } else if (type == TokenType::GREATER_THAN) {
                            --angle_depth;
                            if (angle_depth == 0) {
                                return peek(offset + 1).type ==
                                    TokenType::LEFT_PAREN;
                            }
                        } else if (type == TokenType::RIGHT_SHIFT) {
                            if (angle_depth <= 2) {
                                return peek(offset + 1).type ==
                                    TokenType::LEFT_PAREN;
                            }
                            angle_depth -= 2;
                        }
                        ++offset;
                    }
                };
                bool has_explicit_template_arguments = false;
                bool explicit_template_id_has_written_arguments = false;
                bool explicit_template_id_error = false;
                std::vector<collect::Session::TemplateArgument>
                    explicit_template_arguments;
                std::vector<collect::CandidateExplicitTemplateArguments>
                    candidate_explicit_template_arguments;
                std::vector<const collect::Session::TemplateInfo*>
                    explicit_template_candidates;
                cir::DeclContextId friend_context =
                    friend_context_for(friend_declarator);
                if (friend_declarator.has_name &&
                    check(TokenType::LESS_THAN)) {
                    has_explicit_template_arguments = true;
                    explicit_template_id_has_written_arguments =
                        peek(1).type != TokenType::GREATER_THAN;
                    explicit_template_candidates =
                        collect_session_.function_template_infos_for_name(
                            friend_context,
                            friend_declarator.name,
                            !friend_declarator.qualified_context.valid());
                    if (!explicit_template_id_is_followed_by_parameter_list()) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "function template friend specialization must have a function parameter list",
                            current_loc());
                        explicit_template_id_error = true;
                    } else {
                        bool parsed_arguments = false;
                        if (!explicit_template_candidates.empty()) {
                            parsed_arguments =
                                parse_function_template_argument_list_for_candidates(
                                    *explicit_template_candidates.front(),
                                    explicit_template_candidates,
                                    explicit_template_arguments,
                                    candidate_explicit_template_arguments,
                                    friend_declarator.loc);
                        } else {
                            parsed_arguments =
                                parse_dependent_expression_template_argument_list(
                                    friend_declarator.loc);
                        }
                        if (!parsed_arguments) {
                            explicit_template_id_error = true;
                        } else {
                            ParsedDeclarator suffix =
                                member_parser.parse_declarator(
                                    friend_declarator.type_ref,
                                    true,
                                    &friend_declarator);
                            friend_declarator.type = suffix.type;
                            friend_declarator.type_ref = suffix.type_ref;
                            friend_declarator.is_function =
                                suffix.is_function;
                            friend_declarator.is_variadic =
                                suffix.is_variadic;
                            friend_declarator.has_prototype =
                                suffix.has_prototype;
                            friend_declarator.is_kr_style =
                                suffix.is_kr_style;
                            friend_declarator.has_trailing_return_type =
                                suffix.has_trailing_return_type;
                            friend_declarator.has_unsupported_semantics =
                                friend_declarator
                                    .has_unsupported_semantics ||
                                suffix.has_unsupported_semantics;
                            friend_declarator.kr_param_names =
                                std::move(suffix.kr_param_names);
                            friend_declarator.params =
                                std::move(suffix.params);
                            friend_declarator.vla_bounds =
                                collect_session_.chain(
                                    std::move(friend_declarator.vla_bounds),
                                    std::move(suffix.vla_bounds),
                                    friend_declarator.loc);
                            friend_declarator.attrs.append(
                                std::move(suffix.attrs));
                        }
                    }
                }
                if (friend_declarator.is_function &&
                    friend_declarator.has_name &&
                    friend_declarator.name == "operator==") {
                    has_friend_equality_declaration = true;
                }
                bool friend_defaulted =
                    check(TokenType::ASSIGN) &&
                    peek(1).type == TokenType::DEFAULT;
                bool friend_definition =
                    check(TokenType::LEFT_BRACE) || friend_defaulted;
                bool invalid_constrained_friend_declaration =
                    friend_declarator.is_function &&
                    friend_declarator.has_name &&
                    friend_declarator.has_trailing_requires_clause &&
                    !friend_declarator.abbreviated_template_info.has_value() &&
                    !has_explicit_template_arguments &&
                    !friend_definition;
                bool invalid_enclosing_constrained_friend_template_declaration =
                    false;
                if (!friend_definition &&
                    friend_declarator.abbreviated_template_info.has_value()) {
                    collect::Session::TemplateInfo constraint_probe =
                        *friend_declarator.abbreviated_template_info;
                    constraint_probe.name = friend_declarator.name;
                    constraint_probe.operator_function =
                        friend_declarator.operator_function;
                    constraint_probe.pattern_type = friend_declarator.type;
                    record_trailing_function_requires_clause(
                        constraint_probe, friend_declarator);
                    invalid_enclosing_constrained_friend_template_declaration =
                        constraint_references_parameter_outside_head(
                            constraint_probe);
                    if (invalid_enclosing_constrained_friend_template_declaration) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "a friend function template declaration whose constraint depends on an enclosing template parameter shall be a definition",
                            friend_declarator.trailing_requires_loc.isInvalid()
                                ? friend_declarator.loc
                                : friend_declarator.trailing_requires_loc);
                    }
                }
                if (invalid_constrained_friend_declaration) {
                    diagnose(
                        DiagnosticLevel::Error,
                        "a non-template friend declaration with a requires-clause shall be a definition",
                        friend_declarator.trailing_requires_loc);
                }
                if (friend_declarator.is_function &&
                    friend_declarator.has_name) {
                    if (!friend_definition) {
                        const cir::File& file = collect_session_.file();
                        bool defer_template_pattern_grant =
                            file.valid(record.entity) &&
                            file.entity(record.entity).is_template_pattern;
                        if (has_explicit_template_arguments) {
                            bool has_error = explicit_template_id_error;
                            for (const ParsedParam& param :
                                 friend_declarator.params) {
                                if (param.has_default_argument) {
                                    diagnose(
                                        DiagnosticLevel::Error,
                                        "default arguments are not allowed in friend declarations naming function template specializations",
                                        param.default_argument_loc);
                                    has_error = true;
                                }
                            }

                            if (explicit_template_id_has_written_arguments &&
                                (flags.is_inline || flags.is_constexpr ||
                                 flags.is_consteval)) {
                                diagnose(
                                    DiagnosticLevel::Error,
                                    "inline, constexpr, and consteval are not allowed in friend declarations naming function template specializations",
                                    friend_declarator.loc);
                                has_error = true;
                            }

                            struct Match {
                                const collect::Session::TemplateInfo* info =
                                    nullptr;
                                std::vector<
                                    collect::Session::TemplateArgument>
                                    arguments;
                            };
                            std::vector<Match> matches;
                            if (!has_error && !defer_template_pattern_grant) {
                                std::vector<std::string> seen_match_keys;
                                for (const collect::Session::TemplateInfo*
                                         candidate :
                                     explicit_template_candidates) {
                                    const std::vector<
                                        collect::Session::TemplateArgument>*
                                        candidate_arguments =
                                            &explicit_template_arguments;
                                    auto replayed = std::find_if(
                                        candidate_explicit_template_arguments
                                            .begin(),
                                        candidate_explicit_template_arguments
                                            .end(),
                                        [&](const collect::
                                                CandidateExplicitTemplateArguments&
                                                entry) {
                                            return entry.template_entity ==
                                                candidate->entity;
                                        });
                                    if (replayed !=
                                        candidate_explicit_template_arguments
                                            .end()) {
                                        if (!replayed->viable) {
                                            continue;
                                        }
                                        candidate_arguments =
                                            &replayed->arguments;
                                    }
                                    std::vector<
                                        collect::Session::TemplateArgument>
                                        deduced;
                                    collect::Session::
                                        PatternInstantiationCallbacks
                                            callbacks;
                                    configure_pattern_instantiation_callbacks(
                                        callbacks,
                                        friend_declarator.loc);
                                    if (deduce_function_template_declaration_match(
                                            *candidate,
                                            friend_declarator.type,
                                            deduced,
                                            candidate_arguments,
                                            callbacks,
                                            friend_declarator.loc)) {
                                        std::string match_key =
                                            collect_session_.template_memo_key(
                                                candidate->entity,
                                                deduced);
                                        if (std::find(
                                                seen_match_keys.begin(),
                                                seen_match_keys.end(),
                                                match_key) !=
                                            seen_match_keys.end()) {
                                            continue;
                                        }
                                        seen_match_keys.push_back(
                                            std::move(match_key));
                                        matches.push_back(
                                            Match{candidate,
                                                  std::move(deduced)});
                                    }
                                }
                                if (matches.empty()) {
                                    diagnose(
                                        DiagnosticLevel::Error,
                                        "no matching function template specialization for friend declaration",
                                        friend_declarator.loc);
                                    has_error = true;
                                }
                            }
                            auto more_specialized =
                                [&](const Match& lhs, const Match& rhs) {
                                if (!lhs.info || !rhs.info) {
                                    return false;
                                }
                                return collect_session_
                                    .function_template_more_specialized(
                                        *lhs.info,
                                        *rhs.info,
                                        collect::Session::
                                            FunctionTemplateOrderingContext::
                                                declaration());
                            };
                            auto diagnose_ambiguous_match_notes =
                                [&](const Match& lhs, const Match& rhs) {
                                auto note_candidate = [&](const Match& match) {
                                    if (match.info &&
                                        match.info->entity.valid() &&
                                        collect_session_.file().valid(
                                            match.info->entity)) {
                                        diagnose(
                                            DiagnosticLevel::Note,
                                            "candidate function template declared here",
                                            collect_session_.file()
                                                .entity(match.info->entity)
                                                .loc);
                                    }
                                };
                                note_candidate(lhs);
                                note_candidate(rhs);
                                if (lhs.info && rhs.info &&
                                    collect_session_
                                        .function_template_unordered_constraints_tie(
                                            *lhs.info,
                                            *rhs.info,
                                            collect::Session::
                                                FunctionTemplateOrderingContext::
                                                    declaration())) {
                                    diagnose(
                                        DiagnosticLevel::Note,
                                        "candidate associated constraints are not ordered by subsumption",
                                        friend_declarator.loc);
                                }
                            };
                            if (!has_error && !defer_template_pattern_grant) {
                                size_t best = 0;
                                for (size_t i = 1; i < matches.size(); ++i) {
                                    if (more_specialized(matches[i],
                                                         matches[best])) {
                                        best = i;
                                    }
                                }
                                size_t ambiguous_index = matches.size();
                                for (size_t i = 0; i < matches.size(); ++i) {
                                    if (i != best &&
                                        !more_specialized(matches[best],
                                                          matches[i])) {
                                        ambiguous_index = i;
                                        break;
                                    }
                                }
                                if (ambiguous_index != matches.size()) {
                                    diagnose(
                                        DiagnosticLevel::Error,
                                        "ambiguous function template specialization friend declaration",
                                        friend_declarator.loc);
                                    diagnose_ambiguous_match_notes(
                                        matches[best],
                                        matches[ambiguous_index]);
                                    has_error = true;
                                } else if (!defer_template_pattern_grant) {
                                    const Match& selected = matches[best];
                                    collect_session_
                                        .add_pending_friend_function_template_specialization(
                                            record.entity,
                                            selected.info->entity,
                                            selected.arguments,
                                            friend_declarator.type);
                                }
                            }
                        } else if (!defer_template_pattern_grant &&
                                   !invalid_constrained_friend_declaration &&
                                   !invalid_enclosing_constrained_friend_template_declaration) {
                            if (friend_declarator
                                    .abbreviated_template_info.has_value()) {
                                collect::Session::TemplateInfo hidden_info =
                                    std::move(*friend_declarator
                                                   .abbreviated_template_info);
                                hidden_info.name = friend_declarator.name;
                                hidden_info.operator_function =
                                    friend_declarator.operator_function;
                                hidden_info.pattern_type =
                                    friend_declarator.type;
                                record_trailing_function_requires_clause(
                                    hidden_info, friend_declarator);
                                hidden_info.lexical_context = friend_context;
                                std::vector<collect::ParamInput> hidden_params =
                                    param_inputs_from_parsed_params(
                                        friend_declarator.params,
                                        /*move_runtime_fragments=*/false);
                                cir::EntityId hidden = collect_session_
                                    .declare_hidden_friend_function_template(
                                        std::move(hidden_info),
                                        friend_context,
                                        friend_declarator.loc,
                                        &hidden_params,
                                        record.entity);
                                if (hidden.valid()) {
                                    collect_session_
                                        .add_pending_friend_function_template(
                                            record.entity, hidden);
                                }
                            } else {
                                collect_session_.add_pending_friend_function(
                                    record.entity,
                                    friend_declarator.name,
                                    friend_declarator.type,
                                    friend_context,
                                    friend_declarator.loc,
                                    {},
                                    current_record_is_local(
                                        collect_session_),
                                    friend_declarator.operator_function);
                            }
                        }
                    }
                } else {
                    diagnose(DiagnosticLevel::Error,
                             "unsupported friend declaration",
                             loc_for_index(member_begin));
                }
                if (friend_definition) {
                    if (friend_defaulted) {
                        bool valid_comparison =
                            friend_declarator.name == "operator==" ||
                            friend_declarator.name == "operator!=" ||
                            friend_declarator.name == "operator<" ||
                            friend_declarator.name == "operator<=" ||
                            friend_declarator.name == "operator>" ||
                            friend_declarator.name == "operator>=" ||
                            friend_declarator.name == "operator<=>";
                        if (!friend_declarator.is_function ||
                            !friend_declarator.has_name ||
                            friend_declarator.qualified_context.valid() ||
                            has_explicit_template_arguments ||
                            !valid_comparison) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "only an unqualified comparison operator may be explicitly defaulted as a friend",
                                friend_declarator.loc);
                        } else {
                            cir::EntityId hidden = collect_session_
                                .add_pending_friend_function(
                                    record.entity,
                                    friend_declarator.name,
                                    friend_declarator.type,
                                    friend_context,
                                    friend_declarator.loc,
                                    {},
                                    /*require_existing=*/false,
                                    friend_declarator.operator_function);
                            if (hidden.valid()) {
                                const auto* payload = std::get_if<
                                    cir::FunctionTypePayload>(
                                    &collect_session_.file().type_payload(
                                        collect_session_.file().resolved_type(
                                            friend_declarator.type)));
                                PendingHiddenFriendBody pending;
                                pending.entity = hidden;
                                pending.granting_record = record.entity;
                                pending.lexical_context =
                                    collect_session_.current_decl_context();
                                pending.name = friend_declarator.name;
                                pending.function_type =
                                    friend_declarator.type;
                                pending.result_type = payload
                                    ? payload->return_type
                                    : collect_session_.type_ref(
                                          collect_session_.file()
                                              .unknown_type());
                                pending.params =
                                    param_inputs_from_parsed_params(
                                        friend_declarator.params,
                                        /*move_runtime_fragments=*/false);
                                pending.flags = flags;
                                pending.loc = friend_declarator.loc;
                                pending.is_defaulted_comparison = true;
                                pending.has_explicit_exception_spec =
                                    friend_declarator.has_noexcept_specifier;
                                uint64_t key = static_cast<uint64_t>(
                                    record.entity.index);
                                pending_hidden_friend_bodies_[key].push_back(
                                    std::move(pending));
                                collect_session_.track_speculative_rollback(
                                    [this, key] {
                                        auto found =
                                            pending_hidden_friend_bodies_.find(
                                                key);
                                        if (found ==
                                            pending_hidden_friend_bodies_.end()) {
                                            return;
                                        }
                                        if (!found->second.empty()) {
                                            found->second.pop_back();
                                        }
                                        if (found->second.empty()) {
                                            pending_hidden_friend_bodies_.erase(
                                                found);
                                        }
                                    });
                            }
                        }
                        consume();
                        consume();
                        if (!match(TokenType::SEMICOLON)) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "expected ';' after defaulted friend comparison",
                                current_loc());
                        }
                        children.push_back(make_node(
                            NodeKind::FunctionDecl, member_begin,
                            last_consumed_raw_end(), {member_type},
                            text_payload(friend_declarator.name)));
                        continue;
                    }

                    if (current_record_is_local(collect_session_)) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "a friend function cannot be defined in a local class",
                            friend_declarator.loc);
                        skip_balanced_until_semicolon_or_brace();
                        continue;
                    }
                    if (!friend_declarator.is_function ||
                        !friend_declarator.has_name ||
                        has_explicit_template_arguments ||
                        friend_declarator.qualified_context.valid()) {
                        diagnose(
                            DiagnosticLevel::Error,
                            friend_declarator.qualified_context.valid()
                                ? "a friend function definition must have an unqualified name"
                                : "invalid friend function definition",
                            current_loc());
                        skip_until_statement_boundary();
                        continue;
                    }
                    bool record_is_template_pattern =
                        collect_session_.file().valid(record.entity) &&
                        collect_session_.file().entity(record.entity)
                            .is_template_pattern;
                    size_t definition_begin = cursor_;
                    size_t definition_end =
                        skip_balanced_until_semicolon_or_brace();
                    if (record_is_template_pattern &&
                        !friend_declarator.abbreviated_template_info
                             .has_value()) {
                        children.push_back(make_node(
                            NodeKind::FunctionDecl,
                            member_begin,
                            last_consumed_raw_end(),
                            {member_type},
                            text_payload(friend_declarator.name)));
                        continue;
                    }
                    if (!friend_declarator.abbreviated_template_info
                             .has_value()) {
                        cir::EntityId hidden =
                            collect_session_.add_pending_friend_function(
                                record.entity,
                                friend_declarator.name,
                                friend_declarator.type,
                                friend_context,
                                friend_declarator.loc,
                                friend_declarator
                                        .has_trailing_requires_clause
                                    ? record.entity
                                    : cir::EntityId{},
                                /*require_existing=*/false,
                                friend_declarator.operator_function);
                        if (hidden.valid()) {
                            const auto* payload = std::get_if<
                                cir::FunctionTypePayload>(
                                &collect_session_.file().type_payload(
                                    collect_session_.file().resolved_type(
                                        friend_declarator.type)));
                            PendingHiddenFriendBody pending;
                            pending.entity = hidden;
                            pending.granting_record = record.entity;
                            pending.lexical_context =
                                collect_session_.current_decl_context();
                            pending.body_begin = definition_begin;
                            pending.body_end = definition_end;
                            pending.name = friend_declarator.name;
                            pending.function_type = friend_declarator.type;
                            pending.result_type = payload
                                ? payload->return_type
                                : collect_session_.type_ref(
                                      collect_session_.file().unknown_type());
                            pending.params = param_inputs_from_parsed_params(
                                friend_declarator.params,
                                /*move_runtime_fragments=*/false);
                            collect_session_
                                .register_hidden_friend_default_arguments(
                                    hidden,
                                    pending.params,
                                    friend_declarator.loc);

                            for (collect::ParamInput& parameter :
                                 pending.params) {
                                parameter.default_argument.reset();
                            }
                            pending.flags = flags;
                            pending.loc = friend_declarator.loc;
                            uint64_t key =
                                static_cast<uint64_t>(record.entity.index);
                            pending_hidden_friend_bodies_[key].push_back(
                                std::move(pending));
                            collect_session_.track_speculative_rollback(
                                [this, key] {
                                    auto found =
                                        pending_hidden_friend_bodies_.find(key);
                                    if (found ==
                                        pending_hidden_friend_bodies_.end()) {
                                        return;
                                    }
                                    if (!found->second.empty()) {
                                        found->second.pop_back();
                                    }
                                    if (found->second.empty()) {
                                        pending_hidden_friend_bodies_.erase(
                                            found);
                                    }
                                });
                        }
                        children.push_back(make_node(
                            NodeKind::FunctionDecl,
                            member_begin,
                            last_consumed_raw_end(),
                            {member_type},
                            text_payload(friend_declarator.name)));
                        continue;
                    }
                    collect::Session::TemplateInfo hidden_info =
                        friend_declarator.abbreviated_template_info.has_value()
                            ? std::move(
                                  *friend_declarator.abbreviated_template_info)
                            : collect::Session::TemplateInfo{};
                    hidden_info.name = friend_declarator.name;
                    hidden_info.operator_function =
                        friend_declarator.operator_function;
                    hidden_info.pattern_type = friend_declarator.type;
                    record_trailing_function_requires_clause(
                        hidden_info, friend_declarator);
                    bool references_enclosing_parameter =
                        constraint_references_parameter_outside_head(
                            hidden_info);
                    hidden_info.has_definition = true;
                    hidden_info.definition_begin = member_begin + 1;
                    hidden_info.definition_end = definition_end;
                    hidden_info.lexical_context = friend_context;
                    cir::EntityId owner_template{};
                    std::vector<collect::Session::TemplateArgument>
                        owner_arguments;
                    if (collect_session_.template_arguments_for_record(
                            record.entity,
                            &owner_template,
                            &owner_arguments)) {
                        const collect::Session::TemplateInfo* owner_info =
                            collect_session_.template_info(owner_template);
                        if (owner_info && owner_info->is_class_template &&
                            !owner_arguments.empty()) {
                            collect::Session::TemplateArgumentBindings
                                owner_bindings;
                            if (collect_session_
                                    .bind_template_arguments_to_parameters(
                                        owner_info->parameters,
                                        owner_arguments,
                                        owner_bindings)) {
                                hidden_info.enclosing_instantiation_bindings
                                    .push_back(
                                        {owner_info->parameters,
                                         std::move(owner_bindings)});
                            }
                        }
                    }
                    std::vector<collect::ParamInput> hidden_params =
                        param_inputs_from_parsed_params(
                            friend_declarator.params,
                            /*move_runtime_fragments=*/false);
                    cir::EntityId hidden =
                        collect_session_
                            .declare_hidden_friend_function_template(
                                std::move(hidden_info),
                                friend_context,
                                friend_declarator.loc,
                                &hidden_params,
                                record.entity,
                                references_enclosing_parameter
                                    ? record.entity
                                    : cir::EntityId{});
                    if (hidden.valid()) {
                        collect_session_.add_pending_friend_function_template(
                            record.entity, hidden);
                    } else {
                        diagnose(DiagnosticLevel::Error,
                                 "this friend definition form is not supported yet",
                                 friend_declarator.loc);
                    }
                    children.push_back(make_node(NodeKind::FunctionDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 {member_type},
                                                 text_payload(
                                                     friend_declarator.name)));
                    continue;
                }
                if (!match(TokenType::SEMICOLON)) {
                    diagnose(DiagnosticLevel::Error,
                             "expected ';' after friend declaration",
                             current_loc());
                }
                children.push_back(make_node(NodeKind::RecordDecl,
                                             member_begin,
                                             last_consumed_raw_end(),
                                             {member_type}));
                continue;
            }
            if (check(TokenType::SEMICOLON) &&
                member_base_type.type.valid() &&
                collect_session_.file().valid(member_base_type.type)) {
                cir::TypeId resolved_member_type =
                    collect_session_.file().resolved_type(member_base_type.type);
                cir::TypeKind member_type_kind =
                    collect_session_.file().valid(resolved_member_type)
                        ? collect_session_.file().type(resolved_member_type).kind
                        : cir::TypeKind::Invalid;
                if (member_type_kind == cir::TypeKind::Record ||
                    member_type_kind == cir::TypeKind::Enum) {
                    cir::EntityId member_record =
                        member_type_kind == cir::TypeKind::Record
                            ? collect_session_.file().record_entity(
                                  resolved_member_type)
                            : cir::EntityId{};
                    const cir::RecordFacts* member_facts =
                        member_record.valid()
                            ? collect_session_.file().record_facts(member_record)
                            : nullptr;
                    bool anonymous_record =
                        member_facts &&
                        collect_session_.file().entity(member_record)
                            .is_unnamed_record;
                    bool anonymous_union =
                        anonymous_record &&
                        member_facts->kind == cir::RecordKind::Union;
                    consume();
                    if (anonymous_union) {
                        if (member_parser.storage_class != StorageClass::None ||
                            flags.is_thread_local || flags.is_mutable) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "a class-scope anonymous union cannot have a storage-class specifier",
                                loc_for_index(member_begin));
                        }
                        fields.push_back(
                            collect_session_.declare_anonymous_union_member(
                                resolved_member_type,
                                current_access,
                                loc_for_index(member_begin)));
                    } else if (anonymous_record &&
                               member_facts->kind ==
                                   cir::RecordKind::Struct) {
                        if (member_parser.storage_class != StorageClass::None ||
                            flags.is_thread_local || flags.is_mutable) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "an anonymous struct member cannot have a storage-class specifier",
                                loc_for_index(member_begin));
                        }
                        collect::RecordFieldInput input;
                        input.type = resolved_member_type;
                        input.qualifiers = member_base_type.qualifiers;
                        input.loc = loc_for_index(member_begin);
                        input.declared_access = current_access;
                        fields.push_back(std::move(input));
                    }
                    children.push_back(make_node(NodeKind::RecordDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 {member_type}));
                    continue;
                }
            }

            bool parsed_any_member = false;
            bool parsed_body = false;
            while (!at_end()) {
                member_parser.reset_declarator_parsing_state();
                member_parser.allow_cxx_member_declarator_ids = true;
                ParsedDeclarator declarator = member_parser.parse_declarator(member_base_type, true);
                LayoutAttrs declarator_attrs = parse_layout_attributes();
                std::vector<NodeId> member_children = leading_member_attrs.syntax;
                member_children.push_back(member_type);
                if (declarator.syntax != InvalidNodeId) {
                    member_children.push_back(declarator.syntax);
                }
                member_children.insert(member_children.end(),
                                       declarator_attrs.syntax.begin(),
                                       declarator_attrs.syntax.end());

                if (declarator.is_function) {
                    bool is_abbreviated_template =
                        declarator.abbreviated_template_info.has_value();
                    bool acquired_through_dependent_type =
                        !declarator.has_declarator_operators &&
                        collect_session_
                            .template_instantiation_reclassifies_data_member_as_function(
                                declarator.name,
                                declarator.loc);
                    if (acquired_through_dependent_type) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "function declaration acquired through a dependent type without a function declarator",
                            declarator.loc);
                    }
                    if (flags.is_thread_local) {
                        diagnose(DiagnosticLevel::Error,
                                 "thread_local cannot be applied to a member function",
                                 declarator.loc);
                    }
                    AttributeList member_attrs = leading_member_attrs.attrs;
                    member_attrs.append(member_parser.leading_attrs);
                    member_attrs.append(declarator.attrs);
                    member_attrs.append(declarator_attrs.attrs);
                    collect::DeclFlags method_flags = flags;
                    method_flags.attrs = member_attrs;
                    collect::RecordMethodInput method;
                    method.name = declarator.name;
                    method.type = declarator.type;
                    method.operator_function = declarator.operator_function;
                    method.params = param_inputs_from_parsed_params(
                        declarator.params,
                        /*move_runtime_fragments=*/false);
                    method.loc = declarator.loc.isInvalid()
                        ? loc_for_index(member_begin)
                        : declarator.loc;
                    method.declared_access = current_access;
                    method.flags = method_flags;
                    method.is_static = flags.is_static;
                    method.is_virtual = leading_virtual;
                    method.is_function_template = is_abbreviated_template;
                    method.has_explicit_exception_spec =
                        declarator.has_noexcept_specifier;
                    method.has_deferred_noexcept_operand =
                        declarator.has_deferred_noexcept_operand;
                    method.noexcept_operand_begin =
                        declarator.noexcept_operand_begin;
                    method.noexcept_operand_end =
                        declarator.noexcept_operand_end;
                    method.noexcept_operand_loc =
                        declarator.noexcept_operand_loc;
                    method.noexcept_declaration_context =
                        declarator.noexcept_declaration_context;
                    method.noexcept_lookup_generation =
                        declarator.noexcept_lookup_generation;
                    size_t method_index = methods.size();
                    if (declarator.has_trailing_requires_clause) {
                        if (leading_virtual) {
                            diagnose(DiagnosticLevel::Error,
                                     "a virtual function cannot have an associated requires-clause",
                                     declarator.trailing_requires_loc);
                        }
                        retain_method_constraint(
                            method_index,
                            method,
                            declarator.trailing_requires_constraint_begin,
                            declarator.trailing_requires_constraint_end,
                            declarator.trailing_requires_normal_form,
                            declarator.trailing_requires_value);
                    }
                    bool declared_through_function_type =
                        !declarator.has_declarator_operators;
                    std::optional<PendingMemberBody> pending_template_body;
                    bool abbreviated_has_error = false;
                    if (is_abbreviated_template) {
                        if (!lang_opts_.is_cxx20_or_later()) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "abbreviated function templates require C++20",
                                method.loc);
                            abbreviated_has_error = true;
                        }
                        if (leading_virtual) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "an abbreviated function template cannot be virtual",
                                method.loc);
                            abbreviated_has_error = true;
                        }
                        abbreviated_has_error =
                            parse_member_function_template_tail(
                                method,
                                member_children,
                                member_begin,
                                /*allow_pure_specifier=*/true,
                                /*allow_inline_body=*/true,
                                method_index,
                                std::move(declarator.params),
                                &pending_template_body) ||
                            abbreviated_has_error;
                        if (pending_template_body.has_value() &&
                            declarator.has_placeholder_type_constraint) {
                            pending_template_body
                                ->has_placeholder_return_type_constraint =
                                true;
                            pending_template_body
                                ->placeholder_return_type_constraint_begin =
                                declarator
                                    .placeholder_type_constraint_begin;
                            pending_template_body
                                ->placeholder_return_type_constraint_end =
                                declarator
                                    .placeholder_type_constraint_end;
                            pending_template_body
                                ->placeholder_return_type_constraint_loc =
                                declarator.placeholder_type_constraint_loc;
                        }

                        parsed_body = true;
                    } else {
                        parsed_body = parse_member_function_tail(
                            method,
                            member_children,
                            false,
                            declarator.params,
                            declared_through_function_type);
                        if (parsed_body &&
                            declarator.has_placeholder_type_constraint &&
                            !pending_bodies.empty() &&
                            pending_bodies.back().method_index ==
                                method_index) {
                            PendingMemberBody& pending =
                                pending_bodies.back();
                            pending
                                .has_placeholder_return_type_constraint =
                                true;
                            pending
                                .placeholder_return_type_constraint_begin =
                                declarator
                                    .placeholder_type_constraint_begin;
                            pending
                                .placeholder_return_type_constraint_end =
                                declarator
                                    .placeholder_type_constraint_end;
                            pending
                                .placeholder_return_type_constraint_loc =
                                declarator.placeholder_type_constraint_loc;
                        }
                    }
                    method.has_deferred_definition =
                        is_abbreviated_template
                        ? pending_template_body.has_value()
                        : parsed_body;
                    cir::EntityId method_entity =
                        collect_session_.declare_record_method_shell(
                            record.entity, method);
                    if (!is_abbreviated_template && parsed_body &&
                        !pending_bodies.empty() &&
                        pending_bodies.back().method_index == method_index) {
                        register_deferred_template_member_body(
                            method_entity, pending_bodies.back());
                    }
                    methods.push_back(std::move(method));
                    if (is_abbreviated_template && !abbreviated_has_error) {
                        collect::Session::TemplateInfo info =
                            std::move(*declarator.abbreviated_template_info);
                        info.name = declarator.name;
                        info.operator_function = declarator.operator_function;
                        info.pattern_type = declarator.type;
                        record_trailing_function_requires_clause(
                            info, declarator);
                        info.has_definition =
                            pending_template_body.has_value();
                        PendingMemberTemplate pending;
                        pending.method_index = method_index;
                        pending.info = std::move(info);
                        pending.body = std::move(pending_template_body);
                        pending.loc = method.loc;
                        pending_member_templates.push_back(
                            std::move(pending));
                    }
                    children.push_back(make_node(NodeKind::FunctionDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 member_children,
                                                 text_payload(declarator.name),
                                                 is_abbreviated_template
                                                     ? (abbreviated_has_error
                                                            ? NodeFlagHasError
                                                            : NodeFlagNone)
                                                     : (parsed_body
                                                            ? NodeFlagHasError
                                                            : NodeFlagNone)));
                } else if (member_parser.storage_class == StorageClass::Typedef) {
                    handle_typedef_declarator(declarator);
                    children.push_back(make_node(NodeKind::VarDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 member_children,
                                                 text_payload(declarator.name)));
                } else if (flags.is_static) {
                    if (declarator.name.empty()) {
                        diagnose(DiagnosticLevel::Error,
                                 "static data member declaration requires an identifier",
                                 loc_for_index(member_begin));
                    }
                    collect::DeclFlags static_flags = flags;
                    static_flags.type_qualifiers =
                        declarator.type_ref.qualifiers;
                    collect::RecordStaticDataMemberInput input;
                    input.name = declarator.name;
                    input.type = declarator.type.valid() ? declarator.type : member_base_type.type;
                    input.loc = declarator.loc.isInvalid()
                        ? loc_for_index(member_begin)
                        : declarator.loc;
                    input.attrs = leading_member_attrs.attrs;
                    input.attrs.append(member_parser.leading_attrs);
                    input.attrs.append(declarator.attrs);
                    input.attrs.append(declarator_attrs.attrs);
                    input.declared_access = current_access;
                    input.flags = static_flags;
                    input.initialization_kind =
                        check(TokenType::ASSIGN)
                            ? (peek(1).type == TokenType::LEFT_BRACE
                                   ? collect::ConstructorInitializationKind::
                                         CopyList
                                   : collect::ConstructorInitializationKind::
                                         Copy)
                            : collect::ConstructorInitializationKind::Direct;
                    input.entity =
                        collect_session_.declare_record_static_data_member(input);

                    std::optional<collect::ExprResult> static_initializer;
                    size_t static_initializer_begin = current_raw_index();
                    const collect::Session::TemplateInfo::
                        StaticDataMemberInitializer*
                        retained_initializer =
                            collect_session_
                                .current_instantiation_static_data_member_initializer(
                                    input.name, input.loc);
                    bool can_defer_initializer =
                        retained_initializer != nullptr &&
                        current_raw_index() ==
                            retained_initializer->begin &&
                        retained_initializer->end >
                            retained_initializer->begin &&
                        ((input.flags.type_qualifiers & cir::QualConst) ||
                         input.flags.is_constexpr) &&
                        cir::is_integer_like_type(collect_session_.file(),
                                                  input.type) &&
                        !collect_session_.contains_auto_type(
                            input.type, cir::AutoTypeFlavor::Cxx);
                    if (can_defer_initializer) {
                        input.has_deferred_initializer = true;
                        input.initializer_begin =
                            retained_initializer->begin;
                        input.initializer_end =
                            retained_initializer->end;
                        input.initializer_loc =
                            retained_initializer->loc;
                        input.initializer_context =
                            retained_initializer->declaration_context;
                        input.initializer_lookup_generation =
                            retained_initializer->lookup_generation;

                        input.initializer_value_expression = {};
                        seek_raw_index(retained_initializer->end);
                        member_children.push_back(make_node(
                            NodeKind::InitListExpr,
                            retained_initializer->begin,
                            retained_initializer->end,
                            {}));
                    } else if (match(TokenType::ASSIGN)) {
                        ParsedExpr init = check(TokenType::LEFT_BRACE)
                            ? parse_init_list_expression()
                            : parse_expression(PrecLevel::ASSIGNMENT);
                        static_initializer = init.sem;
                        member_children.push_back(init.syntax);
                    } else if (check(TokenType::LEFT_BRACE)) {
                        ParsedExpr init = parse_init_list_expression();
                        static_initializer = init.sem;
                        member_children.push_back(init.syntax);
                    } else if (check(TokenType::LEFT_PAREN)) {
                        size_t init_begin = current_raw_index();
                        int parens = 0;
                        do {
                            TokenType type = current().type;
                            consume();
                            if (type == TokenType::LEFT_PAREN) ++parens;
                            if (type == TokenType::RIGHT_PAREN) --parens;
                        } while (!at_end() && parens > 0);
                        member_children.push_back(make_node(NodeKind::InitListExpr,
                                                            init_begin,
                                                            last_consumed_raw_end(),
                                                            {},
                                                            {},
                                                            NodeFlagHasError));
                        diagnose(DiagnosticLevel::Error,
                                 "static data member direct initializers are not supported",
                                 loc_for_index(init_begin));
                    }
                    if (static_initializer.has_value()) {
                        input.initializer_begin = static_initializer_begin;
                        input.initializer_end = last_consumed_raw_end();
                        input.initializer_loc =
                            loc_for_index(static_initializer_begin);
                        input.initializer_context =
                            collect_session_.current_decl_context();
                        input.initializer_lookup_generation =
                            collect_session_.lookup_generation();
                        input.initializer_value_expression =
                            static_initializer->template_value_expr;
                        collect_session_.file()
                            .canonicalize_template_value_expression(
                                input.initializer_value_expression);
                        if (static_data_member_initializer_capture_ &&
                            input.initializer_begin < input.initializer_end) {
                            collect::Session::TemplateInfo::
                                StaticDataMemberInitializer retained;
                            retained.name = input.name;
                            retained.begin = input.initializer_begin;
                            retained.end = input.initializer_end;
                            retained.loc = input.loc;
                            retained.declaration_context =
                                input.initializer_context;
                            retained.lookup_generation =
                                input.initializer_lookup_generation;
                            retained.value_expression =
                                input.initializer_value_expression;
                            static_data_member_initializer_capture_->push_back(
                                std::move(retained));
                        }
                    }
                    bool has_cxx_auto =
                        collect_session_.contains_auto_type(
                            input.type, cir::AutoTypeFlavor::Cxx);
                    if (has_cxx_auto && !static_initializer.has_value()) {
                        diagnose(
                            DiagnosticLevel::Error,
                            "declaration with 'auto' type requires an "
                            "initializer",
                            input.loc);
                        input.has_error = true;
                    } else if (has_cxx_auto &&
                               static_initializer->has_error) {

                        input.has_error = true;
                    } else if (has_cxx_auto &&
                               !collect_session_.expr_is_dependent(
                                   *static_initializer)) {
                        cir::TypeId deduced_type =
                            collect_session_.deduce_auto_type(
                                input.type, *static_initializer, input.loc);
                        if (!deduced_type.valid() ||
                            !collect_session_.file().valid(deduced_type) ||
                            collect_session_.contains_auto_type(
                                deduced_type)) {
                            diagnose(
                                DiagnosticLevel::Error,
                                "cannot deduce type for static data member "
                                "with 'auto' type",
                                input.loc);
                            input.has_error = true;
                        } else {
                            input.type = deduced_type;
                            (void)collect_session_
                                .complete_record_static_data_member_type(
                                    input.entity,
                                    input.name,
                                    input.type);
                        }
                    }
                    if (static_initializer.has_value() &&
                        !input.has_error) {
                        collect_session_
                            .register_template_value_parameter_equivalence(
                                input.entity,
                                input.type,
                                *static_initializer);
                        (void)collect_session_
                            .materialize_record_static_data_member_initializer(
                                input.entity,
                                input.type,
                                *static_initializer,
                                input.loc,
                                input.initialization_kind);
                        input.initializer_materialization_attempted = true;
                    }
                    if (input.entity.valid()) {
                        cir::Entity& entity =
                            collect_session_.file().entity_mut(input.entity);
                        entity.has_initializer =
                            static_initializer.has_value() ||
                            input.has_deferred_initializer;
                        entity.initializer_is_value_dependent =
                            static_initializer.has_value() &&
                            collect_session_.expr_is_value_dependent(
                                *static_initializer);
                    }
                    bool static_member_has_error = input.has_error;
                    input.initializer = std::move(static_initializer);
                    collect_session_.stage_record_static_data_member_fact(
                        input);
                    static_data_members.push_back(std::move(input));
                    children.push_back(make_node(NodeKind::VarDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 member_children,
                                                 text_payload(declarator.name),
                                                 static_member_has_error
                                                     ? NodeFlagHasError
                                                     : NodeFlagNone));
                } else {
                    bool is_bitfield = false;
                    uint32_t bit_width = 0;
                    cir::TemplateValueExpression bit_width_expression;
                    bool bit_width_is_dependent = false;
                    LayoutAttrs bitfield_attrs;
                    if (match(TokenType::COLON)) {
                        is_bitfield = true;
                        if (check(TokenType::COMMA) || check(TokenType::SEMICOLON) ||
                            check(TokenType::RIGHT_BRACE)) {
                            diagnose(DiagnosticLevel::Error,
                                     "expected bit-field width",
                                     current_loc());
                        } else {
                            ParsedExpr width = parse_conditional_expression();
                            member_children.push_back(width.syntax);
                            bit_width_expression =
                                width.sem.template_value_expr;
                            collect_session_.file()
                                .canonicalize_template_value_expression(
                                    bit_width_expression);
                            bit_width_is_dependent =
                                collect_session_.expr_is_dependent(width.sem) ||
                                collect_session_.expr_is_value_dependent(
                                    width.sem);
                            if (!bit_width_is_dependent) {
                                int64_t value = 0;
                                if (collect_session_.evaluate_integer_constant(
                                        width.sem,
                                        value,
                                        declarator.loc,
                                        "bit-field width is not an integer constant expression")) {
                                    if (value < 0) {
                                        diagnose(DiagnosticLevel::Error,
                                                 "bit-field width cannot be negative",
                                                 declarator.loc);
                                    } else if (value >
                                               static_cast<int64_t>(
                                                   std::numeric_limits<uint32_t>::max())) {
                                        diagnose(DiagnosticLevel::Error,
                                                 "bit-field width is too large",
                                                 declarator.loc);
                                    } else {
                                        bit_width =
                                            static_cast<uint32_t>(value);
                                    }
                                }
                            }
                        }
                        bitfield_attrs = parse_layout_attributes();
                        member_children.insert(member_children.end(),
                                               bitfield_attrs.syntax.begin(),
                                               bitfield_attrs.syntax.end());
                    }

                    bool has_dmi = false;
                    bool dmi_braced = false;
                    uint32_t dmi_begin = 0;
                    uint32_t dmi_end = 0;
                    SrcLoc dmi_loc{};
                    if (check(TokenType::ASSIGN) ||
                        check(TokenType::LEFT_BRACE)) {
                        has_dmi = true;
                        dmi_loc = current_loc();
                        if (match(TokenType::ASSIGN)) {
                            dmi_braced = check(TokenType::LEFT_BRACE);
                        } else {
                            dmi_braced = true;
                        }
                        dmi_begin =
                            static_cast<uint32_t>(current_raw_index());
                        int depth = 0;
                        while (!at_end()) {
                            TokenType type = current().type;
                            if (depth == 0 &&
                                (type == TokenType::COMMA ||
                                 type == TokenType::SEMICOLON ||
                                 type == TokenType::RIGHT_BRACE)) {
                                break;
                            }
                            if (type == TokenType::LEFT_PAREN ||
                                type == TokenType::LEFT_BRACE ||
                                type == TokenType::LEFT_BRACKET) {
                                ++depth;
                            }
                            if (type == TokenType::RIGHT_PAREN ||
                                type == TokenType::RIGHT_BRACE ||
                                type == TokenType::RIGHT_BRACKET) {
                                --depth;
                            }
                            consume();
                            if (dmi_braced && depth == 0 &&
                                type == TokenType::RIGHT_BRACE) {

                                break;
                            }
                        }
                        dmi_end =
                            static_cast<uint32_t>(current_raw_index());
                    }

                    collect::RecordFieldInput input;
                    input.name = declarator.name;
                    input.type = declarator.type.valid() ? declarator.type : member_base_type.type;
                    input.qualifiers = declarator.type_ref.qualifiers;
                    input.has_default_member_initializer = has_dmi;
                    input.default_member_initializer_braced = dmi_braced;
                    input.default_member_initializer_begin = dmi_begin;
                    input.default_member_initializer_end = dmi_end;
                    input.default_member_initializer_loc = dmi_loc;
                    input.default_member_initializer_context =
                        collect_session_.current_decl_context();
                    input.default_member_initializer_lookup_generation =
                        collect_session_.lookup_generation();
                    input.loc = declarator.loc.isInvalid()
                        ? loc_for_index(member_begin)
                        : declarator.loc;
                    input.attrs = leading_member_attrs.attrs;
                    input.attrs.append(member_parser.leading_attrs);
                    input.attrs.append(declarator.attrs);
                    input.attrs.append(declarator_attrs.attrs);
                    input.attrs.append(bitfield_attrs.attrs);
                    input.type = collect_session_
                                     .apply_type_attributes(
                                         collect_session_.type_ref(input.type),
                                         input.attrs,
                                         input.loc)
                                     .type;
                    input.declared_access = current_access;
                    input.forced_alignment = std::max({leading_member_attrs.alignment,
                                                       declarator_attrs.alignment,
                                                       bitfield_attrs.alignment});
                    input.is_packed = leading_member_attrs.is_packed ||
                                      declarator_attrs.is_packed ||
                                      bitfield_attrs.is_packed;
                    input.is_bitfield = is_bitfield;
                    input.bit_width = bit_width;
                    input.bit_width_expression =
                        std::move(bit_width_expression);
                    input.bit_width_is_dependent =
                        bit_width_is_dependent;
                    input.is_mutable = flags.is_mutable;
                    fields.push_back(std::move(input));
                    children.push_back(make_node(NodeKind::FieldDecl,
                                                 member_begin,
                                                 last_consumed_raw_end(),
                                                 member_children,
                                                 text_payload(declarator.name)));
                }

                parsed_any_member = true;
                if (parsed_body || !match(TokenType::COMMA)) {
                    break;
                }
                member_begin = current_raw_index();
            }

            if (!parsed_any_member) {
                diagnose(DiagnosticLevel::Error,
                         "expected class member declarator",
                         loc_for_index(member_begin));
            }
            if (!parsed_body && !match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error,
                         "expected ';' after class member declaration",
                         current_loc());
                skip_until_statement_boundary();
            }
        }

        if (!match(TokenType::RIGHT_BRACE)) {
            diagnose(DiagnosticLevel::Error, "expected '}' after record body", current_loc());
        }
        collect_session_.set_current_record_member_access(std::nullopt);
        LayoutAttrs post_body_attrs = parse_layout_attributes();
        children.insert(children.end(), post_body_attrs.syntax.begin(), post_body_attrs.syntax.end());
        merge_attrs(record_attrs, std::move(post_body_attrs));
        if (!has_friend_equality_declaration &&
            std::none_of(methods.begin(), methods.end(),
                         [](const collect::RecordMethodInput& method) {
                             return method.name == "operator==";
                         })) {
            uint64_t key = static_cast<uint64_t>(record.entity.index);
            auto pending = pending_hidden_friend_bodies_.find(key);
            if (pending != pending_hidden_friend_bodies_.end()) {
                std::optional<PendingHiddenFriendBody> implicit_equality;
                for (const PendingHiddenFriendBody& spaceship :
                     pending->second) {
                    if (!spaceship.is_defaulted_comparison ||
                        spaceship.name != "operator<=>" ||
                        !spaceship.entity.valid() ||
                        !collect_session_.file().valid(spaceship.entity)) {
                        continue;
                    }
                    const auto* payload = std::get_if<
                        cir::FunctionTypePayload>(
                        &collect_session_.file().type_payload(
                            collect_session_.file().resolved_type(
                                spaceship.function_type)));
                    if (!payload) {
                        continue;
                    }
                    cir::TypeId equality_type =
                        collect_session_.function_type(
                            collect_session_.type_ref(
                                collect_session_.file().builtin_type(
                                    cir::BuiltinTypeKind::Bool)),
                            payload->parameters,
                            payload->is_variadic,
                            payload->has_prototype,
                            payload->member_is_const,
                            payload->exception_spec,
                            payload->parameter_pack_flags,
                            payload->member_ref_qualifier,
                            payload->member_is_volatile);
                    cir::OperatorFunctionIdentity identity;
                    identity.kind =
                        cir::OperatorFunctionKind::Symbolic;
                    identity.spelling =
                        cir::OperatorFunctionSpelling::Equal;
                    cir::EntityId equality =
                        collect_session_.add_pending_friend_function(
                            record.entity, "operator==", equality_type,
                            collect_session_.file()
                                .entity(spaceship.entity)
                                .semantic_context,
                            spaceship.loc, {},
                            /*require_existing=*/false, identity);
                    if (!equality.valid()) {
                        break;
                    }
                    PendingHiddenFriendBody generated = spaceship;
                    generated.entity = equality;
                    generated.name = "operator==";
                    generated.function_type = equality_type;
                    generated.result_type = collect_session_.type_ref(
                        collect_session_.file().builtin_type(
                            cir::BuiltinTypeKind::Bool));
                    generated.implicit_equality_origin = spaceship.entity;
                    implicit_equality = std::move(generated);
                    break;
                }
                if (implicit_equality.has_value()) {
                    pending->second.push_back(
                        std::move(*implicit_equality));
                }
            }
        }
        collect_session_.leave_scope();
        for (PendingMethodConstraints& lhs : pending_method_constraints) {
            if (lhs.method_index >= methods.size()) {
                continue;
            }
            for (const PendingMethodConstraints& rhs :
                 pending_method_constraints) {
                if (lhs.method_index == rhs.method_index ||
                    rhs.method_index >= methods.size()) {
                    continue;
                }
                if (collect_session_.declaration_more_constrained(
                        lhs.constraints, rhs.constraints)) {
                    methods[lhs.method_index].more_constrained_than.push_back(
                        methods[rhs.method_index]
                            .associated_constraint_fingerprint);
                }
            }
        }
        std::vector<const collect::Session::TemplateInfo*>
            method_template_heads(methods.size(), nullptr);
        for (const PendingMemberTemplate& pending :
             pending_member_templates) {
            if (pending.method_index < method_template_heads.size()) {
                method_template_heads[pending.method_index] = &pending.info;
            }
        }
        std::vector<cir::EntityId> method_entities;
        record = collect_session_.finish_record_definition(std::move(record),
                                                           kind,
                                                           std::move(fields),
                                                           std::move(static_data_members),
                                                           std::move(methods),
                                                           keyword.loc,
                                                           layout_options_from_attrs(record_attrs),
                                                           &method_entities,
                                                           &method_template_heads,
                                                           std::move(bases),
                                                           is_final,
                                                           kind == cir::RecordKind::Union &&
                                                               tag.empty() &&
                                                               check(TokenType::SEMICOLON));
        if (base_access_capture.valid() &&
            !collect_session_.finish_access_capture(base_access_capture,
                                                    record.entity)) {
            record.has_error = true;
        }
        replay_or_defer_record_bodies(record.entity,
                                      std::move(pending_member_templates),
                                      std::move(pending_bodies),
                                      std::move(method_entities));
        if (type_out) {
            *type_out = record.type;
        }

        std::string text = std::string(cir::record_kind_name(kind));
        if (!tag.empty()) {
            text += ' ';
            text += tag;
        }
        return make_node(NodeKind::RecordDecl,
                         begin,
                         last_consumed_raw_end(),
                         children,
                         text_payload(std::move(text)),
                         (record.has_error || header_has_error) ? NodeFlagHasError : NodeFlagNone);
    }

    std::vector<collect::RecordFieldInput> fields;
    bool is_definition = false;
    if (check(TokenType::LEFT_BRACE)) {
        is_definition = true;
        if (!tag.empty()) {
            collect_session_.declare_record_tag_in_current_scope(kind, tag, keyword.loc);
        }
        consume();

        while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
            size_t field_begin = current_raw_index();
            if (match(TokenType::SEMICOLON)) {
                continue;
            }
            if (check(TokenType::STATIC_ASSERT)) {
                ParsedDecl assert_decl = parse_static_assert_declaration();
                if (assert_decl.syntax != InvalidNodeId) {
                    children.push_back(assert_decl.syntax);
                }
                continue;
            }
            LayoutAttrs leading_field_attrs = parse_layout_attributes();
            if (!is_type_start(current().type)) {
                diagnose(DiagnosticLevel::Error, "expected field declaration", current_loc());
                skip_until_statement_boundary();
                continue;
            }

            DeclarationParser field_parser(
                *this,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberDeclSpecifier));
            cir::TypeRef field_base_type = field_parser.parse_declaration(false, true);
            NodeId field_type = field_parser.type_syntax;
            bool parsed_any_field = false;
            while (!at_end()) {
                field_parser.reset_declarator_parsing_state();
                ParsedDeclarator declarator = field_parser.parse_declarator(field_base_type, true);
                LayoutAttrs declarator_attrs = parse_layout_attributes();

                bool is_bitfield = false;
                uint32_t bit_width = 0;
                cir::TemplateValueExpression bit_width_expression;
                bool bit_width_is_dependent = false;
                NodeId width_syntax = InvalidNodeId;
                LayoutAttrs bitfield_attrs;
                if (match(TokenType::COLON)) {
                    is_bitfield = true;
                    if (check(TokenType::COMMA) || check(TokenType::SEMICOLON) ||
                        check(TokenType::RIGHT_BRACE)) {
                        diagnose(DiagnosticLevel::Error, "expected bit-field width", current_loc());
                    } else {
                        ParsedExpr width = parse_conditional_expression();
                        width_syntax = width.syntax;
                        bit_width_expression =
                            width.sem.template_value_expr;
                        collect_session_.file()
                            .canonicalize_template_value_expression(
                                bit_width_expression);
                        bit_width_is_dependent =
                            collect_session_.expr_is_dependent(width.sem) ||
                            collect_session_.expr_is_value_dependent(
                                width.sem);
                        if (!bit_width_is_dependent) {
                            int64_t value = 0;
                            if (collect_session_.evaluate_integer_constant(
                                    width.sem,
                                    value,
                                    declarator.loc,
                                    "bit-field width is not an integer constant expression")) {
                                if (value < 0) {
                                    diagnose(DiagnosticLevel::Error,
                                             "bit-field width cannot be negative",
                                             declarator.loc);
                                } else if (value >
                                           static_cast<int64_t>(
                                               std::numeric_limits<uint32_t>::max())) {
                                    diagnose(DiagnosticLevel::Error,
                                             "bit-field width is too large",
                                             declarator.loc);
                                } else {
                                    bit_width =
                                        static_cast<uint32_t>(value);
                                }
                            }
                        }
                    }
                    bitfield_attrs = parse_layout_attributes();
                }

                std::vector<NodeId> field_children = leading_field_attrs.syntax;
                field_children.push_back(field_type);
                if (declarator.syntax != InvalidNodeId) {
                    field_children.push_back(declarator.syntax);
                }
                field_children.insert(field_children.end(),
                                      declarator_attrs.syntax.begin(),
                                      declarator_attrs.syntax.end());
                if (width_syntax != InvalidNodeId) {
                    field_children.push_back(width_syntax);
                }
                field_children.insert(field_children.end(),
                                      bitfield_attrs.syntax.begin(),
                                      bitfield_attrs.syntax.end());
                NodeId field_node = make_node(NodeKind::FieldDecl,
                                              field_begin,
                                              last_consumed_raw_end(),
                                              field_children,
                                              text_payload(declarator.name));
                children.push_back(field_node);

                collect::RecordFieldInput input;
                input.name = declarator.name;
                input.type = declarator.type.valid() ? declarator.type : field_base_type.type;
                input.qualifiers = declarator.type_ref.qualifiers;
                input.loc = declarator.loc.isInvalid() ? loc_for_index(field_begin) : declarator.loc;
                input.attrs = leading_field_attrs.attrs;
                input.attrs.append(field_parser.leading_attrs);
                input.attrs.append(declarator.attrs);
                input.attrs.append(declarator_attrs.attrs);
                input.attrs.append(bitfield_attrs.attrs);

                input.type = collect_session_
                                 .apply_type_attributes(
                                     collect_session_.type_ref(input.type),
                                     input.attrs,
                                     input.loc)
                                 .type;
                input.forced_alignment = std::max({leading_field_attrs.alignment,
                                                   declarator_attrs.alignment,
                                                   bitfield_attrs.alignment});
                input.is_packed = leading_field_attrs.is_packed ||
                                  declarator_attrs.is_packed ||
                                  bitfield_attrs.is_packed;
                input.is_bitfield = is_bitfield;
                input.bit_width = bit_width;
                input.bit_width_expression =
                    std::move(bit_width_expression);
                input.bit_width_is_dependent =
                    bit_width_is_dependent;
                fields.push_back(std::move(input));
                parsed_any_field = true;

                if (!match(TokenType::COMMA)) {
                    break;
                }
                field_begin = current_raw_index();
            }

            if (!parsed_any_field) {
                diagnose(DiagnosticLevel::Error, "expected field declarator", loc_for_index(field_begin));
            }
            if (!match(TokenType::SEMICOLON)) {
                diagnose(DiagnosticLevel::Error, "expected ';' after field declaration", current_loc());
                skip_until_statement_boundary();
            }
        }

        if (!match(TokenType::RIGHT_BRACE)) {
            diagnose(DiagnosticLevel::Error, "expected '}' after record body", current_loc());
        }
        LayoutAttrs post_body_attrs = parse_layout_attributes();
        children.insert(children.end(), post_body_attrs.syntax.begin(), post_body_attrs.syntax.end());
        merge_attrs(record_attrs, std::move(post_body_attrs));
    }

    collect::RecordDeclResult record = is_definition
        ? collect_session_.define_record(kind,
                                         tag,
                                         std::move(fields),
                                         keyword.loc,
                                         layout_options_from_attrs(record_attrs))
        : collect_session_.declare_record_tag(kind, tag, keyword.loc);
    if (type_out) {
        *type_out = record.type;
    }

    std::string text = std::string(cir::record_kind_name(kind));
    if (!tag.empty()) {
        text += ' ';
        text += tag;
    }
    NodeId syntax = make_node(NodeKind::RecordDecl,
                              begin,
                              last_consumed_raw_end(),
                              children,
                              text_payload(std::move(text)),
                              record.has_error ? NodeFlagHasError : NodeFlagNone);
    return syntax;
}

NodeId Parser::parse_enum_specifier(cir::TypeId* type_out) {
    size_t begin = current_raw_index();
    Token keyword = current();
    if (!match(TokenType::ENUM)) {
        return parse_error_node("expected enum specifier", begin, begin + 1);
    }

    bool is_scoped = false;
    if (lang_opts_.is_cxx_mode() &&
        (check(TokenType::CLASS) || check(TokenType::STRUCT))) {
        is_scoped = true;
        consume();
    }

    bool enum_packed = false;
    auto consume_enum_attributes = [&]() {
        while (check(TokenType::ATTRIBUTE_KW)) {
            ParsedAttributes attrs = try_parse_attributes();
            for (const ParsedAttribute& attr : attrs.attrs.attrs) {
                if (attr.kind == AttributeKind::Packed) {
                    enum_packed = true;
                }
            }
        }
    };
    consume_enum_attributes();

    struct QualifiedEnumContextExit {
        collect::Session* session = nullptr;
        ~QualifiedEnumContextExit() {
            if (session) {
                session->leave_scope();
            }
        }
    } qualified_enum_context;
    if (lang_opts_.is_cxx_mode()) {
        ParsedNestedName nested = parse_nested_name_specifier();
        if (nested.consumed_any) {
            if (nested.has_error || !nested.scope.context.valid()) {
                diagnose(DiagnosticLevel::Error,
                         "qualified enum definition qualifier does not name a class or namespace",
                         keyword.loc);
            } else {
                const cir::File& file = collect_session_.file();
                cir::DeclContextKind context_kind =
                    file.decl_context(nested.scope.context).kind;
                if (context_kind != cir::DeclContextKind::Record &&
                    context_kind != cir::DeclContextKind::Namespace &&
                    context_kind != cir::DeclContextKind::TranslationUnit) {
                    diagnose(DiagnosticLevel::Error,
                             "qualified enum definition qualifier does not name a class or namespace",
                             keyword.loc);
                } else {
                    collect::ScopeFlags flags =
                        context_kind == cir::DeclContextKind::Record
                            ? collect::ScopeFlags::RecordScope
                            : (collect::ScopeFlags::NamespaceScope |
                               collect::ScopeFlags::FileScope);
                    collect_session_.enter_existing_context(
                        nested.scope.context,
                        flags);
                    qualified_enum_context.session = &collect_session_;
                }
            }
        }
    }

    std::string tag;
    if (is_identifier_token(current().type)) {
        tag = current().value;
        consume();
    }
    consume_enum_attributes();

    std::vector<NodeId> children;
    bool has_error = false;

    cir::TypeRef fixed_underlying{};
    if (check(TokenType::COLON)) {
        consume();
        DeclarationParser underlying_parser(*this);
        // An enum-base ends after its type-specifier-seq. Parsing a declarator
        // here would consume the name in forms such as
        // `typedef enum E : int E;` instead of leaving it for the typedef.
        fixed_underlying = underlying_parser.parse_declaration(false, true);
        if (!fixed_underlying.valid()) {
            diagnose(DiagnosticLevel::Error,
                     "expected integer type after ':' in enum specifier",
                     current_loc());
            has_error = true;
        } else {
            cir::TypeId resolved_underlying =
                collect_session_.file().resolved_type(fixed_underlying.type);
            cir::TypeKind underlying_kind =
                collect_session_.file().valid(resolved_underlying)
                    ? collect_session_.file().type(resolved_underlying).kind
                    : cir::TypeKind::Invalid;
            cir::OperatorValueDomain domain =
                collect_session_.file().operator_value_domain(fixed_underlying);
            bool integer_domain =
                domain == cir::OperatorValueDomain::Bool ||
                domain == cir::OperatorValueDomain::SignedInteger ||
                domain == cir::OperatorValueDomain::UnsignedInteger;
            bool dependent_underlying =
                collect_session_.is_dependent_type(fixed_underlying.type);
            if (!dependent_underlying &&
                (!integer_domain ||
                 (underlying_kind != cir::TypeKind::Builtin &&
                  underlying_kind != cir::TypeKind::BitInt))) {
                diagnose(DiagnosticLevel::Error,
                         "invalid fixed underlying type for enum",
                         keyword.loc);
                has_error = true;
            }
        }
    }

    if (is_scoped && !fixed_underlying.valid()) {
        fixed_underlying = collect_session_.file().type_ref(
            collect_session_.file().builtin_type(cir::BuiltinTypeKind::Int));
    }
    if (is_scoped && tag.empty()) {
        diagnose(DiagnosticLevel::Error,
                 "scoped enum requires a name",
                 keyword.loc);
        has_error = true;
    }

    if (!check(TokenType::LEFT_BRACE)) {
        if (lang_opts_.is_cxx_mode() && !is_scoped &&
            !fixed_underlying.valid() && check(TokenType::SEMICOLON)) {
            diagnose(DiagnosticLevel::Error,
                     "opaque enum declaration requires an explicit underlying type",
                     keyword.loc);
            has_error = true;
        }
        cir::TypeId type = collect_session_.declare_enum_tag(tag,
                                                             is_scoped,
                                                             fixed_underlying,
                                                             keyword.loc);
        if (type_out) {
            *type_out = type;
        }
        std::string text = is_scoped ? "enum class" : "enum";
        if (!tag.empty()) {
            text += ' ';
            text += tag;
        }
        return make_node(NodeKind::RecordDecl,
                         begin,
                         last_consumed_raw_end(),
                         children,
                         text_payload(std::move(text)),
                         (has_error || !type.valid()) ? NodeFlagHasError
                                                      : NodeFlagNone);
    }

    cir::TypeId announced_enum_type;
    bool entered_enum_scope = false;
    cir::EntityId announced_enum_entity{};
    if (lang_opts_.is_cxx_mode() && !tag.empty()) {
        announced_enum_type = collect_session_.declare_enum_tag(tag,
                                                                 is_scoped,
                                                                 fixed_underlying,
                                                                 keyword.loc);
        const auto* enum_payload = announced_enum_type.valid() &&
                                           collect_session_.file().valid(
                                               announced_enum_type)
            ? std::get_if<cir::EnumTypePayload>(
                  &collect_session_.file().type_payload(announced_enum_type))
            : nullptr;
        if (!enum_payload) {
            announced_enum_type = {};
            has_error = true;
        }
        announced_enum_entity = enum_payload ? enum_payload->entity
                                             : cir::EntityId{};
        cir::EntityId owner = collect_session_.enclosing_record_for_context(
            collect_session_.current_decl_context());
        bool defer_scoped_definition =
            is_scoped && !replaying_deferred_scoped_enum_definition_ &&
            collect_session_.is_instantiating() && owner.valid() &&
            collect_session_.file().template_specialization(owner);
        if (defer_scoped_definition && announced_enum_entity.valid()) {
            size_t definition_end = skip_balanced_until_semicolon_or_brace();
            uint64_t key = static_cast<uint64_t>(announced_enum_entity.index);
            deferred_scoped_enum_definitions_[key] =
                DeferredScopedEnumDefinition{announced_enum_entity,
                                             owner,
                                             begin,
                                             definition_end,
                                             keyword.loc};
            collect_session_.track_speculative_rollback([this, key] {
                deferred_scoped_enum_definitions_.erase(key);
            });
            if (type_out) {
                *type_out = announced_enum_type;
            }
            std::string text = "enum class " + tag;
            return make_node(NodeKind::RecordDecl,
                             begin,
                             definition_end,
                             children,
                             text_payload(std::move(text)),
                             has_error ? NodeFlagHasError : NodeFlagNone);
        }
        if (announced_enum_entity.valid() &&
            collect_session_.file().valid(announced_enum_entity)) {
            cir::DeclContextId enum_context =
                collect_session_.file()
                    .entity(announced_enum_entity)
                    .semantic_context;
            if (enum_context.valid()) {
                collect_session_.enter_existing_context(
                    enum_context,
                    collect::ScopeFlags::EnumScope);
                entered_enum_scope = true;
            }
        }
    }

    consume();
    std::vector<collect::EnumEnumeratorInput> enumerators;
    int64_t next_value = 0;
    while (!at_end() && !check(TokenType::RIGHT_BRACE)) {
        size_t enumerator_begin = current_raw_index();
        if (!check(TokenType::IDENTIFIER)) {
            diagnose(DiagnosticLevel::Error, "expected enumerator name", current_loc());
            has_error = true;
            skip_balanced_until_semicolon_or_brace();
            break;
        }

        Token name_token = current();
        NodeId name_node = parse_name_node(NodeKind::Name);
        std::vector<NodeId> enumerator_children{name_node};
        std::optional<int64_t> value;

        while (check(TokenType::ATTRIBUTE_KW) || (check(TokenType::LEFT_BRACKET) &&
               peek(1).type == TokenType::LEFT_BRACKET)) {
            ParsedAttributes enum_attrs = try_parse_attributes();
            enumerator_children.insert(enumerator_children.end(),
                                       enum_attrs.syntax.begin(),
                                       enum_attrs.syntax.end());
        }

        if (match(TokenType::ASSIGN)) {
            uint64_t value_taint_before = collect_session_.pattern_taint();
            ParsedExpr expr = parse_conditional_expression();
            enumerator_children.push_back(expr.syntax);
            int64_t evaluated = 0;
            bool defer_dependent_value =
                collect_session_.in_template_definition() &&
                (collect_session_.expr_is_dependent(expr.sem) ||
                 collect_session_.pattern_taint() != value_taint_before);
            if (defer_dependent_value) {
                value = next_value;
                ++next_value;
            } else if (collect_session_.evaluate_integer_constant(
                    expr.sem,
                    evaluated,
                    name_token.loc,
                    "enumerator value is not an integer constant expression")) {
                value = evaluated;
                next_value = evaluated + 1;
            } else {
                has_error = true;
                value = next_value;
                ++next_value;
            }
        } else {
            value = next_value;
            ++next_value;
        }

        cir::EntityId enumerator_entity = collect_session_.declare_enumerator(
            name_token.value,
            value.value_or(next_value - 1),

            fixed_underlying.valid() ? fixed_underlying.type : cir::TypeId{},
            name_token.loc);

        enumerators.push_back(collect::EnumEnumeratorInput{
            std::string(name_token.value),
            value,
            name_token.loc,
            enumerator_entity
        });
        children.push_back(make_node(NodeKind::FieldDecl,
                                     enumerator_begin,
                                     last_consumed_raw_end(),
                                     enumerator_children,
                                     text_payload(name_token.value),
                                     has_error ? NodeFlagHasError : NodeFlagNone));

        if (match(TokenType::COMMA)) {
            if (check(TokenType::RIGHT_BRACE)) {
                break;
            }
            continue;
        }
        if (!check(TokenType::RIGHT_BRACE)) {
            diagnose(DiagnosticLevel::Error, "expected ',' or '}' in enum specifier", current_loc());
            has_error = true;
            while (!at_end() && !check(TokenType::COMMA) && !check(TokenType::RIGHT_BRACE)) {
                consume();
            }
            match(TokenType::COMMA);
        }
    }

    if (!match(TokenType::RIGHT_BRACE)) {
        diagnose(DiagnosticLevel::Error, "expected '}' after enum body", current_loc());
        has_error = true;
    }

    consume_enum_attributes();
    if (entered_enum_scope) {
        collect_session_.leave_scope();
    }

    collect::EnumDeclResult enum_result =
        collect_session_.define_enum(tag,
                                     std::move(enumerators),
                                     keyword.loc,
                                     fixed_underlying,
                                     enum_packed,
                                     is_scoped);
    if (type_out) {
        *type_out = enum_result.type;
    }

    std::string text = is_scoped ? "enum class" : "enum";
    if (!tag.empty()) {
        text += ' ';
        text += tag;
    }
    return make_node(NodeKind::RecordDecl,
                     begin,
                     last_consumed_raw_end(),
                     children,
                     text_payload(std::move(text)),
                     (has_error || enum_result.has_error) ? NodeFlagHasError : NodeFlagNone);
}

bool Parser::force_deferred_scoped_enum_definition(
    cir::EntityId enum_entity) {
    if (!enum_entity.valid() || !collect_session_.file().valid(enum_entity)) {
        return false;
    }
    if (collect_session_.file().entity(enum_entity).is_definition) {
        return true;
    }
    uint64_t key = static_cast<uint64_t>(enum_entity.index);
    auto found = deferred_scoped_enum_definitions_.find(key);
    if (found == deferred_scoped_enum_definitions_.end()) {
        return false;
    }
    DeferredScopedEnumDefinition deferred = found->second;
    deferred_scoped_enum_definitions_.erase(found);

    collect_session_.track_speculative_rollback(
        "restore deferred scoped enum definition",
        [this, key, deferred] {
            deferred_scoped_enum_definitions_[key] = deferred;
        });

    collect::Session::InstantiationScope scope;
    if (!collect_session_.begin_member_instantiation_scope(enum_entity,
                                                           scope)) {
        return false;
    }
    bool entered_owner = false;
    if (deferred.owner.valid() &&
        collect_session_.file().valid(deferred.owner)) {
        cir::DeclContextId context =
            collect_session_.file().entity(deferred.owner).semantic_context;
        if (context.valid()) {
            collect_session_.enter_existing_context(
                context, collect::ScopeFlags::RecordScope);
            entered_owner = true;
        }
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    bool saved_replaying = replaying_deferred_scoped_enum_definition_;
    cursor_ = deferred.definition_begin;
    pending_template_closes_ = 0;
    replaying_deferred_scoped_enum_definition_ = true;
    cir::TypeId replayed_type{};
    (void)parse_enum_specifier(&replayed_type);
    replaying_deferred_scoped_enum_definition_ = saved_replaying;
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_template_closes;
    if (entered_owner) {
        collect_session_.leave_scope();
    }
    collect_session_.finish_template_instantiation(std::move(scope));
    return collect_session_.file().valid(enum_entity) &&
        collect_session_.file().entity(enum_entity).is_definition;
}

bool Parser::force_deferred_member_class_definition(
    cir::EntityId record_entity) {
    if (!record_entity.valid() ||
        !collect_session_.file().valid(record_entity)) {
        return false;
    }
    const cir::RecordFacts* existing =
        collect_session_.file().record_facts(record_entity);
    if (existing && !existing->is_incomplete) {
        return true;
    }
    uint64_t key = static_cast<uint64_t>(record_entity.index);
    auto found = deferred_member_class_definitions_.find(key);
    if (found == deferred_member_class_definitions_.end()) {
        return false;
    }
    DeferredMemberClassDefinition deferred = found->second;
    deferred_member_class_definitions_.erase(found);

    collect_session_.track_speculative_rollback(
        "restore deferred member class definition",
        [this, key, deferred] {
            deferred_member_class_definitions_[key] = deferred;
        });

    collect::Session::InstantiationScope scope;
    if (!collect_session_.begin_member_instantiation_scope(record_entity,
                                                           scope)) {
        return false;
    }
    bool entered_owner = false;
    if (deferred.owner.valid() &&
        collect_session_.file().valid(deferred.owner)) {
        cir::DeclContextId context =
            collect_session_.file().entity(deferred.owner).semantic_context;
        if (context.valid()) {
            collect_session_.enter_existing_context(
                context, collect::ScopeFlags::RecordScope);
            entered_owner = true;
        }
    }

    size_t saved_cursor = cursor_;
    size_t saved_last_end = last_consumed_raw_end_;
    int saved_template_closes = pending_template_closes_;
    size_t saved_replaying = replaying_deferred_member_class_begin_;
    cursor_ = deferred.definition_begin;
    pending_template_closes_ = 0;
    replaying_deferred_member_class_begin_ = deferred.definition_begin;
    cir::TypeId replayed_type{};
    (void)parse_record_specifier(&replayed_type);
    replaying_deferred_member_class_begin_ = saved_replaying;
    cursor_ = saved_cursor;
    last_consumed_raw_end_ = saved_last_end;
    pending_template_closes_ = saved_template_closes;
    if (entered_owner) {
        collect_session_.leave_scope();
    }
    collect_session_.finish_template_instantiation(std::move(scope));
    const cir::RecordFacts* facts =
        collect_session_.file().record_facts(record_entity);
    return facts && !facts->is_incomplete;
}

} // namespace aburi::syntax
