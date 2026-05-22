#include "parser.h"
#include "cpp_out_of_line_match.h"
#include "../ast/ast_clone.h"
#include "../ast/special_members.h"
#include "../collect/lookup_engine.h"
#include "../collect/collect_templates_internal.h"
#include "../helpers/casting.h"
#include "../helpers/qualified_name_utils.h"

// Parser-owned handling for out-of-line C++ member definitions.
// Keep the heavy definition replay/merge logic out of parser_cxx.cpp so the
// main C++ parser file stays focused on core syntax entrypoints.

namespace {
std::optional<std::string> namespace_prefix_from_member_qualifier(
    const std::string* qualifier_prefix) {
    if (!qualifier_prefix || qualifier_prefix->empty()) {
        return std::nullopt;
    }
    size_t pos = qualifier_prefix->rfind("::");
    if (pos == std::string::npos || pos == 0) {
        return std::nullopt;
    }
    return qualifier_prefix->substr(0, pos);
}

void adopt_out_of_line_member_qualifier_prefix(const FuncDecl* target_decl,
                                               const FuncDecl* parsed_decl) {
    if (!target_decl) {
        return;
    }
    auto namespace_prefix = namespace_prefix_from_member_qualifier(
        parsed_decl ? get_func_decl_cxx_qualifier_prefix(parsed_decl) : nullptr);
    if (namespace_prefix.has_value()) {
        set_func_decl_cxx_qualifier_prefix(target_decl, *namespace_prefix);
    } else {
        set_func_decl_cxx_qualifier_prefix(target_decl, std::nullopt);
    }
}

void merge_out_of_line_constructor_definition(
    CppConstructorDecl* matched_ctor_decl,
    CppConstructorDecl* parsed_ctor,
    const RecordSemanticState::Constructor* matched_ctor_state,
    const std::shared_ptr<Symbol>& matched_symbol,
    const std::shared_ptr<ASTContext>& ast_ctx,
    const ObjectDecl* owner_record_decl) {
    if (!matched_ctor_decl || !parsed_ctor || !matched_ctor_state || !owner_record_decl) {
        return;
    }

    matched_ctor_decl->parameters = std::move(parsed_ctor->parameters);
    matched_ctor_decl->type = parsed_ctor->type;
    matched_ctor_decl->body = std::move(parsed_ctor->body);
    matched_ctor_decl->scope = parsed_ctor->scope;
    matched_ctor_decl->stmt_labels = std::move(parsed_ctor->stmt_labels);
    matched_ctor_decl->ctor_initializers = std::move(parsed_ctor->ctor_initializers);
    matched_ctor_decl->is_explicit = parsed_ctor->is_explicit;
    matched_ctor_decl->explicit_specifier = parsed_ctor->explicit_specifier;
    matched_ctor_decl->is_deleted = parsed_ctor->is_deleted;
    matched_ctor_decl->is_defaulted = parsed_ctor->is_defaulted;
    matched_ctor_decl->is_defaulted_on_first_declaration = false;
    matched_ctor_decl->is_constexpr = parsed_ctor->is_constexpr;
    matched_ctor_decl->is_consteval = parsed_ctor->is_consteval;
    if (matched_ctor_decl->is_consteval) {
        matched_ctor_decl->is_constexpr = true;
        matched_ctor_decl->is_inline = true;
    }
    matched_ctor_decl->set_language_linkage(parsed_ctor->get_language_linkage());
    if (parsed_ctor->asm_label) {
        matched_ctor_decl->set_asm_label(*parsed_ctor->asm_label);
    } else {
        matched_ctor_decl->clear_asm_label();
    }
    matched_ctor_decl->clear_deferred_inline_body_token_range();

    adopt_out_of_line_member_qualifier_prefix(matched_ctor_decl, parsed_ctor);

    if (ast_ctx) {
        const auto& parsed_attrs = ast_ctx->get_attrs(parsed_ctor->node_id).attrs;
        if (!parsed_attrs.empty()) {
            auto& dst_attrs = ast_ctx->get_attrs_mut(matched_ctor_decl->node_id).attrs;
            dst_attrs.insert(dst_attrs.end(), parsed_attrs.begin(), parsed_attrs.end());
        }
    }

    if (matched_symbol) {
        matched_symbol->is_defined = true;
        matched_symbol->is_deleted = matched_ctor_decl->is_deleted;
        matched_symbol->is_defaulted = matched_ctor_decl->is_defaulted;
        matched_symbol->is_constexpr = matched_ctor_decl->is_constexpr;
        matched_symbol->is_consteval = matched_ctor_decl->is_consteval;
        matched_symbol->is_inline = matched_ctor_decl->is_inline;
        matched_symbol->type = QualType(matched_ctor_decl->type);
        matched_symbol->function_definition = matched_ctor_decl;
    }

    if (const RecordSemanticState* owner_state =
            record_semantics_cache_lookup(owner_record_decl, ast_ctx.get())) {
        RecordSemanticState updated_state = *owner_state;
        for (auto& ctor : updated_state.constructors) {
            if (ctor.decl != matched_ctor_state->decl) {
                continue;
            }
            ctor.decl = matched_ctor_decl;
            ctor.type = QualType(matched_ctor_decl->type);
            ctor.is_deleted = matched_ctor_decl->is_deleted;
            ctor.is_defaulted = matched_ctor_decl->is_defaulted;
            ctor.is_constexpr = matched_ctor_decl->is_constexpr;
            ctor.is_consteval = matched_ctor_decl->is_consteval;
            if (matched_symbol) {
                ctor.symbol = matched_symbol;
            }
            break;
        }
        cpp_recompute_default_constructor_traits(
            updated_state.definition_data,
            updated_state.constructors);
        record_semantics_cache_set(
            ast_ctx.get(),
            owner_record_decl,
            std::move(updated_state));
    }
}

void merge_out_of_line_constructor_template_definition(
    CppConstructorDecl* matched_ctor_decl,
    CppConstructorDecl* parsed_ctor,
    const std::shared_ptr<ASTContext>& ast_ctx) {
    if (!matched_ctor_decl || !parsed_ctor) {
        return;
    }

    matched_ctor_decl->parameters = std::move(parsed_ctor->parameters);
    matched_ctor_decl->type = parsed_ctor->type;
    matched_ctor_decl->body = std::move(parsed_ctor->body);
    matched_ctor_decl->scope = parsed_ctor->scope;
    matched_ctor_decl->stmt_labels = std::move(parsed_ctor->stmt_labels);
    matched_ctor_decl->ctor_initializers =
        std::move(parsed_ctor->ctor_initializers);
    matched_ctor_decl->is_explicit = parsed_ctor->is_explicit;
    matched_ctor_decl->explicit_specifier = parsed_ctor->explicit_specifier;
    matched_ctor_decl->is_deleted = parsed_ctor->is_deleted;
    matched_ctor_decl->is_defaulted = parsed_ctor->is_defaulted;
    matched_ctor_decl->is_defaulted_on_first_declaration = false;
    matched_ctor_decl->is_constexpr = parsed_ctor->is_constexpr;
    matched_ctor_decl->is_consteval = parsed_ctor->is_consteval;
    if (matched_ctor_decl->is_consteval) {
        matched_ctor_decl->is_constexpr = true;
        matched_ctor_decl->is_inline = true;
    }
    matched_ctor_decl->set_language_linkage(parsed_ctor->get_language_linkage());
    if (parsed_ctor->asm_label) {
        matched_ctor_decl->set_asm_label(*parsed_ctor->asm_label);
    } else {
        matched_ctor_decl->clear_asm_label();
    }
    matched_ctor_decl->clear_deferred_inline_body_token_range();

    adopt_out_of_line_member_qualifier_prefix(matched_ctor_decl, parsed_ctor);

    if (ast_ctx) {
        const auto& parsed_attrs =
            ast_ctx->get_attrs(parsed_ctor->node_id).attrs;
        if (!parsed_attrs.empty()) {
            auto& dst_attrs =
                ast_ctx->get_attrs_mut(matched_ctor_decl->node_id).attrs;
            dst_attrs.insert(
                dst_attrs.end(),
                parsed_attrs.begin(),
                parsed_attrs.end());
        }
    }
}

struct ScopeRestoreGuard {
    Collect* collect = nullptr;
    std::shared_ptr<Scope> scope;
    std::shared_ptr<DeclContext> context;

    ~ScopeRestoreGuard() {
        if (!collect) {
            return;
        }
        collect->collect_set_current_scope(scope);
        collect->set_current_decl_context(context);
    }
};

template <typename StackT>
struct RecordParseScopeGuard {
    StackT* stack = nullptr;

    ~RecordParseScopeGuard() {
        if (stack && !stack->empty()) {
            stack->pop_back();
        }
    }
};
} // namespace

void Parser::remap_out_of_line_constructor_with_parameter_rebinds(
    CppConstructorDecl* ctor_decl,
    const std::unordered_map<const TemplateParameterDecl*,
                             const TemplateParameterDecl*>& parameter_rebinds,
    SrcLoc declarator_loc) {
    if (!ctor_decl || parameter_rebinds.empty()) {
        return;
    }

    ASTCloneContext clone_ctx;
    clone_ctx.ast_ctx = ast_ctx.get();
    for (const auto& [active_parameter, canonical_parameter] : parameter_rebinds) {
        auto* active_non_type =
            dyn_cast<TemplateNonTypeParmDecl>(
                const_cast<TemplateParameterDecl*>(active_parameter));
        auto* canonical_non_type =
            dyn_cast<TemplateNonTypeParmDecl>(
                const_cast<TemplateParameterDecl*>(canonical_parameter));
        if (active_non_type && canonical_non_type &&
            active_non_type->sym && canonical_non_type->sym) {
            clone_ctx.symbol_remap.emplace(
                active_non_type->sym.get(),
                canonical_non_type->sym);
        }
    }

    clone_ctx.rewrite_type = [&](QualType type) -> QualType {
        return template_sema_internal::remap_template_parameter_types_in_type(
            type,
            parameter_rebinds);
    };
    clone_ctx.rewrite_symbol =
        [&](const std::shared_ptr<Symbol>& sym) -> std::shared_ptr<Symbol> {
        if (!sym) {
            return nullptr;
        }
        if (auto it = clone_ctx.symbol_remap.find(sym.get());
            it != clone_ctx.symbol_remap.end()) {
            return it->second;
        }
        return sym;
    };

    ctor_decl->type =
        clone_ctx.rewrite_type(QualType(ctor_decl->type)).get_shared();

    std::vector<std::unique_ptr<Decl>> remapped_parameters;
    remapped_parameters.reserve(ctor_decl->parameters.size());
    for (const auto& parameter : ctor_decl->parameters) {
        std::string clone_error;
        auto remapped_parameter =
            clone_decl_tree(parameter.get(), clone_ctx, &clone_error);
        if (!remapped_parameter) {
            error_custloc(
                clone_error.empty()
                    ? "failed to remap out-of-line constructor parameter"
                    : clone_error,
                parameter ? parameter->location : declarator_loc);
        }
        remapped_parameters.push_back(std::move(remapped_parameter));
    }
    ctor_decl->parameters = std::move(remapped_parameters);

    for (auto& initializer : ctor_decl->ctor_initializers) {
        if (initializer.member_expr) {
            std::string clone_error;
            auto remapped_member =
                clone_expr_with_substitution(
                    initializer.member_expr.get(),
                    clone_ctx,
                    &clone_error);
            if (!remapped_member) {
                error_custloc(
                    clone_error.empty()
                        ? "failed to remap out-of-line constructor member initializer"
                        : clone_error,
                    initializer.location);
            }
            initializer.member_expr = std::move(remapped_member);
        }
        if (initializer.init_expr) {
            std::string clone_error;
            auto remapped_init =
                clone_expr_with_substitution(
                    initializer.init_expr.get(),
                    clone_ctx,
                    &clone_error);
            if (!remapped_init) {
                error_custloc(
                    clone_error.empty()
                        ? "failed to remap out-of-line constructor initializer expression"
                        : clone_error,
                    initializer.location);
            }
            initializer.init_expr = std::move(remapped_init);
        }
    }

    if (ctor_decl->body) {
        std::string clone_error;
        auto remapped_body =
            clone_stmt_tree(ctor_decl->body.get(), clone_ctx, &clone_error);
        if (!remapped_body) {
            error_custloc(
                clone_error.empty()
                    ? "failed to remap out-of-line constructor body"
                    : clone_error,
                ctor_decl->body->location);
        }
        ctor_decl->body = std::move(remapped_body);
    }
}

bool Parser::is_cpp_out_of_line_constructor_declaration_start() {
    if (!is_cxx_mode_active()) {
        return false;
    }

    RevertingTentativeParsingAction tentative(*this);
    while (gentle_check(TokenType::CONSTEXPR_KW) ||
           gentle_check(TokenType::CONSTEVAL_KW) ||
           gentle_check(TokenType::INLINE)) {
        advance();
    }
    consume_cpp_scope_resolution(); // Allow optional leading '::'.

    std::vector<CppQualifiedNameComponent> components;
    auto parse_component = [&]() -> std::optional<CppQualifiedNameComponent> {
        if (!gentle_check(TokenType::IDENTIFIER)) {
            return std::nullopt;
        }
        CppQualifiedNameComponent component;
        component.name = current_token().value;
        advance();
        if (gentle_check(TokenType::LESS_THAN)) {
            component.has_template_argument_list = true;
            component.template_arguments = parse_cpp_template_argument_list();
        }
        return component;
    };

    auto first_component = parse_component();
    if (!first_component) {
        return false;
    }
    components.push_back(std::move(*first_component));
    bool saw_scope_resolution = false;
    while (is_cpp_scope_resolution_here()) {
        saw_scope_resolution = true;
        consume_cpp_scope_resolution();
        auto component = parse_component();
        if (!component) {
            return false;
        }
        components.push_back(std::move(*component));
    }

    if (!saw_scope_resolution || components.size() < 2) {
        return false;
    }
    if (components.back().has_template_argument_list ||
        gentle_check(TokenType::BITWISE_NOT) ||
        !gentle_check(TokenType::LEFT_PAREN)) {
        return false;
    }

    const auto& final_name = components.back().name;
    const auto& owner_name = components[components.size() - 2].name;
    return final_name == owner_name;
}

bool Parser::is_cpp_out_of_line_destructor_declaration_start() {
    if (!is_cxx_mode_active()) {
        return false;
    }

    RevertingTentativeParsingAction tentative(*this);
    while (gentle_check(TokenType::CONSTEVAL_KW)) {
        advance();
    }
    consume_cpp_scope_resolution(); // Allow optional leading '::'.

    std::vector<CppQualifiedNameComponent> owner_components;
    auto parse_component = [&]() -> std::optional<CppQualifiedNameComponent> {
        if (!gentle_check(TokenType::IDENTIFIER)) {
            return std::nullopt;
        }
        CppQualifiedNameComponent component;
        component.name = current_token().value;
        advance();
        if (gentle_check(TokenType::LESS_THAN)) {
            component.has_template_argument_list = true;
            component.template_arguments = parse_cpp_template_argument_list();
        }
        return component;
    };

    auto first_component = parse_component();
    if (!first_component) {
        return false;
    }
    owner_components.push_back(std::move(*first_component));
    bool saw_scope_resolution = false;
    while (is_cpp_scope_resolution_here()) {
        saw_scope_resolution = true;
        consume_cpp_scope_resolution();
        if (gentle_check(TokenType::BITWISE_NOT)) {
            break;
        }
        auto component = parse_component();
        if (!component) {
            return false;
        }
        owner_components.push_back(std::move(*component));
    }

    if (!saw_scope_resolution || owner_components.empty()) {
        return false;
    }
    if (!gentle_check_and_consume(TokenType::BITWISE_NOT)) {
        return false;
    }
    if (!gentle_check(TokenType::IDENTIFIER)) {
        return false;
    }
    std::string destructor_name = current_token().value;
    advance();
    if (!gentle_check(TokenType::LEFT_PAREN)) {
        return false;
    }

    const std::string& owner_name = owner_components.back().name;
    return destructor_name == owner_name;
}

std::vector<std::unique_ptr<Decl>> Parser::parse_cpp_out_of_line_constructor_definition() {
    std::vector<std::unique_ptr<Decl>> parsed_decls;
    if (!is_cxx_mode_active() ||
        !is_cpp_out_of_line_constructor_declaration_start()) {
        return parsed_decls;
    }

    SrcLoc decl_loc = current_token().loc;
    bool prefix_constexpr = false;
    bool prefix_consteval = false;
    bool prefix_inline = false;
    while (true) {
        if (gentle_check(TokenType::CONSTEXPR_KW)) {
            if (prefix_constexpr) {
                error_custloc("duplicate 'constexpr' specifier", current_token().loc);
            }
            if (prefix_consteval) {
                error_custloc(
                    "'constexpr' cannot be combined with 'consteval'",
                    current_token().loc);
            }
            prefix_constexpr = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::CONSTEVAL_KW)) {
            if (!lang_opts.is_cxx20_or_later()) {
                error_custloc("'consteval' is only available in C++20",
                              current_token().loc);
            }
            if (prefix_consteval) {
                error_custloc("duplicate 'consteval' specifier", current_token().loc);
            }
            if (prefix_constexpr) {
                error_custloc(
                    "'constexpr' cannot be combined with 'consteval'",
                    current_token().loc);
            }
            prefix_consteval = true;
            prefix_constexpr = true;
            prefix_inline = true;
            advance();
            continue;
        }
        if (gentle_check(TokenType::INLINE)) {
            if (prefix_inline) {
                error_custloc("duplicate 'inline' specifier", current_token().loc);
            }
            prefix_inline = true;
            advance();
            continue;
        }
        break;
    }
    bool has_global_qualifier = consume_cpp_scope_resolution();
    std::vector<CppQualifiedNameComponent> name_components;
    std::vector<size_t> component_token_indices;

    if (!gentle_check(TokenType::IDENTIFIER)) {
        error_custloc("expected identifier in out-of-line constructor definition",
                      current_token().loc);
    }

    auto parse_component =
        [&]() -> CppQualifiedNameComponent {
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected identifier after '::' in out-of-line constructor definition",
                    current_token().loc);
            }
            CppQualifiedNameComponent component;
            component.name = current_token().value;
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                component.has_template_argument_list = true;
                component.template_arguments = parse_cpp_template_argument_list();
            }
            return component;
        };

    while (true) {
        component_token_indices.push_back(get_token_idx());
        name_components.push_back(parse_component());
        if (!is_cpp_scope_resolution_here()) {
            break;
        }
        consume_cpp_scope_resolution();
    }

    if (name_components.size() < 2 || component_token_indices.size() < 2) {
        error_custloc("expected qualified constructor name", decl_loc);
    }

    const auto& constructor_component = name_components.back();
    const auto& owner_component = name_components[name_components.size() - 2];
    const std::string& constructor_name = constructor_component.name;
    const std::string& owner_name = owner_component.name;
    if (constructor_component.has_template_argument_list) {
        error_custloc("expected constructor name '" + owner_name + "'", decl_loc);
    }
    if (constructor_name != owner_name) {
        error_custloc("expected constructor name '" + owner_name + "'", decl_loc);
    }

    std::vector<std::string> namespace_qualifiers;
    namespace_qualifiers.reserve(name_components.size() - 2);
    for (size_t idx = 0; idx + 2 < name_components.size(); ++idx) {
        if (name_components[idx].has_template_argument_list) {
            fail_cpp_future_work(
                "template-id nested-name specifier",
                "template-id qualifier chains",
                decl_loc);
        }
        namespace_qualifiers.push_back(name_components[idx].name);
    }
    const size_t constructor_token_idx = component_token_indices.back();
    std::vector<std::string> qualified_owner_components = namespace_qualifiers;
    qualified_owner_components.push_back(owner_component.spelling());
    std::string qualified_owner_name = qualified_name_utils::format_cpp_qualified_name(
        has_global_qualifier,
        namespace_qualifiers,
        owner_component.spelling());
    std::string qualified_constructor_name = qualified_name_utils::format_cpp_qualified_name(
        has_global_qualifier,
        qualified_owner_components,
        constructor_name);

    auto current_scope = collect_->collect_current_scope();
    auto translation_unit_context = collect_->get_translation_unit_decl_context();
    auto current_context = collect_->get_current_decl_context();
    if (!current_scope || !translation_unit_context || !current_context) {
        error_custloc("internal error: missing scope context for constructor definition",
                      decl_loc);
    }
    auto global_scope = current_scope;
    while (global_scope && global_scope->parent) {
        global_scope = global_scope->parent;
    }
    if (!global_scope) {
        error_custloc("internal error: missing global scope for constructor definition",
                      decl_loc);
    }

    auto owner_namespace_scope = has_global_qualifier ? global_scope : current_scope;
    std::shared_ptr<DeclContext> owner_namespace_context =
        has_global_qualifier ? translation_unit_context : current_context;
    for (size_t idx = 0; idx < namespace_qualifiers.size(); ++idx) {
        bool allow_enclosing_lookup = (!has_global_qualifier && idx == 0);
        auto resolved = resolve_named_namespace_scope(
            owner_namespace_context.get(),
            namespace_qualifiers[idx],
            allow_enclosing_lookup);
        if (!resolved || !resolved->associated_decl_context) {
            error_custloc(
                "out-of-line declaration of '" +
                    qualified_constructor_name +
                    "' does not match any declaration in the target class",
                decl_loc);
        }
        owner_namespace_scope = resolved;
        owner_namespace_context = std::shared_ptr<DeclContext>(
            owner_namespace_context,
            resolved->associated_decl_context);
    }

    auto saved_scope = collect_->collect_current_scope();
    auto saved_context = collect_->get_current_decl_context();
    ScopeRestoreGuard scope_restore_guard{
        collect_.get(),
        saved_scope,
        saved_context
    };

    const ObjectDecl* owner_record_decl = nullptr;
    const ClassTemplateDecl* owner_class_template = nullptr;
    QualType owner_current_instantiation_type = nullptr;
    bool allow_owner_enclosing_lookup =
        !has_global_qualifier && namespace_qualifiers.empty();
    if (owner_component.has_template_argument_list) {
        const DeclBinding* template_binding =
            LookupEngine::lookup_unqualified_template_binding(
                owner_component.name,
                owner_namespace_scope,
                allow_owner_enclosing_lookup,
                LookupNamespace::Tag);
        const Decl* primary_template = nullptr;
        if (template_binding) {
            primary_template = template_binding->template_decl;
            if (!primary_template &&
                template_binding->template_overload_candidates.size() == 1) {
                primary_template =
                    template_binding->template_overload_candidates.front();
            }
        }
        auto* class_template = dyn_cast<ClassTemplateDecl>(primary_template);
        if (!class_template ||
            !cpp_primary_template_owner_matches(
                class_template,
                owner_component.template_arguments)) {
            error_custloc(
                "out-of-line declaration of '" +
                    qualified_owner_name + "::" + constructor_name +
                    "' does not match any declaration in the target class",
                decl_loc);
        }
        owner_class_template = class_template;
        owner_record_decl = class_template->pattern_semantic_decl();
        owner_current_instantiation_type =
            build_cpp_current_instantiation_type(
                owner_class_template,
                owner_name,
                owner_component.template_arguments);
    } else {
        auto* owner_tag_decl = LookupEngine::lookup_tag_decl(
            owner_name,
            owner_namespace_scope,
            allow_owner_enclosing_lookup);
        const ObjectDecl* owner_record = dyn_cast<ObjectDecl>(owner_tag_decl);
        if (owner_record && owner_record->get_record_type()) {
            if (auto* canonical_owner =
                    dyn_cast<ObjectDecl>(
                        owner_record->get_record_type()->get_decl())) {
                owner_record = canonical_owner;
            }
        }
        owner_record_decl = owner_record;
    }
    if (!owner_record_decl) {
        error_custloc(
            "out-of-line declaration of '" +
                qualified_owner_name + "::" + constructor_name +
                "' does not match any declaration in the target class",
            decl_loc);
    }
    const RecordSemanticState* owner_state =
        collect_->query_lookup_record_semantics(owner_record_decl);
    if (!owner_state || owner_state->is_incomplete) {
        error_custloc(
            "incomplete type '" + qualified_owner_name +
                "' named in nested name specifier",
            decl_loc);
    }

    if (saved_scope &&
        scope_flags_contains(saved_scope->flags, ScopeFlags::TemplateParameterScope) &&
        saved_context) {
        auto rebased_scope = std::make_shared<Scope>(*saved_scope);
        rebased_scope->parent = owner_namespace_scope;
        rebased_scope->associated_decl_context = saved_context.get();
        collect_->collect_set_current_scope(std::move(rebased_scope));
        collect_->set_current_decl_context(saved_context);
    } else {
        collect_->collect_set_current_scope(owner_namespace_scope);
        collect_->set_current_decl_context(owner_namespace_context);
    }

    set_token_idx(constructor_token_idx);
    QualType previous_record_lookup_type =
        collect_ ? collect_->collect_current_cpp_record_lookup_type()
                 : QualType();
    struct OutOfLineRecordLookupGuard {
        Collect* collect = nullptr;
        QualType previous_type = nullptr;
        ~OutOfLineRecordLookupGuard() {
            if (collect) {
                collect->collect_set_current_cpp_record_lookup_type(previous_type);
            }
        }
    } record_lookup_guard{collect_.get(), previous_record_lookup_type};
    QualType owner_record_lookup_type = owner_current_instantiation_type;
    if (!owner_record_lookup_type && owner_record_decl->get_record_type()) {
        owner_record_lookup_type =
            QualType(owner_record_decl->get_record_type());
    }
    if (collect_ && owner_record_lookup_type) {
        collect_->collect_set_current_cpp_record_lookup_type(
            owner_record_lookup_type);
    }
    cxx_record_parse_stack_.push_back(
        CppRecordParseFrame{
            owner_record_decl->is_union ? CppRecordKind::Union : CppRecordKind::Class,
            owner_name,
            owner_record_decl,
            owner_class_template,
            owner_current_instantiation_type});
    RecordParseScopeGuard<decltype(cxx_record_parse_stack_)>
        record_parse_scope_guard{&cxx_record_parse_stack_};

    auto parsed_member = parse_cpp_constructor_member();
    auto* parsed_ctor = dyn_cast<CppConstructorDecl>(parsed_member.get());
    if (!parsed_ctor) {
        error_custloc(
            "internal error: failed to parse out-of-line constructor definition",
            decl_loc);
    }
    if (prefix_constexpr) {
        parsed_ctor->is_constexpr = true;
    }
    if (prefix_consteval) {
        parsed_ctor->is_consteval = true;
        parsed_ctor->is_constexpr = true;
        parsed_ctor->is_inline = true;
    }
    if (prefix_inline) {
        parsed_ctor->is_inline = true;
    }

    if (owner_class_template && !active_template_parameter_stack_.empty()) {
        const auto& active_parameters = active_template_parameter_stack_.back();
        if (active_parameters.size() == owner_class_template->parameters.size()) {
            std::unordered_map<const TemplateParameterDecl*,
                               const TemplateParameterDecl*> parameter_rebinds;
            parameter_rebinds.reserve(active_parameters.size());
            for (size_t idx = 0; idx < active_parameters.size(); ++idx) {
                const auto* active_parameter = active_parameters[idx];
                const auto* canonical_parameter =
                    owner_class_template->parameters[idx].get();
                if (!active_parameter || !canonical_parameter ||
                    active_parameter->get_kind() != canonical_parameter->get_kind()) {
                    error_custloc(
                        "internal error: out-of-line constructor template head is not structurally compatible with the owner template",
                        decl_loc);
                }
                parameter_rebinds.emplace(active_parameter, canonical_parameter);
            }
            remap_out_of_line_constructor_with_parameter_rebinds(
                parsed_ctor,
                parameter_rebinds,
                decl_loc);
        }
    }

    bool parsed_is_definition =
        parsed_ctor->body != nullptr ||
        parsed_ctor->has_deferred_inline_body() ||
        parsed_ctor->is_deleted ||
        parsed_ctor->is_defaulted;
    if (!parsed_is_definition) {
        error_custloc(
            "out-of-line declaration of '" +
                qualified_constructor_name +
                "' must be a definition",
            decl_loc);
    }

    auto parameter_shape_matches =
        [](const TemplateParameterDecl* active_parameter,
           const TemplateParameterDecl* canonical_parameter) -> bool {
        return active_parameter &&
               canonical_parameter &&
               active_parameter->get_kind() == canonical_parameter->get_kind() &&
               active_parameter->is_parameter_pack ==
                   canonical_parameter->is_parameter_pack &&
               active_parameter->depth == canonical_parameter->depth &&
               active_parameter->index == canonical_parameter->index;
    };
    auto find_active_parameter_list_matching =
        [&](const TemplateParameterList& canonical_parameters)
        -> const std::vector<const TemplateParameterDecl*>* {
        for (auto stack_it = active_template_parameter_stack_.rbegin();
             stack_it != active_template_parameter_stack_.rend();
             ++stack_it) {
            if (stack_it->size() != canonical_parameters.size()) {
                continue;
            }
            bool matches = true;
            for (size_t idx = 0; idx < canonical_parameters.size(); ++idx) {
                if (!parameter_shape_matches(
                        (*stack_it)[idx],
                        canonical_parameters[idx].get())) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                return &*stack_it;
            }
        }
        return nullptr;
    };
    auto add_parameter_rebinds =
        [&](const std::vector<const TemplateParameterDecl*>& active_parameters,
            const TemplateParameterList& canonical_parameters,
            std::unordered_map<const TemplateParameterDecl*,
                               const TemplateParameterDecl*>& rebinds) -> bool {
        if (active_parameters.size() != canonical_parameters.size()) {
            return false;
        }
        for (size_t idx = 0; idx < canonical_parameters.size(); ++idx) {
            const auto* active_parameter = active_parameters[idx];
            const auto* canonical_parameter = canonical_parameters[idx].get();
            if (!parameter_shape_matches(active_parameter, canonical_parameter)) {
                return false;
            }
            rebinds.emplace(active_parameter, canonical_parameter);
        }
        return true;
    };
    auto non_type_parameter_types_match_after_rebind =
        [&](const std::vector<const TemplateParameterDecl*>& active_parameters,
            const TemplateParameterList& canonical_parameters,
            const std::unordered_map<const TemplateParameterDecl*,
                                     const TemplateParameterDecl*>& rebinds)
        -> bool {
        for (size_t idx = 0; idx < canonical_parameters.size(); ++idx) {
            auto* active_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(active_parameters[idx]));
            if (!active_non_type) {
                continue;
            }
            auto* canonical_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(
                        canonical_parameters[idx].get()));
            if (!canonical_non_type) {
                return false;
            }
            QualType remapped_active_type =
                template_sema_internal::remap_template_parameter_types_in_type(
                    active_non_type->type,
                    rebinds);
            if (!cpp_out_of_line_type_matches(
                    remapped_active_type,
                    canonical_non_type->type,
                    false)) {
                return false;
            }
        }
        return true;
    };

    const RecordSemanticState::Constructor* matched_ctor_state = nullptr;
    // Out-of-line definition must match a previously declared constructor
    // signature in the class; compare canonicalized parameter signatures.
    QualType parsed_ctor_type = desugar_type(QualType(parsed_ctor->type));
    for (const auto& ctor : owner_state->constructors) {
        if (ctor.is_implicit || !ctor.type) {
            continue;
        }
        QualType candidate_type = desugar_type(ctor.type);
        if (!cpp_out_of_line_type_matches(candidate_type, parsed_ctor_type, true)) {
            continue;
        }
        matched_ctor_state = &ctor;
        break;
    }
    CppConstructorDecl* matched_ctor_template_decl = nullptr;
    std::unordered_map<const TemplateParameterDecl*, const TemplateParameterDecl*>
        matched_ctor_template_rebinds;
    if (!matched_ctor_state) {
        for (const auto& method_template : owner_state->method_templates) {
            if (method_template.name != constructor_name ||
                !method_template.decl ||
                !method_template.decl->function_decl()) {
                continue;
            }
            auto* templated_ctor =
                dyn_cast<CppConstructorDecl>(
                    method_template.decl->function_decl());
            if (!templated_ctor || !templated_ctor->type) {
                continue;
            }

            std::unordered_map<const TemplateParameterDecl*,
                               const TemplateParameterDecl*> rebinds;
            if (owner_class_template) {
                const auto* active_owner_parameters =
                    find_active_parameter_list_matching(
                        owner_class_template->parameters);
                if (!active_owner_parameters ||
                    !add_parameter_rebinds(
                        *active_owner_parameters,
                        owner_class_template->parameters,
                        rebinds)) {
                    continue;
                }
            }
            const auto* active_member_parameters =
                find_active_parameter_list_matching(
                    method_template.decl->parameters);
            if (!active_member_parameters ||
                !add_parameter_rebinds(
                    *active_member_parameters,
                    method_template.decl->parameters,
                    rebinds) ||
                !non_type_parameter_types_match_after_rebind(
                    *active_member_parameters,
                    method_template.decl->parameters,
                    rebinds)) {
                continue;
            }

            QualType remapped_parsed_type =
                template_sema_internal::remap_template_parameter_types_in_type(
                    QualType(parsed_ctor->type),
                    rebinds);
            if (!cpp_out_of_line_type_matches(
                    desugar_type(QualType(templated_ctor->type)),
                    desugar_type(remapped_parsed_type),
                    true)) {
                continue;
            }

            matched_ctor_template_decl =
                const_cast<CppConstructorDecl*>(templated_ctor);
            matched_ctor_template_rebinds = std::move(rebinds);
            break;
        }
    }
    if ((!matched_ctor_state || !matched_ctor_state->decl) &&
        !matched_ctor_template_decl) {
        error_custloc(
            "out-of-line declaration of '" +
                qualified_constructor_name +
                "' does not match any declaration in the target class",
            decl_loc);
    }

    if (matched_ctor_template_decl) {
        remap_out_of_line_constructor_with_parameter_rebinds(
            parsed_ctor,
            matched_ctor_template_rebinds,
            decl_loc);
        if (matched_ctor_template_decl->body != nullptr ||
            matched_ctor_template_decl->has_deferred_inline_body()) {
            error_custloc(
                "redefinition of '" +
                    qualified_constructor_name +
                    "'",
                decl_loc);
        }
        if (matched_ctor_template_decl->is_consteval != parsed_ctor->is_consteval) {
            error_custloc(
                "conflicting consteval specifier for '" +
                    qualified_constructor_name + "'",
                decl_loc);
        }
    }

    CppConstructorDecl* matched_ctor_decl = nullptr;
    if (!matched_ctor_template_decl) {
        matched_ctor_decl =
            const_cast<CppConstructorDecl*>(matched_ctor_state->decl);
        if (!matched_ctor_decl ||
            matched_ctor_decl->body != nullptr ||
            matched_ctor_decl->has_deferred_inline_body() ||
            (matched_ctor_state->symbol && matched_ctor_state->symbol->is_defined)) {
            error_custloc(
                "redefinition of '" +
                    qualified_constructor_name +
                    "'",
                decl_loc);
        }
        if (matched_ctor_decl->is_consteval != parsed_ctor->is_consteval) {
            error_custloc(
                "conflicting consteval specifier for '" +
                    qualified_constructor_name + "'",
                decl_loc);
        }
    }

    register_function_default_arguments(
        matched_ctor_state ? matched_ctor_state->symbol : nullptr,
        parsed_ctor,
        decl_loc);

    auto owner_record_type = owner_record_decl->get_record_type();
    auto parse_deferred_constructor_body_now =
        [&](CppConstructorDecl* ctor_decl) {
            if (!ctor_decl || !ctor_decl->has_deferred_inline_body() ||
                ctor_decl->body) {
                return;
            }

            size_t saved_token_idx = get_token_idx();
            auto saved_func_type = func_type;
            auto saved_decl_linkage = current_language_linkage_;
            auto saved_seen_stmt_labels = seen_stmt_labels;
            auto saved_stmt_labels = stmt_labels;
            auto saved_local_label_scopes = local_label_scopes_;
            uint64_t saved_local_label_unique_id = local_label_unique_id_;

            seen_stmt_labels.clear();
            stmt_labels.clear();
            local_label_scopes_.clear();
            local_label_unique_id_ = 0;

            auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
            auto function_scope = entered_scope.scope;

            Collect::CppThisContext cpp_this_context;
            cpp_this_context.is_member_function = true;
            cpp_this_context.is_static_member_function = false;
            QualType constructor_owner_type = owner_record_lookup_type;
            if (!constructor_owner_type && owner_record_type) {
                constructor_owner_type = QualType(owner_record_type);
            }
            cpp_this_context.access_context_type = constructor_owner_type;
            if (constructor_owner_type) {
                cpp_this_context.this_type = QualType(
                    std::make_shared<PointerType>(constructor_owner_type));
            }

            func_type = ctor_decl->type;
            current_language_linkage_ = LanguageLinkage::None;
            collect_->collect_start_function_definition(
                ctor_decl->name, QualType(ctor_decl->type), cpp_this_context);

            Collect::ImmediateFunctionContextScope immediate_function_context_guard(
                collect_.get(), ctor_decl->is_consteval != 0);

            for (auto& param_decl_base : ctor_decl->parameters) {
                auto* param_decl = dyn_cast<ParamDecl>(param_decl_base.get());
                if (!param_decl || !param_decl->has_name() ||
                    param_decl->get_name() == "this") {
                    continue;
                }
                param_decl->sym = collect_->collect_declare_variable_symbol(
                    param_decl->get_name(),
                    param_decl->type,
                    param_decl->storage_class,
                    false,
                    false,
                    param_decl->location);
            }

            auto parse_deferred_constructor_member_initializers =
                [&](CppConstructorDecl* ctor) {
                if (!ctor) {
                    return;
                }
                size_t saved_idx = get_token_idx();
                bool saw_base_initializer = false;
                bool saw_delegating_initializer = false;
                std::unordered_set<std::string> seen_resolved_initializers;
                auto initializer_display_name =
                    [](const CppCtorInitializer& initializer) -> std::string {
                    if (!initializer.target_spelling.empty()) {
                        return initializer.target_spelling;
                    }
                    return initializer.member_name;
                };
                auto note_resolved_initializer =
                    [&](const std::string& key,
                        const CppCtorInitializer& initializer) {
                    if (initializer.is_pack_expansion) {
                        return;
                    }
                    if (!seen_resolved_initializers.insert(key).second) {
                        diag_engine->report_error(
                            "constructor mem-initializer-list has duplicate initializer '" +
                                initializer_display_name(initializer) + "'",
                            initializer.location);
                    }
                };
                for (auto& mem_init : ctor->ctor_initializers) {
                    mem_init.member_expr.reset();
                    mem_init.init_expr.reset();
                    mem_init.is_base_initializer = false;
                    mem_init.resolved_target_type = nullptr;

                    if (mem_init.is_delegating_initializer) {
                        saw_delegating_initializer = true;
                        note_resolved_initializer("delegating", mem_init);
                        if (ctor->ctor_initializers.size() != 1) {
                            diag_engine->report_error(
                                "delegating constructor initializer must appear alone",
                                mem_init.location);
                        }
                        if (!owner_record_type) {
                            diag_engine->report_error(
                                "delegating constructor target type is unavailable",
                                mem_init.location);
                            continue;
                        }
                        mem_init.resolved_target_type =
                            QualType(owner_record_type);
                        if (mem_init.deferred_init_end_token_idx <=
                            mem_init.deferred_init_begin_token_idx) {
                            continue;
                        }

                        set_token_idx(mem_init.deferred_init_begin_token_idx);
                        std::unique_ptr<Expr> parsed_init;
                        if (gentle_check(TokenType::LEFT_PAREN)) {
                            advance(); // '('
                            std::vector<std::unique_ptr<Expr>> args;
                            if (!gentle_check(TokenType::RIGHT_PAREN)) {
                                do {
                                    args.push_back(
                                        parse_assignment_expression_with_optional_pack_expansion());
                                } while (gentle_check_and_consume(TokenType::COMMA));
                            }
                            check_and_consume(TokenType::RIGHT_PAREN);
                            mem_init.init_expr =
                                collect_->collect_member_initializer_expression(
                                    std::move(args),
                                    QualType(owner_record_type),
                                    false,
                                    mem_init.location,
                                    true);
                        } else if (gentle_check(TokenType::LEFT_BRACE)) {
                            parsed_init = parse_init_list();
                        } else {
                            error("expected '(' or '{' in constructor member initializer");
                        }

                        set_token_idx(mem_init.deferred_init_end_token_idx);
                        if (!mem_init.init_expr && parsed_init) {
                            mem_init.init_expr =
                                collect_->collect_member_initializer_expression(
                                    std::move(parsed_init),
                                    QualType(owner_record_type),
                                    mem_init.location);
                        }
                        continue;
                    }

                    auto base_init_target =
                        resolve_cpp_ctor_base_initializer_target(
                            *owner_state,
                            QualType(owner_record_type),
                            mem_init);
                    if (base_init_target) {
                        saw_base_initializer = true;
                        mem_init.is_base_initializer = true;
                        mem_init.member_name = base_init_target.base_name;
                        mem_init.resolved_target_type = base_init_target.type;
                        note_resolved_initializer(
                            "base:" + base_init_target.type.to_string(),
                            mem_init);
                    } else if (base_init_target.found_non_base_type) {
                        continue;
                    }

                    MemberExpr* member_expr = nullptr;
                    if (!base_init_target) {
                        auto this_expr = collect_->collect_cpp_this_expression(mem_init.location);
                        mem_init.member_expr = collect_->collect_member_expression(
                            std::move(this_expr),
                            mem_init.member_name,
                            true,
                            mem_init.location);
                        member_expr = dyn_cast<MemberExpr>(mem_init.member_expr.get());
                        if (!member_expr || !member_expr->member_type) {
                            continue;
                        }
                        note_resolved_initializer(
                            "member:" + mem_init.member_name,
                            mem_init);
                    }
                    if (mem_init.deferred_init_end_token_idx <=
                        mem_init.deferred_init_begin_token_idx) {
                        continue;
                    }

                    set_token_idx(mem_init.deferred_init_begin_token_idx);
                    std::unique_ptr<Expr> parsed_init;
                    if (gentle_check(TokenType::LEFT_PAREN)) {
                        advance(); // '('
                        std::vector<std::unique_ptr<Expr>> args;
                        if (!gentle_check(TokenType::RIGHT_PAREN)) {
                            do {
                                args.push_back(
                                    parse_assignment_expression_with_optional_pack_expansion());
                            } while (gentle_check_and_consume(TokenType::COMMA));
                        }
                        check_and_consume(TokenType::RIGHT_PAREN);

                        if (base_init_target) {
                            mem_init.init_expr =
                                collect_->collect_member_initializer_expression(
                                    std::move(args),
                                    base_init_target.type,
                                    false,
                                    mem_init.location,
                                    true);
                        } else if (type_depends_on_template_parameters(
                                       member_expr->member_type,
                                       ast_ctx.get()) ||
                                   canonical_type_kind(member_expr->member_type) ==
                                       TypeKind::Object ||
                                   args.empty()) {
                            mem_init.init_expr =
                                collect_->collect_member_initializer_expression(
                                    std::move(args),
                                    member_expr->member_type,
                                    false,
                                    mem_init.location);
                        } else if (args.size() > 1) {
                            diag_engine->report_error(
                                "constructor member initializer for non-class member '" +
                                    mem_init.member_name +
                                    "' requires a single expression",
                                mem_init.location);
                        } else {
                            parsed_init = std::move(args.front());
                        }
                    } else if (gentle_check(TokenType::LEFT_BRACE)) {
                        parsed_init = parse_init_list();
                    } else {
                        error("expected '(' or '{' in constructor member initializer");
                    }

                    set_token_idx(mem_init.deferred_init_end_token_idx);
                    if (mem_init.init_expr) {
                        continue;
                    }
                    if (!parsed_init) {
                        continue;
                    }
                    if (base_init_target) {
                        mem_init.init_expr =
                            collect_->collect_member_initializer_expression(
                                std::move(parsed_init),
                                base_init_target.type,
                                mem_init.location);
                    } else if (canonical_type_kind(member_expr->member_type) ==
                        TypeKind::Reference) {
                        mem_init.init_expr = std::move(parsed_init);
                    } else {
                        mem_init.init_expr = collect_->collect_member_initializer_expression(
                            std::move(parsed_init),
                            member_expr->member_type,
                            mem_init.location);
                    }
                }

                if (!saw_delegating_initializer &&
                    !saw_base_initializer &&
                    owner_state->bases.size() == 1) {
                    const auto& direct_base = owner_state->bases.front();
                    if (direct_base.type &&
                        canonical_type_kind(direct_base.type) == TypeKind::Object) {
                        CppCtorInitializer implicit_base_init;
                        implicit_base_init.member_name = direct_base.name;
                        implicit_base_init.target_spelling = direct_base.name;
                        implicit_base_init.target_type = direct_base.type;
                        implicit_base_init.resolved_target_type = direct_base.type;
                        implicit_base_init.is_base_initializer = true;
                        implicit_base_init.location = ctor->location;
                        std::vector<std::unique_ptr<Expr>> args;
                        implicit_base_init.init_expr =
                            collect_->collect_member_initializer_expression(
                                std::move(args),
                                direct_base.type,
                                false,
                                ctor->location,
                                true);
                        ctor->ctor_initializers.insert(
                            ctor->ctor_initializers.begin(),
                            std::move(implicit_base_init));
                    }
                }
                set_token_idx(saved_idx);
            };

            cxx_record_parse_stack_.push_back(
                CppRecordParseFrame{CppRecordKind::Class, owner_name});
            RecordParseScopeGuard<decltype(cxx_record_parse_stack_)>
                nested_record_parse_scope_guard{&cxx_record_parse_stack_};

            try {
                parse_deferred_constructor_member_initializers(ctor_decl);
                set_token_idx(ctor_decl->deferred_inline_body_begin_token_idx);
                if (gentle_check(TokenType::TRY_KW)) {
                    auto try_stmt = parse_cpp_try_statement(
                        function_scope, true);
                    SrcLoc body_loc = try_stmt ? try_stmt->location : SrcLoc();
                    std::vector<std::unique_ptr<Stmt>> stmts;
                    stmts.push_back(std::move(try_stmt));
                    ctor_decl->body = collect_->collect_compound_statement(
                        std::move(stmts), function_scope, body_loc);
                } else {
                    ctor_decl->body = parse_compound_stmt(function_scope);
                }
                ctor_decl->scope = function_scope;
                ctor_decl->stmt_labels.insert(
                    stmt_labels.begin(), stmt_labels.end());
                set_token_idx(ctor_decl->deferred_inline_body_end_token_idx);
                ctor_decl->clear_deferred_inline_body_token_range();
                collect_->collect_leave_scope();
                collect_->collect_finish_function_definition(function_scope);
            } catch (...) {
                collect_->collect_abort_function_definition();
                collect_->collect_leave_scope();
                current_language_linkage_ = saved_decl_linkage;
                func_type = saved_func_type;
                set_token_idx(saved_token_idx);
                seen_stmt_labels = std::move(saved_seen_stmt_labels);
                stmt_labels = std::move(saved_stmt_labels);
                local_label_scopes_ = std::move(saved_local_label_scopes);
                local_label_unique_id_ = saved_local_label_unique_id;
                throw;
            }

            current_language_linkage_ = saved_decl_linkage;
            func_type = saved_func_type;
            set_token_idx(saved_token_idx);
            seen_stmt_labels = std::move(saved_seen_stmt_labels);
            stmt_labels = std::move(saved_stmt_labels);
            local_label_scopes_ = std::move(saved_local_label_scopes);
            local_label_unique_id_ = saved_local_label_unique_id;
        };

    parse_deferred_constructor_body_now(parsed_ctor);
    if (matched_ctor_template_decl) {
        merge_out_of_line_constructor_template_definition(
            matched_ctor_template_decl,
            parsed_ctor,
            ast_ctx);
    } else {
        merge_out_of_line_constructor_definition(
            matched_ctor_decl,
            parsed_ctor,
            matched_ctor_state,
            matched_ctor_state->symbol,
            ast_ctx,
            owner_record_decl);
    }

    parsed_decls.push_back(collect_->collect_nop_declaration(decl_loc));
    return parsed_decls;
}

std::vector<std::unique_ptr<Decl>> Parser::parse_cpp_out_of_line_destructor_definition() {
    std::vector<std::unique_ptr<Decl>> parsed_decls;
    if (!is_cxx_mode_active() ||
        !is_cpp_out_of_line_destructor_declaration_start()) {
        return parsed_decls;
    }

    SrcLoc decl_loc = current_token().loc;
    if (gentle_check(TokenType::CONSTEVAL_KW)) {
        error_custloc("destructor cannot be consteval", current_token().loc);
    }
    bool has_global_qualifier = consume_cpp_scope_resolution();
    std::vector<CppQualifiedNameComponent> owner_components;

    if (!gentle_check(TokenType::IDENTIFIER)) {
        error_custloc("expected identifier in out-of-line destructor definition",
                      current_token().loc);
    }

    auto parse_component =
        [&]() -> CppQualifiedNameComponent {
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected identifier after '::' in out-of-line destructor definition",
                    current_token().loc);
            }
            CppQualifiedNameComponent component;
            component.name = current_token().value;
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                component.has_template_argument_list = true;
                component.template_arguments = parse_cpp_template_argument_list();
            }
            return component;
        };

    while (true) {
        owner_components.push_back(parse_component());
        if (!is_cpp_scope_resolution_here()) {
            error_custloc(
                "expected '::' in out-of-line destructor definition",
                current_token().loc);
        }
        consume_cpp_scope_resolution();
        if (gentle_check(TokenType::BITWISE_NOT)) {
            break;
        }
    }

    if (owner_components.empty()) {
        error_custloc("expected qualified destructor name", decl_loc);
    }
    const auto& owner_component = owner_components.back();
    const std::string& owner_name = owner_component.name;
    std::vector<std::string> namespace_qualifiers;
    namespace_qualifiers.reserve(owner_components.size() - 1);
    for (size_t idx = 0; idx + 1 < owner_components.size(); ++idx) {
        if (owner_components[idx].has_template_argument_list) {
            fail_cpp_future_work(
                "template-id nested-name specifier",
                "template-id qualifier chains",
                decl_loc);
        }
        namespace_qualifiers.push_back(owner_components[idx].name);
    }
    std::string qualified_owner_name = qualified_name_utils::format_cpp_qualified_name(
        has_global_qualifier,
        namespace_qualifiers,
        owner_component.spelling());
    std::vector<std::string> qualified_owner_components = namespace_qualifiers;
    qualified_owner_components.push_back(owner_component.spelling());
    std::string qualified_destructor_name = qualified_name_utils::format_cpp_qualified_name(
        has_global_qualifier,
        qualified_owner_components,
        "~" + owner_name);

    const size_t destructor_token_idx = get_token_idx();
    if (!gentle_check(TokenType::BITWISE_NOT)) {
        error_custloc("expected '~' in out-of-line destructor definition",
                      current_token().loc);
    }
    advance(); // '~'
    if (!gentle_check(TokenType::IDENTIFIER) ||
        current_token().value != owner_name) {
        error_custloc("expected destructor name '~" + owner_name + "'",
                      current_token().loc);
    }
    auto current_scope = collect_->collect_current_scope();
    auto translation_unit_context = collect_->get_translation_unit_decl_context();
    auto current_context = collect_->get_current_decl_context();
    if (!current_scope || !translation_unit_context || !current_context) {
        error_custloc("internal error: missing scope context for destructor definition",
                      decl_loc);
    }
    auto global_scope = current_scope;
    while (global_scope && global_scope->parent) {
        global_scope = global_scope->parent;
    }
    if (!global_scope) {
        error_custloc("internal error: missing global scope for destructor definition",
                      decl_loc);
    }

    auto owner_namespace_scope = has_global_qualifier ? global_scope : current_scope;
    std::shared_ptr<DeclContext> owner_namespace_context =
        has_global_qualifier ? translation_unit_context : current_context;
    for (size_t idx = 0; idx < namespace_qualifiers.size(); ++idx) {
        bool allow_enclosing_lookup = (!has_global_qualifier && idx == 0);
        auto resolved = resolve_named_namespace_scope(
            owner_namespace_context.get(),
            namespace_qualifiers[idx],
            allow_enclosing_lookup);
        if (!resolved || !resolved->associated_decl_context) {
            error_custloc(
                "out-of-line declaration of '" +
                    qualified_destructor_name +
                    "' does not match any declaration in the target class",
                decl_loc);
        }
        owner_namespace_scope = resolved;
        owner_namespace_context = std::shared_ptr<DeclContext>(
            owner_namespace_context,
            resolved->associated_decl_context);
    }

    auto saved_scope = collect_->collect_current_scope();
    auto saved_context = collect_->get_current_decl_context();
    ScopeRestoreGuard scope_restore_guard{
        collect_.get(),
        saved_scope,
        saved_context
    };

    const ObjectDecl* owner_record_decl = nullptr;
    const ClassTemplateDecl* owner_class_template = nullptr;
    QualType owner_current_instantiation_type = nullptr;
    bool allow_owner_enclosing_lookup =
        !has_global_qualifier && namespace_qualifiers.empty();
    if (owner_component.has_template_argument_list) {
        const DeclBinding* template_binding =
            LookupEngine::lookup_unqualified_template_binding(
                owner_component.name,
                owner_namespace_scope,
                allow_owner_enclosing_lookup,
                LookupNamespace::Tag);
        const Decl* primary_template = nullptr;
        if (template_binding) {
            primary_template = template_binding->template_decl;
            if (!primary_template &&
                template_binding->template_overload_candidates.size() == 1) {
                primary_template =
                    template_binding->template_overload_candidates.front();
            }
        }
        auto* class_template = dyn_cast<ClassTemplateDecl>(primary_template);
        if (!class_template ||
            !cpp_primary_template_owner_matches(
                class_template,
                owner_component.template_arguments)) {
            error_custloc(
                "out-of-line declaration of '" +
                    qualified_destructor_name +
                    "' does not match any declaration in the target class",
                decl_loc);
        }
        owner_class_template = class_template;
        owner_record_decl = class_template->pattern_semantic_decl();
        owner_current_instantiation_type =
            build_cpp_current_instantiation_type(
                owner_class_template,
                owner_name,
                owner_component.template_arguments);
    } else {
        auto* owner_tag_decl = LookupEngine::lookup_tag_decl(
            owner_name,
            owner_namespace_scope,
            allow_owner_enclosing_lookup);
        const ObjectDecl* owner_record = dyn_cast<ObjectDecl>(owner_tag_decl);
        if (owner_record && owner_record->get_record_type()) {
            if (auto* canonical_owner =
                    dyn_cast<ObjectDecl>(
                        owner_record->get_record_type()->get_decl())) {
                owner_record = canonical_owner;
            }
        }
        owner_record_decl = owner_record;
    }
    if (!owner_record_decl) {
        error_custloc(
            "out-of-line declaration of '" +
                qualified_destructor_name +
                "' does not match any declaration in the target class",
            decl_loc);
    }
    const RecordSemanticState* owner_state =
        collect_->query_lookup_record_semantics(owner_record_decl);
    if (!owner_state || owner_state->is_incomplete) {
        error_custloc(
            "incomplete type '" + qualified_owner_name +
                "' named in nested name specifier",
            decl_loc);
    }

    if (saved_scope &&
        scope_flags_contains(saved_scope->flags, ScopeFlags::TemplateParameterScope) &&
        saved_context) {
        auto rebased_scope = std::make_shared<Scope>(*saved_scope);
        rebased_scope->parent = owner_namespace_scope;
        rebased_scope->associated_decl_context = saved_context.get();
        collect_->collect_set_current_scope(std::move(rebased_scope));
        collect_->set_current_decl_context(saved_context);
    } else {
        collect_->collect_set_current_scope(owner_namespace_scope);
        collect_->set_current_decl_context(owner_namespace_context);
    }

    set_token_idx(destructor_token_idx);
    QualType previous_record_lookup_type =
        collect_ ? collect_->collect_current_cpp_record_lookup_type()
                 : QualType();
    struct OutOfLineRecordLookupGuard {
        Collect* collect = nullptr;
        QualType previous_type = nullptr;
        ~OutOfLineRecordLookupGuard() {
            if (collect) {
                collect->collect_set_current_cpp_record_lookup_type(previous_type);
            }
        }
    } record_lookup_guard{collect_.get(), previous_record_lookup_type};
    QualType owner_record_lookup_type = owner_current_instantiation_type;
    if (!owner_record_lookup_type && owner_record_decl->get_record_type()) {
        owner_record_lookup_type =
            QualType(owner_record_decl->get_record_type());
    }
    if (collect_ && owner_record_lookup_type) {
        collect_->collect_set_current_cpp_record_lookup_type(
            owner_record_lookup_type);
    }
    cxx_record_parse_stack_.push_back(
        CppRecordParseFrame{
            owner_record_decl->is_union ? CppRecordKind::Union : CppRecordKind::Class,
            owner_name,
            owner_record_decl,
            owner_class_template,
            owner_current_instantiation_type});
    RecordParseScopeGuard<decltype(cxx_record_parse_stack_)>
        record_parse_scope_guard{&cxx_record_parse_stack_};

    auto parsed_member = parse_cpp_destructor_member();
    auto* parsed_dtor = dyn_cast<CppDestructorDecl>(parsed_member.get());
    if (!parsed_dtor) {
        error_custloc(
            "internal error: failed to parse out-of-line destructor definition",
            decl_loc);
    }
    bool parsed_is_definition =
        parsed_dtor->body != nullptr ||
        parsed_dtor->has_deferred_inline_body() ||
        parsed_dtor->is_deleted ||
        parsed_dtor->is_defaulted;
    if (!parsed_is_definition) {
        error_custloc(
            "out-of-line declaration of '" +
                qualified_destructor_name +
                "' must be a definition",
            decl_loc);
    }

    const RecordSemanticState::Destructor* matched_dtor_state = nullptr;
    QualType parsed_dtor_type = desugar_type(QualType(parsed_dtor->type));
    for (const auto& dtor : owner_state->destructors) {
        if (!dtor.type) {
            continue;
        }
        QualType candidate_type = desugar_type(dtor.type);
        if (!cpp_out_of_line_type_matches(candidate_type, parsed_dtor_type, true)) {
            continue;
        }
        matched_dtor_state = &dtor;
        break;
    }
    if (!matched_dtor_state || !matched_dtor_state->decl) {
        error_custloc(
            "out-of-line declaration of '" +
                qualified_destructor_name +
                "' does not match any declaration in the target class",
            decl_loc);
    }

    auto* matched_dtor_decl =
        const_cast<CppDestructorDecl*>(matched_dtor_state->decl);
    if (!matched_dtor_decl ||
        matched_dtor_decl->body != nullptr ||
        matched_dtor_decl->has_deferred_inline_body() ||
        (matched_dtor_state->symbol && matched_dtor_state->symbol->is_defined)) {
        error_custloc(
            "redefinition of '" +
                qualified_destructor_name +
                "'",
            decl_loc);
    }

    auto owner_record_type = owner_record_decl->get_record_type();
    auto parse_deferred_destructor_body_now =
        [&](CppDestructorDecl* dtor_decl) {
            if (!dtor_decl || !dtor_decl->has_deferred_inline_body() ||
                dtor_decl->body) {
                return;
            }

            size_t saved_token_idx = get_token_idx();
            auto saved_func_type = func_type;
            auto saved_decl_linkage = current_language_linkage_;
            auto saved_seen_stmt_labels = seen_stmt_labels;
            auto saved_stmt_labels = stmt_labels;
            auto saved_local_label_scopes = local_label_scopes_;
            uint64_t saved_local_label_unique_id = local_label_unique_id_;

            seen_stmt_labels.clear();
            stmt_labels.clear();
            local_label_scopes_.clear();
            local_label_unique_id_ = 0;

            auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
            auto function_scope = entered_scope.scope;

            Collect::CppThisContext cpp_this_context;
            cpp_this_context.is_member_function = true;
            cpp_this_context.is_static_member_function = false;
            auto dtor_fn_type = dyn_cast_shared<FunctionType>(dtor_decl->type);
            if (dtor_fn_type && !dtor_fn_type->parameters.empty()) {
                cpp_this_context.this_type = dtor_fn_type->parameters.front();
            }
            if (!cpp_this_context.this_type && owner_record_type) {
                cpp_this_context.this_type = QualType(
                    std::make_shared<PointerType>(QualType(owner_record_type)));
            }

            func_type = dtor_decl->type;
            current_language_linkage_ = LanguageLinkage::None;
            collect_->collect_start_function_definition(
                dtor_decl->name, QualType(dtor_decl->type), cpp_this_context);

            for (auto& param_decl_base : dtor_decl->parameters) {
                auto* param_decl = dyn_cast<ParamDecl>(param_decl_base.get());
                if (!param_decl || !param_decl->has_name() ||
                    param_decl->get_name() == "this") {
                    continue;
                }
                param_decl->sym = collect_->collect_declare_variable_symbol(
                    param_decl->get_name(),
                    param_decl->type,
                    param_decl->storage_class,
                    false,
                    false,
                    param_decl->location);
            }

            cxx_record_parse_stack_.push_back(
                CppRecordParseFrame{CppRecordKind::Class, owner_name});
            RecordParseScopeGuard<decltype(cxx_record_parse_stack_)>
                nested_record_parse_scope_guard{&cxx_record_parse_stack_};

            try {
                set_token_idx(dtor_decl->deferred_inline_body_begin_token_idx);
                if (gentle_check(TokenType::TRY_KW)) {
                    auto try_stmt = parse_cpp_try_statement(function_scope);
                    SrcLoc body_loc = try_stmt ? try_stmt->location : SrcLoc();
                    std::vector<std::unique_ptr<Stmt>> stmts;
                    stmts.push_back(std::move(try_stmt));
                    dtor_decl->body = collect_->collect_compound_statement(
                        std::move(stmts), function_scope, body_loc);
                } else {
                    dtor_decl->body = parse_compound_stmt(function_scope);
                }
                dtor_decl->scope = function_scope;
                dtor_decl->stmt_labels.insert(
                    stmt_labels.begin(), stmt_labels.end());
                set_token_idx(dtor_decl->deferred_inline_body_end_token_idx);
                dtor_decl->clear_deferred_inline_body_token_range();
                collect_->collect_leave_scope();
                collect_->collect_finish_function_definition(function_scope);
            } catch (...) {
                collect_->collect_abort_function_definition();
                collect_->collect_leave_scope();
                current_language_linkage_ = saved_decl_linkage;
                func_type = saved_func_type;
                set_token_idx(saved_token_idx);
                seen_stmt_labels = std::move(saved_seen_stmt_labels);
                stmt_labels = std::move(saved_stmt_labels);
                local_label_scopes_ = std::move(saved_local_label_scopes);
                local_label_unique_id_ = saved_local_label_unique_id;
                throw;
            }

            current_language_linkage_ = saved_decl_linkage;
            func_type = saved_func_type;
            set_token_idx(saved_token_idx);
            seen_stmt_labels = std::move(saved_seen_stmt_labels);
            stmt_labels = std::move(saved_stmt_labels);
            local_label_scopes_ = std::move(saved_local_label_scopes);
            local_label_unique_id_ = saved_local_label_unique_id;
        };

    parse_deferred_destructor_body_now(parsed_dtor);

    matched_dtor_decl->parameters = std::move(parsed_dtor->parameters);
    matched_dtor_decl->type = parsed_dtor->type;
    matched_dtor_decl->body = std::move(parsed_dtor->body);
    matched_dtor_decl->scope = parsed_dtor->scope;
    matched_dtor_decl->stmt_labels = std::move(parsed_dtor->stmt_labels);
    matched_dtor_decl->is_deleted = parsed_dtor->is_deleted;
    matched_dtor_decl->is_defaulted = parsed_dtor->is_defaulted;
    matched_dtor_decl->is_defaulted_on_first_declaration = false;
    matched_dtor_decl->is_override = parsed_dtor->is_override;
    matched_dtor_decl->is_final = parsed_dtor->is_final;
    matched_dtor_decl->is_pure = parsed_dtor->is_pure;
    matched_dtor_decl->is_constexpr = parsed_dtor->is_constexpr;
    matched_dtor_decl->set_language_linkage(parsed_dtor->get_language_linkage());
    if (parsed_dtor->asm_label) {
        matched_dtor_decl->set_asm_label(*parsed_dtor->asm_label);
    } else {
        matched_dtor_decl->clear_asm_label();
    }
    matched_dtor_decl->clear_deferred_inline_body_token_range();
    adopt_out_of_line_member_qualifier_prefix(matched_dtor_decl, parsed_dtor);

    const auto& parsed_attrs = ast_ctx->get_attrs(parsed_dtor->node_id).attrs;
    if (!parsed_attrs.empty()) {
        auto& dst_attrs = ast_ctx->get_attrs_mut(matched_dtor_decl->node_id).attrs;
        dst_attrs.insert(dst_attrs.end(), parsed_attrs.begin(), parsed_attrs.end());
    }

    auto matched_symbol = matched_dtor_state->symbol;
    if (matched_symbol) {
        matched_symbol->is_defined = true;
        matched_symbol->is_deleted = matched_dtor_decl->is_deleted;
        matched_symbol->is_defaulted = matched_dtor_decl->is_defaulted;
        matched_symbol->type = QualType(matched_dtor_decl->type);
        matched_symbol->function_definition = matched_dtor_decl;
    }

    RecordSemanticState updated_state = *owner_state;
    for (auto& dtor : updated_state.destructors) {
        if (dtor.decl != matched_dtor_state->decl) {
            continue;
        }
        dtor.decl = matched_dtor_decl;
        dtor.type = QualType(matched_dtor_decl->type);
        dtor.is_implicit = false;
        dtor.is_defaulted = matched_dtor_decl->is_defaulted;
        dtor.is_deleted = matched_dtor_decl->is_deleted;
        dtor.is_constexpr = matched_dtor_decl->is_constexpr;
        dtor.is_override = matched_dtor_decl->is_override;
        dtor.is_final = matched_dtor_decl->is_final;
        dtor.is_pure = matched_dtor_decl->is_pure;
        if (matched_symbol) {
            dtor.symbol = matched_symbol;
        }
        break;
    }
    updated_state.definition_data.has_user_declared_destructor = true;
    updated_state.definition_data.has_deleted_destructor = false;
    for (const auto& dtor : updated_state.destructors) {
        if (dtor.is_deleted) {
            updated_state.definition_data.has_deleted_destructor = true;
            break;
        }
    }
    collect_->query_publish_record_semantics(owner_record_decl,
                                             std::move(updated_state));

    parsed_decls.push_back(collect_->collect_nop_declaration(decl_loc));
    return parsed_decls;
}
