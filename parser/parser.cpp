#include "parser.h"

#include "../builtin_registry.h"

#include <algorithm>
#include <span>
#include <utility>
#include <vector>

namespace aburi::syntax {

namespace {

bool is_parser_trivia(TokenType type) {
    return type == TokenType::Whitespace || type == TokenType::Newline;
}

} // namespace

Parser::Parser(const std::vector<Token>& tokens,
               LangOptions lang_opts,
               std::shared_ptr<SourceManager> source_manager,
               collect::Session& collect_session)
    : tokens_(tokens),
      lang_opts_(std::move(lang_opts)),
      source_manager_(std::move(source_manager)),
      collect_session_(collect_session) {
    cooked_to_raw_.reserve(tokens_.size());
    for (size_t raw = 0; raw < tokens_.size(); ++raw) {
        if (!is_parser_trivia(tokens_[raw].type)) {
            cooked_to_raw_.push_back(raw);
        }
    }
}

bool Parser::should_defer_complete_class_region() const {
    const cir::File& file = collect_session_.file();
    cir::DeclContextId context = collect_session_.current_decl_context();
    while (context.valid() && file.valid(context)) {
        const cir::DeclContext& declaration = file.decl_context(context);
        if (declaration.kind == cir::DeclContextKind::Record &&
            declaration.owner.valid() && file.valid(declaration.owner)) {
            const cir::RecordFacts* facts =
                file.record_facts(declaration.owner);
            return !facts || facts->is_incomplete;
        }
        context = declaration.parent;
    }
    return false;
}

ParseResult Parser::parse_translation_unit() {
    auto previous_function_template_callback =
        collect_session_.set_function_template_instantiation_callback(
            [this](const collect::Session::TemplateInfo& info,
                   const collect::Session::TemplateArgumentBindings&
                       argument_bindings,
                   SrcLoc loc) {

                if (Parser* owner = module_unit_parser_for(info.entity)) {
                    ConstraintSubstitutionFailureIsolation candidate_failure(
                        *owner);
                    collect::Session::ModuleVisibilityOverride visibility(
                        collect_session_,
                        collect_session_.file().entity(info.entity).origin_unit);
                    return owner->form_function_template_candidate(info,
                                                                   argument_bindings,
                                                                   loc);
                }
                ConstraintSubstitutionFailureIsolation candidate_failure(
                    *this);
                return form_function_template_candidate(
                    info, argument_bindings, loc);
            });
    auto previous_pattern_callback_configurator =
        collect_session_.set_pattern_instantiation_callback_configurator(
            [this](collect::Session::PatternInstantiationCallbacks& callbacks,
                   SrcLoc loc) {
                configure_pattern_instantiation_callbacks(callbacks, loc);
            });
    auto previous_class_placeholder_deduction_callback =
        collect_session_.set_class_template_placeholder_deduction_callback(
            [this](const collect::Session::TemplateInfo& info,
                   const collect::ExprResult& source,
                   SrcLoc loc,
                   bool preserve_diagnostics) {
                Parser* target = this;
                if (Parser* owner = module_unit_parser_for(info.entity)) {
                    target = owner;
                }
                size_t diagnostic_begin = target->diagnostics_.size();
                cir::TypeId result{};
                if (target != this) {
                    collect::Session::ModuleVisibilityOverride visibility(
                        collect_session_,
                        collect_session_.file().entity(info.entity)
                            .origin_unit);
                    result =
                        target->deduce_class_template_initialization_type(
                            info,
                            std::vector<collect::ExprResult>{source},
                            loc,
                            CtadInitializationKind::Copy);
                } else {
                    result = deduce_class_template_initialization_type(
                        info,
                        std::vector<collect::ExprResult>{source},
                        loc,
                        CtadInitializationKind::Copy);
                }
                if (preserve_diagnostics && target != this) {
                    diagnostics_.insert(
                        diagnostics_.end(),
                        std::make_move_iterator(
                            target->diagnostics_.begin() +
                            static_cast<std::ptrdiff_t>(diagnostic_begin)),
                        std::make_move_iterator(
                            target->diagnostics_.end()));
                }
                if (!preserve_diagnostics || target != this) {
                    target->diagnostics_.resize(diagnostic_begin);
                }
                return result;
            });
    auto previous_class_demand_callback =
        collect_session_.set_class_instantiation_demand_callback(
            [this](cir::EntityId specialization,
                   cir::InstantiationDemandKind kind,
                   cir::EntityId subject,
                   SrcLoc loc) {
                cir::EntityId pattern =
                    module_pattern_identity(specialization);
                if (Parser* owner = module_unit_parser_for(pattern)) {
                    collect::Session::ModuleVisibilityOverride visibility(
                        collect_session_,
                        collect_session_.file().entity(pattern).origin_unit);
                    return owner->materialize_class_demand(specialization,
                                                           kind, subject, loc);
                }
                return materialize_class_demand(specialization,
                                                kind,
                                                subject,
                                                loc);
            });
    auto previous_function_demand_callback =
        collect_session_.set_function_instantiation_demand_callback(
            [this](cir::EntityId specialization,
                   cir::InstantiationDemandKind kind,
                   SrcLoc loc) {
                cir::EntityId pattern =
                    module_pattern_identity(specialization);
                if (Parser* owner = module_unit_parser_for(pattern)) {
                    collect::Session::ModuleVisibilityOverride visibility(
                        collect_session_,
                        collect_session_.file().entity(pattern).origin_unit);
                    return owner->materialize_function_demand(specialization,
                                                              kind, loc);
                }
                return materialize_function_demand(specialization, kind, loc);
            });
    auto previous_default_argument_callback =
        collect_session_.set_default_argument_replay_callback(
            [this](cir::EntityId selected, size_t parameter_index, SrcLoc loc) {
                return routed_default_argument_replay(selected,
                                                      parameter_index, loc);
            });
    auto previous_dmi_callback =
        collect_session_.set_default_member_initializer_replay_callback(
            [this](cir::EntityId field, cir::InstId object_place, SrcLoc loc) {
                if (Parser* owner = module_unit_parser_for(field)) {
                    collect::Session::ModuleVisibilityOverride visibility(
                        collect_session_,
                        collect_session_.file().entity(field).origin_unit);
                    return owner->replay_default_member_initializer(
                        field, object_place, loc);
                }
                return replay_default_member_initializer(field, object_place,
                                                         loc);
            });
    auto previous_coroutine_promise_callback =
        collect_session_.set_coroutine_promise_callback(
            [this](const std::vector<cir::TypeRef>& traits_arguments,
                   SrcLoc loc) {
                return resolve_coroutine_promise_type(traits_arguments, loc);
            });
    auto previous_module_replay_callback =
        collect_session_.set_module_unit_replay_callback(
            [this](const std::vector<Token>& tokens) {
                auto replay = std::make_unique<Parser>(
                    tokens, lang_opts_, source_manager_, collect_session_);
                replay->module_parser_registry_ = module_parser_registry_;
                ParseResult replayed = replay->parse_module_unit();
                bool replay_ok = true;
                for (Diagnostic& diag : replayed.diagnostics) {
                    if (diag.level == DiagnosticLevel::Error) {
                        replay_ok = false;
                    }
                    diagnostics_.push_back(std::move(diag));
                }

                cir::ModuleAttachmentId unit =
                    collect_session_.current_module_unit();
                if (unit.valid()) {
                    replay->module_replay_unit_ = unit;
                    module_parser_registry_->by_unit_index[unit.index] = {
                        replay.get(), unit};
                }
                module_parser_registry_->owned.push_back(std::move(replay));
                return replay_ok;
            });
    auto previous_module_register_callback =
        collect_session_.set_module_unit_register_callback(
            [this](const std::vector<Token>& tokens,
                   cir::ModuleAttachmentId unit) {

                auto adopted = std::make_unique<Parser>(
                    tokens, lang_opts_, source_manager_, collect_session_);
                adopted->module_parser_registry_ = module_parser_registry_;
                adopted->module_unit_replay_ = true;
                adopted->module_replay_unit_ = unit;

                for (const auto& [body_key, captured] :
                     collect_session_.captured_member_bodies_for_unit(
                         unit)) {
                    PendingMemberBody hydrated;
                    hydrated.method_index = captured->method_index;
                    hydrated.body_begin = captured->body_begin;
                    hydrated.body_end = captured->body_end;
                    hydrated.init_begin = captured->init_begin;
                    hydrated.init_end = captured->init_end;
                    hydrated.is_constructor_function_try =
                        captured->is_constructor_function_try;
                    for (const collect::Session::CapturedMemberParam&
                             durable : captured->params) {
                        ParsedParam param;
                        param.syntax = InvalidNodeId;
                        param.name = durable.name;
                        param.type = durable.type;
                        param.type_ref = durable.type_ref;
                        param.loc = durable.loc;
                        param.attrs = durable.attrs;
                        param.has_default_argument =
                            durable.has_default_argument;
                        param.default_argument_begin =
                            durable.default_argument_begin;
                        param.default_argument_end =
                            durable.default_argument_end;
                        param.default_argument_loc =
                            durable.default_argument_loc;
                        param.prototype_entity = {};
                        param.is_parameter_pack = durable.is_parameter_pack;
                        param.source_parameter_pack_name =
                            durable.source_parameter_pack_name;
                        param.is_parameter_pack_expansion_sentinel =
                            durable.is_parameter_pack_expansion_sentinel;
                        param.type_originates_from_template_parameter =
                            durable.type_originates_from_template_parameter;
                        param.default_argument_declaration_context =
                            durable.default_argument_declaration_context;
                        param.default_argument_lookup_generation =
                            durable.default_argument_lookup_generation;
                        param.default_argument_requires_complete_class_replay =
                            durable
                                .default_argument_requires_complete_class_replay;
                        hydrated.params.push_back(std::move(param));
                    }
                    adopted->member_template_bodies_[body_key] =
                        std::move(hydrated);
                }
                if (unit.valid()) {
                    module_parser_registry_->by_unit_index[unit.index] = {
                        adopted.get(), unit};
                }
                module_parser_registry_->owned.push_back(std::move(adopted));
            });
    struct CallbackRestore {
        collect::Session& session;
        collect::Session::FunctionTemplateInstantiationCallback function_callback;
        collect::Session::PatternInstantiationCallbackConfigurator
            pattern_callback_configurator;
        collect::Session::ClassTemplatePlaceholderDeductionCallback
            class_placeholder_deduction_callback;
        collect::Session::ClassInstantiationDemandCallback class_demand_callback;
        collect::Session::FunctionInstantiationDemandCallback
            function_demand_callback;
        collect::Session::DefaultArgumentReplayCallback default_argument_callback;
        collect::Session::DefaultMemberInitializerReplayCallback dmi_callback;
        collect::Session::CoroutinePromiseCallback coroutine_promise_callback;
        collect::Session::ModuleUnitReplayCallback module_replay_callback;
        collect::Session::ModuleUnitRegisterCallback module_register_callback;
        ~CallbackRestore() {
            session.set_function_template_instantiation_callback(
                std::move(function_callback));
            session.set_pattern_instantiation_callback_configurator(
                std::move(pattern_callback_configurator));
            session.set_class_template_placeholder_deduction_callback(
                std::move(class_placeholder_deduction_callback));
            session.set_class_instantiation_demand_callback(
                std::move(class_demand_callback));
            session.set_function_instantiation_demand_callback(
                std::move(function_demand_callback));
            session.set_default_argument_replay_callback(
                std::move(default_argument_callback));
            session.set_default_member_initializer_replay_callback(
                std::move(dmi_callback));
            session.set_coroutine_promise_callback(
                std::move(coroutine_promise_callback));
            session.set_module_unit_replay_callback(
                std::move(module_replay_callback));
            session.set_module_unit_register_callback(
                std::move(module_register_callback));
        }
    } restore_callback{collect_session_,
                       std::move(previous_function_template_callback),
                       std::move(previous_pattern_callback_configurator),
                       std::move(
                           previous_class_placeholder_deduction_callback),
                       std::move(previous_class_demand_callback),
                       std::move(previous_function_demand_callback),
                       std::move(previous_default_argument_callback),
                       std::move(previous_dmi_callback),
                       std::move(previous_coroutine_promise_callback),
                       std::move(previous_module_replay_callback),
                       std::move(previous_module_register_callback)};

    std::vector<NodeId> decls;
    size_t begin = current_raw_index();
    if (lang_opts_.is_cxx_mode()) {
        parse_module_preamble(decls);
    }
    while (!at_end()) {

        apply_visibility_directives(false);
        size_t before = mark();
        ParsedDecl decl = parse_external_declaration();
        decls.push_back(decl.syntax);
        if (!made_progress(before)) {
            size_t error_begin = current_raw_index();
            decls.push_back(parse_error_node("parser made no progress", error_begin, error_begin + 1));
            consume();
        }
        apply_weak_directives(false);
        if (lang_opts_.is_cxx_mode() &&
            !collect_session_.is_instantiating()) {

            replay_ready_complete_class_records();
        }
    }
    if (lang_opts_.is_cxx_mode() && !module_unit_replay_) {

        collect_session_.finish_global_initialization();
        collect_session_.finalize_name_linkage();
        replay_referenced_template_members();

        if (!module_parser_registry_->by_unit_index.empty()) {
            for (auto& [unit_index, entry] :
                 module_parser_registry_->by_unit_index) {
                collect::Session::ModuleVisibilityOverride visibility(
                    collect_session_, entry.unit);
                entry.parser->replay_referenced_template_members();
            }
            replay_referenced_template_members();
        }

        collect_session_.finalize_name_linkage();
    }
    apply_weak_directives(true);

    for (const auto& [body_key, body] : member_template_bodies_) {
        collect::Session::CapturedMemberBody captured;
        captured.method_index = body.method_index;
        captured.body_begin = body.body_begin;
        captured.body_end = body.body_end;
        captured.init_begin = body.init_begin;
        captured.init_end = body.init_end;
        captured.is_constructor_function_try =
            body.is_constructor_function_try;
        for (const ParsedParam& param : body.params) {
            if (!param.vla_bounds.empty()) {
                captured.transferable = false;
            }
            for (const auto& constraint :
                 param.abbreviated_type_constraints) {
                if (constraint.has_value()) {
                    captured.transferable = false;
                }
            }
            collect::Session::CapturedMemberParam durable;
            durable.name = param.name;
            durable.type = param.type;
            durable.type_ref = param.type_ref;
            durable.loc = param.loc;
            durable.attrs = param.attrs;
            durable.has_default_argument = param.has_default_argument;
            durable.default_argument_begin = param.default_argument_begin;
            durable.default_argument_end = param.default_argument_end;
            durable.default_argument_loc = param.default_argument_loc;
            durable.is_parameter_pack = param.is_parameter_pack;
            durable.source_parameter_pack_name =
                param.source_parameter_pack_name;
            durable.is_parameter_pack_expansion_sentinel =
                param.is_parameter_pack_expansion_sentinel;
            durable.type_originates_from_template_parameter =
                param.type_originates_from_template_parameter;
            durable.default_argument_declaration_context =
                param.default_argument_declaration_context;
            durable.default_argument_lookup_generation =
                param.default_argument_lookup_generation;
            durable.default_argument_requires_complete_class_replay =
                param.default_argument_requires_complete_class_replay;
            captured.params.push_back(std::move(durable));
        }
        collect_session_.stash_captured_member_body(body_key,
                                                    std::move(captured));
    }
    size_t end = last_consumed_raw_end();
    NodeId root = make_node(NodeKind::TranslationUnit, begin, end, decls);
    tree_.set_root(root);
    return {std::move(tree_), std::move(diagnostics_)};
}

const Token& Parser::current() const {
    static Token eof_token(TokenType::Eof, "", SrcLoc());
    if (cursor_ >= cooked_to_raw_.size()) {
        return eof_token;
    }
    return tokens_[cooked_to_raw_[cursor_]];
}

const Token& Parser::peek(size_t offset) const {
    static Token eof_token(TokenType::Eof, "", SrcLoc());
    size_t index = cursor_ + offset;
    if (index >= cooked_to_raw_.size()) {
        return eof_token;
    }
    return tokens_[cooked_to_raw_[index]];
}

const Token& Parser::last_consumed() const {
    static Token eof_token(TokenType::Eof, "", SrcLoc());
    if (last_consumed_raw_end_ == 0 || tokens_.empty()) {
        return eof_token;
    }
    return tokens_[last_consumed_raw_index()];
}

bool Parser::at_end() const {
    return cursor_ >= cooked_to_raw_.size() || current().type == TokenType::Eof;
}

bool Parser::check(TokenType type) const {
    return !at_end() && current().type == type;
}

bool Parser::match(TokenType type) {
    if (!check(type)) {
        return false;
    }
    consume();
    return true;
}

const Token& Parser::consume() {
    const Token& tok = current();
    if (!at_end()) {
        size_t raw = current_raw_index();
        ++cursor_;
        last_consumed_raw_end_ = raw + 1;
    }
    return tok;
}

size_t Parser::mark() const {
    return cursor_;
}

bool Parser::made_progress(size_t mark) const {
    return cursor_ != mark;
}

size_t Parser::current_raw_index() const {
    if (cursor_ < cooked_to_raw_.size()) {
        return cooked_to_raw_[cursor_];
    }
    return tokens_.size();
}

void Parser::seek_raw_index(size_t raw_index) {
    cursor_ = static_cast<size_t>(std::lower_bound(cooked_to_raw_.begin(),
                                                   cooked_to_raw_.end(),
                                                   raw_index) -
                                  cooked_to_raw_.begin());
    last_consumed_raw_end_ = raw_index;

    pending_template_closes_ = 0;
}

size_t Parser::last_consumed_raw_index() const {
    if (last_consumed_raw_end_ == 0) {
        return 0;
    }
    return last_consumed_raw_end_ - 1;
}

size_t Parser::last_consumed_raw_end() const {
    return last_consumed_raw_end_;
}

SrcLoc Parser::current_loc() const {
    return loc_for_index(current_raw_index());
}

std::string Parser::token_range_display(size_t begin, size_t end) const {
    std::string display;
    size_t limit = std::min({end, begin + 8, tokens_.size()});
    for (size_t i = begin; i < limit; ++i) {
        if (!display.empty() && tokens_[i].flags.has_leading_space) {
            display += ' ';
        }
        display += tokens_[i].value;
    }
    if (end > limit) {
        display += " ...";
    }
    return display;
}

SrcLoc Parser::last_consumed_loc() const {
    return last_consumed().loc;
}

NodeId Parser::parse_error_node(std::string message, size_t begin, size_t end) {
    diagnose(DiagnosticLevel::Error, std::move(message), loc_for_index(begin));
    end = std::min(end, tokens_.size());
    return make_node(NodeKind::Error, begin, end, {}, {}, NodeFlagHasError);
}

NodeId Parser::make_node(NodeKind kind,
                         size_t begin,
                         size_t end,
                         const std::vector<NodeId>& children,
                         NodePayload payload,
                         uint16_t flags,
                         uint16_t opcode) {
    if (end < begin) {
        end = begin;
    }
    if (span_has_macro_expansion(begin, end)) {
        flags |= NodeFlagFromMacro;
    }
    return tree_.add_node(kind, loc_for_index(begin), TokenSpan{begin, end},
        std::span<const NodeId>(children.data(), children.size()), std::move(payload), flags, opcode);
}

bool Parser::is_type_start(TokenType type) {
    switch (type) {
        case TokenType::NULLABILITY_QUALIFIER:
        case TokenType::VOID:
        case TokenType::CHAR:
        case TokenType::SHORT:
        case TokenType::INT:
        case TokenType::LONG:
        case TokenType::FLOAT:
        case TokenType::DOUBLE:
        case TokenType::SIGNED:
        case TokenType::UNSIGNED:
        case TokenType::BOOL:
        case TokenType::WCHAR_T:
        case TokenType::CHAR8_T:
        case TokenType::CHAR16_T:
        case TokenType::CHAR32_T:
        case TokenType::STRUCT:
        case TokenType::UNION:
        case TokenType::ENUM:
        case TokenType::CONST:
        case TokenType::VOLATILE:
        case TokenType::RESTRICT:
        case TokenType::STATIC:
        case TokenType::EXTERN:
        case TokenType::AUTO:
        case TokenType::REGISTER:
        case TokenType::TYPEDEF:
        case TokenType::INLINE:
        case TokenType::NORETURN_KW:
        case TokenType::THREAD_LOCAL:
        case TokenType::INT128:
        case TokenType::UINT128_T:
        case TokenType::TYPENAME:
        case TokenType::BITINT_KW:
        case TokenType::FLOAT16:
        case TokenType::AUTO_TYPE:
        case TokenType::ATOMIC:
        case TokenType::COMPLEX:
        case TokenType::TYPEOF_KW:
        case TokenType::TYPEOF_UNQUAL_KW:
        case TokenType::EXTENSION_KW:
        case TokenType::ALIGNAS:
        case TokenType::ATTRIBUTE_KW:
        case TokenType::CONSTEXPR_KW:
        case TokenType::CONSTEVAL_KW:
        case TokenType::CONSTINIT_KW:
            return true;
        case TokenType::SCOPE_RESOLUTION:
            return lang_opts_.is_cxx_mode() &&
                   (peek_cxx_qualified_type().has_value() ||
                    peek_template_id_qualifier().has_value());
        case TokenType::LEFT_PAREN:
            return out_of_line_structor_declaration_ahead();
        case TokenType::FRIEND_KW:
        case TokenType::MUTABLE_KW:
        case TokenType::EXPLICIT_KW:
        case TokenType::DECLTYPE_KW:
        case TokenType::CLASS:
            return lang_opts_.is_cxx_mode();
        case TokenType::IDENTIFIER:
            if (lang_opts_.is_cxx_mode() && current().value == "__block") {
                return true;
            }
            if (lang_opts_.is_objc() &&
                (current().value == "__strong" ||
                 current().value == "__weak" ||
                 current().value == "__unsafe_unretained" ||
                 current().value == "__autoreleasing")) {

                return true;
            }
            if (out_of_line_structor_declaration_ahead()) {
                return true;
            }
            if (const BuiltinInfo* builtin =
                    BuiltinRegistry::instance().lookup(current().value);
                builtin && builtin->supported &&
                (builtin->syntax == BuiltinSyntaxKind::TypeTransform ||
                 builtin->syntax ==
                     BuiltinSyntaxKind::IntegerSequenceType ||
                 builtin->syntax ==
                     BuiltinSyntaxKind::PackElementType)) {
                return true;
            }
            if (lang_opts_.is_cxx_mode() &&
                (peek(1).type == TokenType::SCOPE_RESOLUTION ||
                 (peek(1).type == TokenType::LESS_THAN &&
                  template_id_precedes_scope(0)))) {
                return peek_cxx_qualified_type().has_value() ||
                       peek_template_id_qualifier().has_value();
            }
            if (lang_opts_.is_cxx_mode() &&
                peek(1).type == TokenType::LESS_THAN) {

                const collect::Session::TemplateInfo* info =
                    collect_session_.template_info_for_name(current().value);
                if (info &&
                    (info->is_class_template || info->is_alias_template)) {
                    return true;
                }
            }
            if (is_deduced_class_template_declaration_start()) {
                return true;
            }
            return collect_session_.is_type_name(current().value);
        default:
            return false;
    }
}

bool Parser::is_decl_specifier(TokenType type) {
    return is_type_start(type) ||
           type == TokenType::ATOMIC ||
           type == TokenType::COMPLEX ||
           type == TokenType::NULLABILITY_QUALIFIER;
}

bool Parser::is_identifier_token(TokenType type) const {
    return type == TokenType::IDENTIFIER ||
           type == TokenType::OPERATOR_KW ||
           type == TokenType::THIS_KW;
}

bool Parser::is_integer_token(TokenType type) const {
    switch (type) {
        case TokenType::INTEGER_CONST:
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::LONG_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::LONG_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
        case TokenType::BITINT_CONST:
        case TokenType::UNSIGNED_BITINT_CONST:
        case TokenType::PP_NUMBER:
            return true;
        default:
            return false;
    }
}

bool Parser::is_imaginary_token(TokenType type) const {
    switch (type) {
        case TokenType::IMAG_FLOAT_CONST:
        case TokenType::IMAG_DOUBLE_CONST:
        case TokenType::IMAG_LONG_DOUBLE_CONST:
        case TokenType::IMAG_INTEGER_CONST:
        case TokenType::IMAG_UNSIGNED_INTEGER_CONST:
        case TokenType::IMAG_LONG_CONST:
        case TokenType::IMAG_UNSIGNED_LONG_CONST:
        case TokenType::IMAG_LONG_LONG_CONST:
        case TokenType::IMAG_UNSIGNED_LONG_LONG_CONST:
            return true;
        default:
            return false;
    }
}

bool Parser::is_floating_token(TokenType type) const {
    switch (type) {
        case TokenType::FLOAT_CONST:
        case TokenType::DOUBLE_CONST:
        case TokenType::LONG_DOUBLE_CONST:
            return true;
        default:
            return false;
    }
}

UnaryOperator Parser::unary_operator_for(TokenType type) const {
    switch (type) {
        case TokenType::BITWISE_AND: return UnaryOperator::AddressOf;
        case TokenType::MULTIPLY: return UnaryOperator::Dereference;
        case TokenType::PLUS: return UnaryOperator::Plus;
        case TokenType::NEGATE: return UnaryOperator::Minus;
        case TokenType::LOGICAL_NOT: return UnaryOperator::LogicalNot;
        case TokenType::BITWISE_NOT: return UnaryOperator::BitwiseNot;
        case TokenType::INCREMENT: return UnaryOperator::PrefixIncrement;
        case TokenType::DECREMENT: return UnaryOperator::PrefixDecrement;
        case TokenType::SIZEOF: return UnaryOperator::SizeofExpr;
        default: return UnaryOperator::Invalid;
    }
}

BinaryOperator Parser::binary_operator_for(TokenType type) const {
    switch (type) {
        case TokenType::ASSIGN: return BinaryOperator::Assign;
        case TokenType::PLUS: return BinaryOperator::Add;
        case TokenType::NEGATE: return BinaryOperator::Sub;
        case TokenType::MULTIPLY: return BinaryOperator::Mul;
        case TokenType::DIVIDE: return BinaryOperator::Div;
        case TokenType::MODULO: return BinaryOperator::Mod;
        case TokenType::LESS_THAN: return BinaryOperator::Less;
        case TokenType::LESS_EQUAL_THAN: return BinaryOperator::LessEqual;
        case TokenType::GREATER_THAN: return BinaryOperator::Greater;
        case TokenType::GREATER_EQUAL_THAN: return BinaryOperator::GreaterEqual;
        case TokenType::EQUAL_TO: return BinaryOperator::Equal;
        case TokenType::NOT_EQUAL: return BinaryOperator::NotEqual;
        case TokenType::THREE_WAY_COMPARE: return BinaryOperator::ThreeWay;
        case TokenType::LOGICAL_AND: return BinaryOperator::LogicalAnd;
        case TokenType::LOGICAL_OR: return BinaryOperator::LogicalOr;
        case TokenType::BITWISE_AND: return BinaryOperator::BitAnd;
        case TokenType::BITWISE_OR: return BinaryOperator::BitOr;
        case TokenType::BITWISE_XOR: return BinaryOperator::BitXor;
        case TokenType::LEFT_SHIFT: return BinaryOperator::Shl;
        case TokenType::RIGHT_SHIFT: return BinaryOperator::Shr;
        case TokenType::DOT_STAR: return BinaryOperator::PtrMemDot;
        case TokenType::ARROW_STAR: return BinaryOperator::PtrMemArrow;
        case TokenType::COMMA: return BinaryOperator::Comma;
        case TokenType::ASSIGN_ADD: return BinaryOperator::AssignAdd;
        case TokenType::ASSIGN_SUB: return BinaryOperator::AssignSub;
        case TokenType::ASSIGN_MUL: return BinaryOperator::AssignMul;
        case TokenType::ASSIGN_DIV: return BinaryOperator::AssignDiv;
        case TokenType::ASSIGN_MOD: return BinaryOperator::AssignMod;
        case TokenType::ASSIGN_LSHIFT: return BinaryOperator::AssignShl;
        case TokenType::ASSIGN_RSHIFT: return BinaryOperator::AssignShr;
        case TokenType::ASSIGN_AND: return BinaryOperator::AssignAnd;
        case TokenType::ASSIGN_XOR: return BinaryOperator::AssignXor;
        case TokenType::ASSIGN_OR: return BinaryOperator::AssignOr;
        default: return BinaryOperator::Invalid;
    }
}

PrecLevel get_prec(TokenType type) {
    switch (type) {
        case TokenType::COMMA:
            return PrecLevel::COMMA;
        case TokenType::ASSIGN:
        case TokenType::ASSIGN_ADD:
        case TokenType::ASSIGN_SUB:
        case TokenType::ASSIGN_MUL:
        case TokenType::ASSIGN_DIV:
        case TokenType::ASSIGN_MOD:
        case TokenType::ASSIGN_LSHIFT:
        case TokenType::ASSIGN_RSHIFT:
        case TokenType::ASSIGN_AND:
        case TokenType::ASSIGN_XOR:
        case TokenType::ASSIGN_OR:
            return PrecLevel::ASSIGNMENT;
        case TokenType::QUESTION:
            return PrecLevel::CONDITIONAL;
        case TokenType::LOGICAL_OR:
            return PrecLevel::LOGICAL_OR;
        case TokenType::LOGICAL_AND:
            return PrecLevel::LOGICAL_AND;
        case TokenType::BITWISE_OR:
            return PrecLevel::INCLUSIVE_OR;
        case TokenType::BITWISE_XOR:
            return PrecLevel::EXCLUSIVE_OR;
        case TokenType::BITWISE_AND:
            return PrecLevel::AND;
        case TokenType::EQUAL_TO:
        case TokenType::NOT_EQUAL:
            return PrecLevel::EQUALITY;
        case TokenType::LESS_THAN:
        case TokenType::LESS_EQUAL_THAN:
        case TokenType::GREATER_THAN:
        case TokenType::GREATER_EQUAL_THAN:
            return PrecLevel::RELATIONAL;
        case TokenType::THREE_WAY_COMPARE:
            return PrecLevel::THREE_WAY;
        case TokenType::LEFT_SHIFT:
        case TokenType::RIGHT_SHIFT:
            return PrecLevel::SHIFT;
        case TokenType::PLUS:
        case TokenType::NEGATE:
            return PrecLevel::ADDSUB;
        case TokenType::MULTIPLY:
        case TokenType::DIVIDE:
        case TokenType::MODULO:
            return PrecLevel::MULTDIV;
        case TokenType::DOT_STAR:
        case TokenType::ARROW_STAR:
            return PrecLevel::PM;
        default:
            return PrecLevel::UNKNOWN;
    }
}

bool Parser::is_right_associative(TokenType type) const {
    switch (type) {
        case TokenType::ASSIGN:
        case TokenType::ASSIGN_ADD:
        case TokenType::ASSIGN_SUB:
        case TokenType::ASSIGN_MUL:
        case TokenType::ASSIGN_DIV:
        case TokenType::ASSIGN_MOD:
        case TokenType::ASSIGN_LSHIFT:
        case TokenType::ASSIGN_RSHIFT:
        case TokenType::ASSIGN_AND:
        case TokenType::ASSIGN_XOR:
        case TokenType::ASSIGN_OR:
            return true;
        default:
            return false;
    }
}

size_t Parser::skip_balanced_until_semicolon() {
    int parens = 0;
    int brackets = 0;
    int braces = 0;
    while (!at_end()) {
        TokenType type = current().type;
        if (type == TokenType::RIGHT_BRACE && braces == 0) {
            break;
        }
        consume();
        if (type == TokenType::LEFT_PAREN) ++parens;
        if (type == TokenType::RIGHT_PAREN && parens > 0) --parens;
        if (type == TokenType::LEFT_BRACKET) ++brackets;
        if (type == TokenType::RIGHT_BRACKET && brackets > 0) --brackets;
        if (type == TokenType::LEFT_BRACE) ++braces;
        if (type == TokenType::RIGHT_BRACE && braces > 0) --braces;
        if (parens == 0 && brackets == 0 && braces == 0 &&
            type == TokenType::SEMICOLON) {
            break;
        }
    }
    return last_consumed_raw_end();
}

size_t Parser::skip_balanced_until_semicolon_or_brace() {
    int parens = 0;
    int brackets = 0;
    while (!at_end()) {
        TokenType type = current().type;
        consume();
        if (type == TokenType::LEFT_PAREN) ++parens;
        if (type == TokenType::RIGHT_PAREN) --parens;
        if (type == TokenType::LEFT_BRACKET) ++brackets;
        if (type == TokenType::RIGHT_BRACKET) --brackets;
        if (parens <= 0 && brackets <= 0 &&
            (type == TokenType::SEMICOLON || type == TokenType::RIGHT_BRACE)) {
            break;
        }
        if (parens <= 0 && brackets <= 0 && type == TokenType::LEFT_BRACE) {
            int braces = 1;
            while (!at_end() && braces > 0) {
                TokenType inner = current().type;
                consume();
                if (inner == TokenType::LEFT_BRACE) ++braces;
                if (inner == TokenType::RIGHT_BRACE) --braces;
            }
            break;
        }
    }
    return last_consumed_raw_end();
}

size_t Parser::skip_until_statement_boundary() {
    while (!at_end() &&
           !check(TokenType::SEMICOLON) &&
           !check(TokenType::RIGHT_BRACE)) {
        consume();
    }
    if (check(TokenType::SEMICOLON)) {
        consume();
    }
    return last_consumed_raw_end();
}

bool Parser::span_has_macro_expansion(size_t begin, size_t end) const {
    if (!source_manager_ || source_manager_->sloc_entry_table.empty()) {
        return false;
    }
    end = std::min(end, tokens_.size());
    for (size_t i = begin; i < end; ++i) {
        if (tokens_[i].loc.isInvalid()) {
            continue;
        }
        const SLocEntry& entry = source_manager_->getEntryForLocation(tokens_[i].loc);
        if (entry.is_expansion) {
            return true;
        }
    }
    return false;
}

void Parser::apply_visibility_directives(bool apply_all) {
    if (!source_manager_) {
        return;
    }
    const auto& directives = source_manager_->pragma_visibility_directives;
    uint32_t boundary = current_loc().offset;
    while (visibility_directives_applied_ < directives.size()) {
        const auto& directive = directives[visibility_directives_applied_];
        if (!apply_all && !at_end() && directive.loc.offset >= boundary) {
            break;
        }
        collect_session_.apply_visibility_pragma(directive.is_push,
                                                 directive.value,
                                                 directive.loc);
        ++visibility_directives_applied_;
    }
}

void Parser::apply_weak_directives(bool apply_all) {
    if (!source_manager_) {
        return;
    }

    const auto& directives = source_manager_->pragma_weak_directives;
    uint32_t boundary = current_loc().offset;
    while (weak_directives_applied_ < directives.size()) {
        const auto& directive = directives[weak_directives_applied_];
        if (!apply_all && !at_end() && directive.loc.offset >= boundary) {
            break;
        }
        collect_session_.apply_weak_pragma(directive.alias,
                                           directive.target,
                                           directive.loc);
        ++weak_directives_applied_;
    }
}

void Parser::diagnose_flagged(WarningId id, std::string message, SrcLoc loc) {
    DiagnosticSeverity severity = DiagnosticSeverity::Warning;
    if (source_manager_) {
        severity = source_manager_->getDiagnosticState(loc).get(id);
    }
    if (severity == DiagnosticSeverity::Ignored) {
        return;
    }
    diagnose(severity == DiagnosticSeverity::Error ? DiagnosticLevel::Error
                                                   : DiagnosticLevel::Warning,
             std::move(message),
             loc);
}

void Parser::diagnose(DiagnosticLevel level, std::string message, SrcLoc loc) {
    diagnostics_.push_back(Diagnostic{level, std::move(message), loc});
}

SrcLoc Parser::loc_for_index(size_t index) const {
    if (index < tokens_.size()) {
        return tokens_[index].loc;
    }
    if (!tokens_.empty()) {
        return tokens_.back().loc;
    }
    return SrcLoc();
}

} // namespace aburi::syntax
