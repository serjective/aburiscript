#ifndef ABURI_SYNTAX_PARSER_H
#define ABURI_SYNTAX_PARSER_H

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "parser_annotation_store.h"
#include "syntax_tree.h"
#include "../diagnostics.h"
#include "../lang_options.h"
#include "../lexer.h"
#include "../source_mgnt.h"
#include "../collect/collect.h"

namespace aburi::syntax {

struct ParseResult {
    Tree tree;
    std::vector<Diagnostic> diagnostics;
};

enum class PrecLevel : uint8_t {
    UNKNOWN = 0,
    COMMA,
    ASSIGNMENT,
    CONDITIONAL,
    LOGICAL_OR,
    LOGICAL_AND,
    INCLUSIVE_OR,
    EXCLUSIVE_OR,
    AND,
    EQUALITY,
    RELATIONAL,
    THREE_WAY,
    SHIFT,
    ADDSUB,
    MULTDIV,
    PM
};

PrecLevel get_prec(TokenType type);

class Parser {
public:
    enum class TentativeMode : uint8_t {
        CollectBacked,
        ParserOnly
    };

    enum class StmtDeclDisambiguation : uint8_t {
        Declaration,
        Expression,
        Ambiguous,
        Invalid
    };

    Parser(const std::vector<Token>& tokens,
           LangOptions lang_opts,
           std::shared_ptr<SourceManager> source_manager,
           collect::Session& collect_session);

    ParseResult parse_translation_unit();

private:
    struct ParserCheckpoint {
        size_t cursor = 0;
        size_t last_consumed_raw_end = 0;
        int pending_template_closes = 0;
        size_t diagnostics_size = 0;
        Tree::Checkpoint tree_checkpoint;
        size_t constraint_concept_id_syntax_size = 0;
        size_t constraint_fold_operand_syntax_size = 0;
    };

    struct TentativeContextFrame {
        size_t id = 0;
        TentativeMode mode = TentativeMode::CollectBacked;
        ParserCheckpoint parser_checkpoint;
    };

    class TentativeParsingAction {
    public:
        explicit TentativeParsingAction(Parser& parser,
                                        TentativeMode mode = TentativeMode::CollectBacked);
        TentativeParsingAction(const TentativeParsingAction&) = delete;
        TentativeParsingAction& operator=(const TentativeParsingAction&) = delete;
        ~TentativeParsingAction();

        void commit();
        void revert();

    private:
        Parser& parser_;
        size_t context_id_ = 0;
        bool active_ = true;
    };

    class RevertingTentativeParsingAction final : public TentativeParsingAction {
    public:
        explicit RevertingTentativeParsingAction(
            Parser& parser,
            TentativeMode mode = TentativeMode::CollectBacked)
            : TentativeParsingAction(parser, mode) {}
        ~RevertingTentativeParsingAction() { revert(); }
    };

    class ConstraintSubstitutionFailureIsolation {
    public:
        explicit ConstraintSubstitutionFailureIsolation(Parser& parser)
            : parser_(parser),
              saved_(parser.constraint_substitution_failure_) {}

        ConstraintSubstitutionFailureIsolation(
            const ConstraintSubstitutionFailureIsolation&) = delete;
        ConstraintSubstitutionFailureIsolation& operator=(
            const ConstraintSubstitutionFailureIsolation&) = delete;

        ~ConstraintSubstitutionFailureIsolation() {
            parser_.constraint_substitution_failure_ = saved_;
        }

    private:
        Parser& parser_;
        bool saved_ = false;
    };

    struct ParsedExpr {
        NodeId syntax = InvalidNodeId;
        collect::ExprResult sem;
    };
    struct ParsedRequiresRequirement {
        NodeId syntax = InvalidNodeId;
        bool dependent = false;
        bool valid = false;
    };
    struct ConstraintConceptIdSyntaxInfo {
        cir::EntityId concept_entity{};
        cir::TypeRef dependent_qualifier;
        cir::NameId concept_name{};
        bool qualified_name = false;
        size_t argument_list_begin = 0;
        size_t argument_list_end = 0;
        std::vector<collect::Session::TemplateArgument> arguments;

        bool is_dependent_concept_id() const {
            return dependent_qualifier.type.valid() &&
                   concept_name.valid();
        }
    };
    struct ConstraintFoldOperandSyntaxInfo {
        std::vector<collect::Session::ParameterPackIdentity> packs;
    };

    struct ParsedDesignatorList {
        std::vector<NodeId> syntax;
        std::vector<collect::InitDesignator> sem;
    };

    struct ParsedAsmString {
        std::string text;
        std::vector<NodeId> syntax;
        bool has_error = false;
    };

    struct ParsedAsmOperandList {
        std::vector<NodeId> syntax;
        std::vector<collect::AsmOperand> operands;
        bool any = false;
    };

    struct ParsedStmt {
        NodeId syntax = InvalidNodeId;
        collect::StmtResult sem;
    };

    struct ParsedDecl {
        NodeId syntax = InvalidNodeId;
        collect::DeclResult sem;
    };

    struct ParsedSwitchLabel {
        NodeId syntax = InvalidNodeId;
        collect::SwitchLabelInput sem;
    };

    struct ParsedAttributes {
        AttributeList attrs;
        std::vector<NodeId> syntax;

        bool empty() const { return attrs.empty(); }
    };

    struct ParsedTypeConstraint {
        const collect::Session::TemplateInfo* concept_info = nullptr;
        std::vector<collect::Session::TemplateArgument> arguments;
        SrcLoc loc{};
        bool qualified_name = false;
        bool has_error = false;
    };

    struct ParsedParam {
        NodeId syntax = InvalidNodeId;
        std::string name;
        cir::TypeId type{};
        cir::TypeRef type_ref{};
        SrcLoc loc{};
        AttributeList attrs;
        bool has_default_argument = false;
        size_t default_argument_begin = 0;
        size_t default_argument_end = 0;
        SrcLoc default_argument_loc{};
        cir::EntityId prototype_entity{};
        cir::Fragment vla_bounds;
        bool is_parameter_pack = false;
        std::string source_parameter_pack_name;
        bool is_parameter_pack_expansion_sentinel = false;
        bool type_originates_from_template_parameter = false;
        cir::DeclContextId default_argument_declaration_context{};
        uint64_t default_argument_lookup_generation = 0;
        bool default_argument_requires_complete_class_replay = false;
        std::vector<std::optional<ParsedTypeConstraint>>
            abbreviated_type_constraints;
    };

    struct ParsedDeclarator {
        NodeId syntax = InvalidNodeId;
        std::string name;
        cir::TypeId type{};
        cir::TypeRef type_ref{};
        SrcLoc loc{};
        AttributeList attrs;
        bool has_name = false;
        bool is_function = false;
        bool constexpr_const_is_implicit = false;
        bool is_variadic = false;
        bool has_prototype = true;
        bool is_kr_style = false;
        bool has_trailing_return_type = false;
        bool has_placeholder_type_constraint = false;
        size_t placeholder_type_constraint_begin = 0;
        size_t placeholder_type_constraint_end = 0;
        SrcLoc placeholder_type_constraint_loc{};
        bool has_noexcept_specifier = false;
        bool has_deferred_noexcept_operand = false;
        size_t noexcept_operand_begin = 0;
        size_t noexcept_operand_end = 0;
        SrcLoc noexcept_operand_loc{};
        cir::DeclContextId noexcept_declaration_context{};
        uint64_t noexcept_lookup_generation = 0;
        bool has_trailing_requires_clause = false;
        size_t trailing_requires_constraint_begin = 0;
        size_t trailing_requires_constraint_end = 0;
        std::optional<collect::Session::NormalizedConstraint>
            trailing_requires_normal_form;
        std::optional<bool> trailing_requires_value;
        SrcLoc trailing_requires_loc{};
        bool has_declarator_operators = false;
        bool has_unsupported_semantics = false;
        cir::DeclContextId qualified_context{};
        const collect::Session::TemplateInfo* template_qualifier_info =
            nullptr;
        std::vector<collect::Session::TemplateArgument>
            template_qualifier_arguments;
        SrcLoc template_qualifier_loc{};
        cir::TypeRef dependent_qualifier_type{};
        std::vector<std::string> kr_param_names;
        std::vector<ParsedParam> params;
        std::optional<collect::Session::TemplateInfo>
            abbreviated_template_info;
        const collect::Session::TemplateInfo* deduced_class_template_info =
            nullptr;
        SrcLoc deduced_class_template_loc{};
        const collect::Session::TemplateInfo*
            explicit_function_template_specialization_info = nullptr;
        std::vector<collect::Session::TemplateArgument>
            explicit_function_template_specialization_arguments;
        cir::EntityId explicit_member_function_template_specialization{};
        cir::Fragment vla_bounds;
        bool is_parameter_pack = false;
        bool type_originates_from_template_parameter = false;
        cir::OperatorFunctionIdentity operator_function;
    };

    enum class RangeDeclarationContext : uint8_t {
        Ordinary,
        Expansion,
    };
    struct RangeDeclarationRecipe {
        NodeId syntax = InvalidNodeId;
        NodeId type_syntax = InvalidNodeId;
        ParsedDeclarator declarator;
        cir::TypeRef structured_pattern{};
        std::vector<collect::StructuredBindingNameInput> structured_names;
        std::vector<NodeId> structured_name_syntax;
        collect::DeclFlags flags;
        SrcLoc loc{};
        RangeDeclarationContext context = RangeDeclarationContext::Ordinary;
        bool is_structured = false;
        bool has_error = false;
    };

    struct ForControlScan {
        bool is_range = false;
        bool has_init_statement = false;
    };

    struct FunctionDeclaratorResult {
        collect::DeclResult decl;
        bool parsed_definition = false;
    };

    struct ExplicitClassTemplateSpecializationParse {
        bool consumed = false;
        bool matched = false;
        bool has_error = false;
        bool is_partial_replay = false;
        cir::EntityId template_entity{};
        cir::DeclContextId qualified_context{};
        std::string source_name;
        std::string display_name;
        std::vector<collect::Session::TemplateArgument> arguments;
    };
    struct ParsedExplicitSpecifier {
        cir::ExplicitSpecifierKind kind = cir::ExplicitSpecifierKind::Absent;
        size_t expression_begin = 0;
        size_t expression_end = 0;
        cir::DeclContextId declaration_context{};
        uint64_t lookup_generation = 0;
        cir::TemplateValueExpression value_expression;
        SrcLoc loc{};
        bool has_error = false;

        bool present() const {
            return kind != cir::ExplicitSpecifierKind::Absent;
        }
        bool effective_value() const {
            return kind == cir::ExplicitSpecifierKind::True;
        }
    };
    ParsedExplicitSpecifier parse_explicit_specifier();
    std::optional<bool> replay_explicit_specifier(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc use_loc,
        const collect::Session::TemplateArgumentBindings* exact_bindings =
            nullptr);
    std::optional<bool> resolve_member_specialization_explicit_specifier(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        cir::EntityId specialization,
        SrcLoc use_loc,
        const collect::Session::TemplateArgumentBindings* exact_bindings =
            nullptr);
    ExplicitClassTemplateSpecializationParse*
        explicit_class_template_specialization_parse_ = nullptr;
    bool explicit_member_record_specialization_ = false;
    bool explicit_member_function_specialization_declaration_ = false;
    bool defer_class_template_qualifier_instantiation_ = false;
    unsigned explicit_member_template_overlay_head_depth_ = 0;
    bool select_partial_for_deferred_class_template_qualifier_ = false;
    bool instantiate_member_parameter_defaults_ = false;
    struct PendingMemberBody {
        size_t method_index = 0;
        size_t body_begin = 0;
        size_t body_end = 0;
        size_t init_begin = 0;
        size_t init_end = 0;
        bool is_constructor_function_try = false;
        std::vector<ParsedParam> params;
        bool has_placeholder_return_type_constraint = false;
        size_t placeholder_return_type_constraint_begin = 0;
        size_t placeholder_return_type_constraint_end = 0;
        SrcLoc placeholder_return_type_constraint_loc{};
    };
    struct PendingMemberTemplate {
        size_t method_index = 0;
        collect::Session::TemplateInfo info;
        std::optional<PendingMemberBody> body;
        SrcLoc loc{};
    };
    struct PendingHiddenFriendBody {
        cir::EntityId entity{};
        cir::EntityId granting_record{};
        cir::EntityId enclosing_template{};
        std::vector<collect::Session::TemplateArgument>
            enclosing_template_arguments;
        uint64_t point_lookup_generation = 0;
        cir::DeclContextId lexical_context{};
        size_t body_begin = 0;
        size_t body_end = 0;
        std::string name;
        cir::TypeId function_type{};
        cir::TypeRef result_type{};
        std::vector<collect::ParamInput> params;
        collect::DeclFlags flags;
        SrcLoc loc{};
        bool is_defaulted_comparison = false;
        bool has_explicit_exception_spec = false;
        cir::EntityId implicit_equality_origin{};
    };
    struct DeferredCompleteClassRecord {
        cir::EntityId record{};
        bool in_template_definition = false;
        std::vector<PendingMemberTemplate> member_templates;
        std::vector<PendingMemberBody> bodies;
        std::vector<cir::EntityId> method_entities;
    };
    void replay_deferred_member_bodies(
        const std::vector<PendingMemberBody>& pending,
        const std::vector<cir::EntityId>& method_entities);
    void register_deferred_template_member_body(
        cir::EntityId method_entity,
        const PendingMemberBody& body);
    bool has_incomplete_enclosing_record(cir::EntityId record) const;
    void finalize_pending_member_templates(
        std::vector<PendingMemberTemplate> pending,
        const std::vector<cir::EntityId>& method_entities);
    void replay_or_defer_record_bodies(
        cir::EntityId record,
        std::vector<PendingMemberTemplate> member_templates,
        std::vector<PendingMemberBody> bodies,
        std::vector<cir::EntityId> method_entities);
    void replay_ready_complete_class_records();
    void replay_hidden_friend_bodies(cir::EntityId record);
    bool replay_hidden_friend_body(PendingHiddenFriendBody body);
    bool force_deferred_hidden_friend_body(
        cir::EntityId function,
        cir::InstantiationDemandKind demand_kind);
    std::unordered_map<uint64_t, std::vector<PendingHiddenFriendBody>>
        pending_hidden_friend_bodies_;
    std::unordered_map<uint64_t, PendingHiddenFriendBody>
        deferred_hidden_friend_bodies_;
    std::vector<DeferredCompleteClassRecord> deferred_complete_class_records_;
    std::vector<cir::EntityId> active_default_member_initializer_replays_;
    void replay_member_body(cir::EntityId method_entity,
                            const PendingMemberBody& body,
                            bool allow_return_deduction = true);
    void validate_member_template_body(collect::Session::TemplateInfo& info,
                                       cir::EntityId method_entity,
                                       const PendingMemberBody& body,
                                       SrcLoc loc);
    bool clone_member_body(cir::EntityId method_entity,
                           const PendingMemberBody& body);
    void record_template_clone_instantiation(bool member);
    void record_template_replay_fallback(bool clone_attempted,
                                         bool member,
                                         std::string display,
                                         SrcLoc loc);
    bool force_deferred_template_member_body(cir::EntityId method_entity,
                                             bool allow_clone = true);
    bool register_source_late_out_of_line_member_body(
        cir::EntityId method_entity);
    bool force_deferred_template_static_data_member_definition(
        cir::EntityId member_entity,
        cir::InstantiationDemandKind demand_kind);
    bool routed_in_class_static_data_member_materialization(
        cir::EntityId member_entity);
    bool materialize_deferred_in_class_static_data_member(
        cir::EntityId member_entity);
    struct DeferredScopedEnumDefinition {
        cir::EntityId entity{};
        cir::EntityId owner{};
        size_t definition_begin = 0;
        size_t definition_end = 0;
        SrcLoc loc{};
    };
    std::unordered_map<uint64_t, DeferredScopedEnumDefinition>
        deferred_scoped_enum_definitions_;
    bool replaying_deferred_scoped_enum_definition_ = false;
    bool force_deferred_scoped_enum_definition(cir::EntityId enum_entity);
    struct DeferredMemberClassDefinition {
        cir::EntityId entity{};
        cir::EntityId owner{};
        size_t definition_begin = 0;
        size_t definition_end = 0;
        SrcLoc loc{};
    };
    std::unordered_map<uint64_t, DeferredMemberClassDefinition>
        deferred_member_class_definitions_;
    size_t replaying_deferred_member_class_begin_ =
        std::numeric_limits<size_t>::max();
    bool force_deferred_member_class_definition(cir::EntityId record_entity);
    void materialize_deferred_static_data_member_expr(
        collect::ExprResult& expression);
    void force_class_explicit_instantiation_definition_members(
        cir::EntityId record_entity,
        SrcLoc instantiation_loc);
    struct DeferredTemplateBody {
        cir::EntityId method;
        PendingMemberBody body;
    };
    std::unordered_map<uint64_t, DeferredTemplateBody> deferred_template_bodies_;
    std::unordered_map<uint64_t, PendingMemberBody> member_template_bodies_;
    // [temp.point]p8
    enum class OdrInstantiationOwner : uint8_t { MemberBody, FunctionDemand };
    struct PendingOdrInstantiation {
        cir::EntityId entity;
        OdrInstantiationOwner owner = OdrInstantiationOwner::MemberBody;
    };
    std::vector<PendingOdrInstantiation> pending_odr_instantiations_;
    std::unordered_set<uint64_t> queued_odr_instantiations_;
    bool draining_odr_instantiations_ = false;
    void queue_odr_instantiation(cir::EntityId entity,
                                 OdrInstantiationOwner owner);
    bool drain_pending_odr_instantiations();
    void replay_referenced_template_members();
    bool parse_member_initializer_list(
        std::vector<collect::Session::MemberInitializerInput>& initializers,
        size_t end_index = 0);

    enum class StorageClass : uint8_t {
        None,
        Typedef,
        Extern,
        Static,
        Auto,
        Register
    };
    struct TypeParseContext {
        enum class Origin : uint8_t {
            None,
            ExplicitTypename,
            TypeRequirement,
            NestedNameSpecifier,
            ElaboratedTypeSpecifier,
            ClassOrDecltype,
            UsingEnumDeclarator,
            FriendTypeSpecifier,
            NewTypeId,
            DefiningTypeId,
            ConversionTypeId,
            TrailingReturnType,
            TypeParameterDefault,
            NamedCastTypeId,
            NamespaceDeclSpecifier,
            FunctionParameter,
            MemberDeclSpecifier,
            MemberParameter,
            QualifiedDeclaratorParameter,
            LambdaParameter,
            RequirementParameter,
            ConstantTemplateParameter
        };

        Origin origin;

        constexpr TypeParseContext() : origin(Origin::None) {}
        constexpr explicit TypeParseContext(Origin value) : origin(value) {}

        constexpr bool is_type_only() const {
            return origin != Origin::None;
        }

        static constexpr TypeParseContext type_only(Origin origin) {
            return TypeParseContext(origin);
        }
    };

    enum class ParameterListPolicy : uint8_t {
        Function,
        RequirementLocal,
    };

    struct DeclarationParser {
        struct TypeTally {
            int void_count = 0;
            int char_count = 0;
            int short_count = 0;
            int int_count = 0;
            int long_count = 0;
            int float_count = 0;
            int double_count = 0;
            int bool_count = 0;
            int wchar_count = 0;
            int char8_count = 0;
            int char16_count = 0;
            int char32_count = 0;
            int signed_count = 0;
            int unsigned_count = 0;
            int complex_count = 0;
            int int128_count = 0;
            int bitint_count = 0;
            uint32_t bitint_bits = 0;
            int float16_count = 0;
            int static_count = 0;
            int extern_count = 0;
            int auto_count = 0;
            int register_count = 0;
            int typedef_count = 0;
            int constexpr_count = 0;
            int consteval_count = 0;
            int constinit_count = 0;
            int inline_count = 0;
            int thread_local_count = 0;
            int auto_type_count = 0;
            int cxx_auto_count = 0;
            int decltype_auto_count = 0;
            int mutable_count = 0;
            int block_byref_count = 0;
        };

        explicit DeclarationParser(
            Parser& parser,
            TypeParseContext context = TypeParseContext{});

        cir::TypeRef parse_declaration(bool run_second_half = true,
                                       bool allow_abstract = true);
        cir::TypeRef parse_declaration_specifiers();
        ParsedDeclarator parse_declarator(cir::TypeRef base_type,
                                          bool allow_abstract = false,
                                          const ParsedDeclarator* prefix = nullptr);
        void reset_declarator_parsing_state();

        Parser& pars;
        const TypeParseContext type_context;
        SrcLoc begin_loc{};
        NodeId type_syntax = InvalidNodeId;
        NodeId declarator_syntax = InvalidNodeId;
        std::string type_text;
        std::string name;
        StorageClass storage_class = StorageClass::None;
        cir::TypeRef first_half{};
        cir::TypeRef result_type{};
        uint8_t qualifiers = cir::QualNone;
        uint8_t base_qualifiers = cir::QualNone;
        bool is_inline = false;
        bool is_thread_local = false;
        bool is_constexpr = false;
        bool is_consteval = false;
        bool is_constinit = false;
        bool is_mutable = false;
        bool is_friend = false;
        bool is_block_byref = false;
        bool is_parameter_pack = false;
        bool is_out_of_line_structor = false;
        bool allow_cxx_member_declarator_ids = false;
        bool allow_friend_type_specifier = false;
        bool allow_parameter_pack_declarator = false;
        bool defer_abbreviated_parameter_rewrite = false;
        bool has_unsupported_semantics = false;
        bool type_originates_from_template_parameter = false;
        bool has_trailing_return_type = false;
        bool has_placeholder_type_constraint = false;
        size_t placeholder_type_constraint_begin = 0;
        size_t placeholder_type_constraint_end = 0;
        SrcLoc placeholder_type_constraint_loc{};
        const collect::Session::TemplateInfo* deduced_class_template_info =
            nullptr;
        SrcLoc deduced_class_template_loc{};
        SrcLoc loc{};
        std::vector<std::string> kr_param_names;
        std::vector<ParsedParam> func_args;
        bool captured_func_args = false;
        AttributeList leading_attrs;
        TypeTally tally;
        cir::Fragment vla_bounds_fragment;
        collect::Session::TemplateInfo abbreviated_template_info;
        collect::Session::TemplateInfo* abbreviated_template_target = nullptr;
        std::vector<std::optional<ParsedTypeConstraint>>
            abbreviated_type_constraints;

    private:
        void error(std::string message);
        void error_custloc(std::string message, SrcLoc loc);
        cir::TypeRef resolve_builtin_type(const TypeTally& tally);
        void validate_tally(const TypeTally& tally);
        static StorageClass resolve_storage_class(const TypeTally& tally);
    };

    const Token& current() const;
    const Token& peek(size_t offset) const;
    size_t skip_attribute_specifier_sequence_offset(size_t offset) const;
    const Token& last_consumed() const;
    bool at_end() const;
    bool check(TokenType type) const;
    bool match(TokenType type);
    const Token& consume();
    size_t mark() const;
    bool made_progress(size_t mark) const;
    size_t current_raw_index() const;
    void seek_raw_index(size_t raw_index);
    size_t last_consumed_raw_index() const;
    size_t last_consumed_raw_end() const;
    SrcLoc current_loc() const;
    SrcLoc last_consumed_loc() const;

    ParsedDecl parse_external_declaration();
    std::optional<ParsedDecl>
        try_parse_cxx_out_of_line_conversion_function_declaration();
    ParsedDecl parse_declaration(bool top_level,
                                 bool condition_declaration = false);
    ParsedDecl parse_static_assert_declaration();
    ParsedDecl parse_cxx_using_declaration();
    ParsedDecl parse_cxx_namespace_declaration(bool is_inline = false);
    void parse_module_preamble(std::vector<NodeId>& decls);
    ParsedDecl parse_cxx_module_construct();
    ParsedDecl parse_cxx_module_declaration(size_t begin,
                                            bool exported,
                                            bool at_start);
    ParsedDecl parse_cxx_import_declaration(size_t begin, bool exported);
    ParsedDecl parse_cxx_export_declaration();
    bool parse_module_name_into(std::string& out);
    ParseResult parse_module_unit();
    struct ModuleParserRegistry {
        struct Entry {
            Parser* parser = nullptr;
            cir::ModuleAttachmentId unit{};
        };
        std::vector<std::unique_ptr<Parser>> owned;
        std::unordered_map<uint32_t, Entry> by_unit_index;
    };
    Parser* module_unit_parser_for(cir::EntityId pattern_entity);
    cir::EntityId module_pattern_identity(cir::EntityId specialization) const;
    size_t capture_out_of_line_member_end(size_t declarator_tail,
                                          size_t declarator_last_end,
                                          bool is_function);
    ParsedDecl parse_cxx_template_declaration();
    ParsedDecl parse_cxx_explicit_instantiation_declaration();
    ParsedDecl parse_cxx_explicit_instantiation_definition();
    std::optional<ParsedDecl> try_parse_cxx_deduction_guide_declaration(
        const collect::Session::TemplateInfo* guide_template_info = nullptr,
        SrcLoc template_loc = SrcLoc(),
        std::optional<size_t> declaration_begin = std::nullopt);
    bool parse_cxx_template_head(collect::Session::TemplateInfo& info,
                                 SrcLoc template_loc,
                                 uint32_t parameter_depth = 0,
                                 bool lambda_template_head = false);
    void record_trailing_function_requires_clause(
        collect::Session::TemplateInfo& info,
        const ParsedDeclarator& declarator);
    void record_function_constraint_parameters(
        collect::Session::TemplateInfo& info,
        const std::vector<ParsedParam>& parameters);
    void record_trailing_function_requires_clause(
        collect::Session::TemplateInfo& info,
        size_t constraint_begin,
        size_t constraint_end,
        std::optional<collect::Session::NormalizedConstraint> normal_form =
            std::nullopt);
    void retain_static_data_member_initializer_tokens(
        collect::Session::TemplateInfo& info,
        size_t definition_begin,
        size_t definition_end);
    std::optional<ParsedDecl> try_parse_class_template_partial_specialization(
        collect::Session::TemplateInfo& info,
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl> try_parse_explicit_class_template_specialization(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl> try_parse_explicit_member_function_specialization(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl> try_parse_explicit_static_data_member_specialization(
        size_t begin,
        SrcLoc template_loc);
    bool reject_explicit_specialization_of_member_of_explicit_class(
        const collect::Session::TemplateInfo& owner_info,
        const std::vector<collect::Session::TemplateArgument>& owner_arguments,
        SrcLoc template_loc);
    std::optional<ParsedDecl> try_parse_explicit_function_template_specialization(
        size_t begin,
        SrcLoc template_loc,
        bool has_member_template_head = false);
    std::optional<ParsedDecl>
    try_parse_class_template_explicit_instantiation_declaration(
        size_t begin,
        SrcLoc extern_loc,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_class_template_explicit_instantiation_definition(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_member_class_explicit_instantiation_declaration(
        size_t begin,
        SrcLoc extern_loc,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_member_class_explicit_instantiation_definition(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_static_data_member_template_explicit_instantiation_declaration(
        size_t begin,
        SrcLoc extern_loc,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_static_data_member_template_explicit_instantiation_definition(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_variable_template_explicit_instantiation_declaration(
        size_t begin,
        SrcLoc extern_loc,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_variable_template_explicit_instantiation_definition(
        size_t begin,
        SrcLoc template_loc);
    void parse_explicit_variable_declarator_suffix(
        ParsedDeclarator& declarator,
        std::vector<NodeId>& children);
    bool validate_variable_template_explicit_instantiation_type(
        const collect::Session::TemplateInfo& primary,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        cir::TypeRef written_type,
        SrcLoc loc);
    std::optional<ParsedDecl>
    try_parse_static_data_member_explicit_instantiation_declaration(
        size_t begin,
        SrcLoc extern_loc,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_static_data_member_explicit_instantiation_definition(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_static_data_member_explicit_instantiation(
        size_t begin,
        SrcLoc introducer_loc,
        SrcLoc template_loc,
        bool is_declaration);
    std::optional<ParsedDecl>
    try_parse_function_template_explicit_instantiation_declaration(
        size_t begin,
        SrcLoc extern_loc,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_function_template_explicit_instantiation_definition(
        size_t begin,
        SrcLoc template_loc);
    std::optional<ParsedDecl>
    try_parse_conversion_function_template_explicit_instantiation(
        size_t begin,
        SrcLoc introducer_loc,
        SrcLoc template_loc,
        bool is_declaration);
    collect::ExprResult replay_default_member_initializer(
        cir::EntityId field,
        cir::InstId object_place,
        SrcLoc loc);
    collect::ExprResult routed_default_argument_replay(
        cir::EntityId selected,
        size_t parameter_index,
        SrcLoc loc);
    collect::ExprResult replay_default_argument(cir::EntityId selected,
                                                size_t parameter_index,
                                                SrcLoc loc);
    bool should_defer_complete_class_region() const;
    void replay_complete_class_regions(
        cir::EntityId record,
        const std::vector<PendingMemberTemplate>& member_templates,
        const std::vector<cir::EntityId>& method_entities);
    cir::FunctionExceptionSpec replay_complete_class_noexcept(
        const cir::RecordMethodFact& method,
        const collect::Session::TemplateInfo* member_template_info);
    void append_default_call_arguments(collect::ExprResult& callee,
                                       std::vector<collect::ExprResult>& args,
                                       SrcLoc loc);
    collect::ParamInput param_input_from_parsed_param(
        ParsedParam& param,
        bool move_runtime_fragments);
    std::vector<collect::ParamInput> param_inputs_from_parsed_params(
        std::vector<ParsedParam>& params,
        bool move_runtime_fragments);
    ParsedDecl parse_cxx_linkage_specification();
    struct ParsedNestedName {
        collect::Session::QualifierResolution scope;
        bool consumed_any = false;
        bool global_qualifier = false;
        bool has_error = false;
        bool depends_on_template_parameter = false;
        std::string last_component_name;
        const collect::Session::TemplateInfo* template_qualifier_info =
            nullptr;
        std::vector<collect::Session::TemplateArgument>
            template_qualifier_arguments;
        SrcLoc template_qualifier_loc{};
    };
    struct QualifiedTypeLookahead {
        cir::TypeRef type;
        size_t tokens_to_consume = 0;
        cir::DeclContextId terminal_context{};
        std::string terminal_name;
        SrcLoc terminal_loc{};
        const collect::Session::TemplateInfo* template_info = nullptr;
        bool is_deduced_placeholder = false;
    };
    struct TemplateIdQualifierLookahead {
        const collect::Session::TemplateInfo* template_info = nullptr;
        std::string_view template_name;
        size_t terminal_offset = 0;
    };
    struct ParsedOperatorFunctionId {
        std::string name;
        cir::OperatorFunctionIdentity identity;
        NodeId type_syntax = InvalidNodeId;
        SrcLoc loc{};
        bool has_error = false;
    };
    struct ParsedConversionFunctionId {
        std::string name;
        cir::OperatorFunctionIdentity identity;
        cir::TypeRef target_type{};
        NodeId type_syntax = InvalidNodeId;
        SrcLoc loc{};
        bool has_error = false;
    };
    struct ParsedConversionFunctionDeclarator {
        ParsedDeclarator declarator;
        cir::TypeRef target_type{};
        NodeId target_syntax = InvalidNodeId;
        bool has_error = false;
    };
    ParsedNestedName parse_nested_name_specifier();
    bool starts_cxx_qualified_name(size_t offset = 0);
    bool decltype_specifier_precedes_scope(size_t offset = 0);
    std::optional<ParsedOperatorFunctionId> parse_operator_function_id();
    bool starts_conversion_function_id(size_t offset = 0);
    bool starts_qualified_conversion_function_id(size_t offset = 0);
    std::pair<cir::TypeRef, NodeId> parse_conversion_type_id();
    std::optional<ParsedConversionFunctionId>
        parse_conversion_function_id();
    std::optional<ParsedConversionFunctionDeclarator>
        parse_conversion_function_declarator(bool require_qualified);
    std::optional<ParsedTypeConstraint> try_parse_type_constraint();
    bool starts_type_constraint_placeholder(size_t offset = 0) const;
    std::optional<collect::Session::NormalizedConstraint>
    build_type_constraint_normal_form(
        const collect::Session::TemplateInfo& info,
        const collect::Session::TemplateParameter& parameter,
        const ParsedTypeConstraint& type_constraint);
    bool evaluate_type_constraint_for_constrained_type(
        const ParsedTypeConstraint& type_constraint,
        cir::TypeRef constrained_type,
        SrcLoc loc,
        bool& dependent,
        bool& satisfied);
    bool validate_placeholder_type_constraint(
        size_t constraint_begin,
        size_t constraint_end,
        SrcLoc constraint_loc,
        cir::TypeRef constrained_type,
        std::string_view diagnostic_subject);
    bool validate_placeholder_return_type_constraint(
        cir::EntityId function,
        size_t constraint_begin,
        size_t constraint_end,
        SrcLoc constraint_loc);
    std::optional<cir::TypeRef> parse_cxx_qualified_type_name(
        TypeParseContext context = TypeParseContext{});
    ParsedExpr parse_cxx_qualified_id_expression();
    collect::ExprResult template_id_expression_result(
        const collect::Session::TemplateInfo& info,
        cir::EntityId instantiated,
        SrcLoc loc,
        bool qualified_name);
    void bind_unqualified_member_template_id(
        collect::ExprResult& expression,
        std::string_view name,
        SrcLoc loc);
    collect::ExprResult evaluate_concept_id_expression(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument> arguments,
        SrcLoc loc,
        bool qualified_name,
        std::vector<collect::Session::TemplateArgument>*
            canonical_arguments_out = nullptr,
        uint64_t point_lookup_generation = 0);
    collect::ExprResult instantiate_template_id_expression_result(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument> arguments,
        SrcLoc loc,
        bool qualified_name,
        std::vector<collect::Session::TemplateArgument>*
            canonical_concept_arguments_out = nullptr,
        const std::vector<const collect::Session::TemplateInfo*>*
            function_candidates = nullptr,
        const std::vector<collect::CandidateExplicitTemplateArguments>*
            candidate_explicit_arguments = nullptr);
    ParsedExpr parse_unqualified_template_id_expression(
        const collect::Session::TemplateInfo& info,
        std::string name,
        SrcLoc loc,
        size_t begin);
    void record_constraint_concept_id_syntax(
        NodeId syntax,
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument> arguments,
        bool qualified_name);
    void record_dependent_constraint_concept_id_syntax(
        NodeId syntax,
        cir::TypeRef dependent_qualifier,
        std::string_view concept_name,
        bool qualified_name,
        size_t argument_list_begin,
        size_t argument_list_end);
    const ConstraintConceptIdSyntaxInfo*
    constraint_concept_id_syntax_info(NodeId syntax) const;
    void record_constraint_fold_operand_syntax(
        NodeId syntax,
        ConstraintFoldOperandSyntaxInfo info);
    const ConstraintFoldOperandSyntaxInfo*
    constraint_fold_operand_syntax_info(NodeId syntax) const;
    bool diagnose_invalid_concept_pack_fold_pattern(NodeId syntax,
                                                    SrcLoc loc);
    std::optional<QualifiedTypeLookahead> peek_cxx_qualified_type(
        size_t start_offset = 0);
    std::optional<TemplateIdQualifierLookahead> peek_template_id_qualifier(
        size_t start_offset = 0);
    bool template_id_precedes_scope(size_t offset);
    size_t template_id_scope_offset(size_t offset);
    bool out_of_line_structor_declaration_ahead(size_t start_offset = 0);
    bool template_id_precedes_postfix(size_t offset, TokenType postfix);
    bool template_id_precedes_call(size_t offset);
    bool template_id_precedes_type_conversion(size_t offset);
    cir::EntityId instantiate_template(const collect::Session::TemplateInfo& info,
                                       SrcLoc loc,
                                       bool record_point_of_instantiation = true);
    cir::TypeRef instantiate_or_defer_qualified_type_template(
        const collect::Session::TemplateInfo& info,
        cir::TypeRef qualifier,
        std::string_view member_name,
        SrcLoc loc);
    bool parse_template_argument_list(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc);
    cir::TypeRef parse_builtin_type_pack_element_type(
        SrcLoc loc,
        std::vector<NodeId>& children);
    // The [temp.arg.general] lookup invariant classifies written arguments
    // before consulting any overload candidate.
    bool parse_candidate_neutral_template_argument_list(
        const collect::Session::TemplateInfo& request_info,
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc);
    struct TemplateArgumentListParsingRequest {
        collect::Session* session = nullptr;
        collect::Session::TemplateArgumentListParsingScope scope;

        TemplateArgumentListParsingRequest() = default;
        TemplateArgumentListParsingRequest(
            collect::Session& session,
            collect::Session::TemplateArgumentListParsingScope scope);
        TemplateArgumentListParsingRequest(
            const TemplateArgumentListParsingRequest&) = delete;
        TemplateArgumentListParsingRequest& operator=(
            const TemplateArgumentListParsingRequest&) = delete;
        TemplateArgumentListParsingRequest(
            TemplateArgumentListParsingRequest&& other) noexcept;
        TemplateArgumentListParsingRequest& operator=(
            TemplateArgumentListParsingRequest&& other) noexcept;
        ~TemplateArgumentListParsingRequest();

        bool active() const { return scope.active; }
        uint64_t point_lookup_generation() const {
            return scope.point_lookup_generation;
        }
        void finish();
    };
    TemplateArgumentListParsingRequest begin_template_argument_list_parsing_request(
        const collect::Session::TemplateInfo& info,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    bool parse_template_argument_list_with_request(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    bool parse_candidate_neutral_template_argument_list_with_request(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    bool parse_function_template_argument_list_for_candidates(
        const collect::Session::TemplateInfo& requested_info,
        const std::vector<const collect::Session::TemplateInfo*>& candidates,
        std::vector<collect::Session::TemplateArgument>& arguments,
        std::vector<collect::CandidateExplicitTemplateArguments>&
            candidate_arguments,
        SrcLoc loc,
        const collect::Session::TemplateInfo** selected_info = nullptr);
    bool parse_and_canonicalize_template_argument_list(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t* point_lookup_generation = nullptr);
    void configure_pattern_instantiation_callbacks(
        collect::Session::PatternInstantiationCallbacks& callbacks,
        SrcLoc loc);
    bool parse_template_template_argument_name(
        collect::Session::TemplateArgument& argument,
        collect::Session::TemplateTemplateParameterKind expected_kind,
        std::string expected_message,
        std::string must_name_message);
    cir::TypeRef parse_builtin_make_integer_sequence_type(
        SrcLoc loc,
        std::vector<NodeId>& children,
        bool materialize_class_definition = false);
    bool is_deduced_class_template_declaration_start();
    bool parse_dependent_type_template_argument_list(
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc);
    bool parse_dependent_expression_template_argument_list(
        SrcLoc loc,
        size_t* argument_list_begin = nullptr,
        size_t* argument_list_end = nullptr,
        std::vector<collect::Session::TemplateArgument>*
            arguments_out = nullptr);
    bool canonicalize_template_arguments(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t* point_lookup_generation = nullptr,
        collect::Session::TemplateArgumentCompletionMode completion_mode =
            collect::Session::TemplateArgumentCompletionMode::Required);
    std::string format_template_argument_binding_failure(
        const collect::Session::TemplateInfo& info,
        const collect::Session::TemplateArgumentBindingFailure& failure) const;
    std::string format_template_argument_kind_mismatch(
        uint32_t parameter_index,
        uint32_t argument_index,
        collect::Session::TemplateParameterKind expected_kind,
        cir::TemplateArgumentKind actual_kind) const;
    bool build_type_constraint_concept_arguments(
        const collect::Session::TemplateInfo& concept_info,
        const collect::Session::TemplateArgument& constrained_argument,
        const std::vector<collect::Session::TemplateArgument>& tail_arguments,
        SrcLoc loc,
        std::vector<collect::Session::TemplateArgument>& concept_arguments,
        uint64_t* point_lookup_generation = nullptr);
    enum class CtadInitializationKind : uint8_t {
        Direct,
        Copy,
        Default,
        CopyList
    };
    void validate_template_definition(collect::Session::TemplateInfo& info,
                                      SrcLoc loc);
    cir::EntityId instantiate_template_with_args(
        const collect::Session::TemplateInfo& info,
        std::vector<collect::Session::TemplateArgument> arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0,
        bool replay_guard_entered = false,
        bool arguments_are_canonical = false,
        bool materialize_class_definition = true,
        bool record_point_of_instantiation = true,
        collect::Session::TemplateArgumentCompletionMode completion_mode =
            collect::Session::TemplateArgumentCompletionMode::Required,
        const collect::Session::TemplateArgumentBindings* exact_bindings =
            nullptr);
    cir::EntityId form_function_template_candidate(
        const collect::Session::TemplateInfo& info,
        const collect::Session::TemplateArgumentBindings& argument_bindings,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    collect::Session::CoroutinePromiseResolution
    resolve_coroutine_promise_type(
        const std::vector<cir::TypeRef>& traits_arguments,
        SrcLoc loc);
    collect::Session::InstantiationDemandResult materialize_function_demand(
        cir::EntityId specialization,
        cir::InstantiationDemandKind kind,
        SrcLoc loc);
    collect::Session::InstantiationDemandResult materialize_class_demand(
        cir::EntityId specialization,
        cir::InstantiationDemandKind kind,
        cir::EntityId subject,
        SrcLoc loc);
    bool template_arguments_are_dependent(
        const std::vector<collect::Session::TemplateArgument>& arguments);
    bool check_template_associated_constraints(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation,
        bool diagnose_unsatisfied,
        const collect::Session::TemplateArgumentBindings* exact_bindings =
            nullptr);
    const collect::Session::TemplateArgumentBindings*
        constraint_argument_bindings_override_ = nullptr;
    collect::Session::PartialSpecializationSelection
    select_template_partial_specialization(
        const collect::Session::TemplateInfo& primary,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    bool partial_specialization_pattern_is_viable(
        const collect::Session::TemplateInfo& primary,
        const collect::Session::TemplateInfo& partial,
        const collect::Session::TemplateArgumentBindings& bindings,
        const std::vector<collect::Session::TemplateArgument>& actual,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    enum class NormalizedConstraintCheckResult {
        Satisfied,
        Unsatisfied,
        Invalid,
        Unsupported
    };
    NormalizedConstraintCheckResult
    evaluate_normalized_associated_constraint(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        const collect::Session::NormalizedConstraint& form,
        uint32_t root,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    NormalizedConstraintCheckResult evaluate_normalized_direct_atom(
        const collect::Session::TemplateInfo& info,
        const collect::Session::NormalizedConstraintNode& node,
        SrcLoc loc);
    NormalizedConstraintCheckResult evaluate_normalized_concept_owned_atom(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        const collect::Session::NormalizedConstraintNode& node,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    NormalizedConstraintCheckResult
    evaluate_normalized_concept_dependent_constraint(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        const collect::Session::NormalizedConstraintNode& node,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    NormalizedConstraintCheckResult evaluate_normalized_fold_expanded_constraint(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        const collect::Session::NormalizedConstraint& form,
        const collect::Session::NormalizedConstraintNode& node,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    bool evaluate_introduced_type_constraint(
        const collect::Session::TemplateInfo& info,
        const collect::Session::TemplateInfo::IntroducedConstraint& constraint,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation,
        std::optional<bool>& value,
        bool& substitution_failure);
    bool check_non_function_template_associated_constraints(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    bool deduce_function_template_declaration_match(
        const collect::Session::TemplateInfo& info,
        cir::TypeId function_type,
        std::vector<collect::Session::TemplateArgument>& deduced,
        const std::vector<collect::Session::TemplateArgument>*
            explicit_arguments,
        collect::Session::PatternInstantiationCallbacks& callbacks,
        SrcLoc loc,
        bool ignore_top_level_exception_spec = false);
    cir::TypeId deduce_class_template_initialization_type(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::ExprResult>& arguments,
        SrcLoc loc,
        CtadInitializationKind initialization_kind,
        const collect::ExprResult* braced_initializer = nullptr,
        bool* selected_aggregate_candidate = nullptr);
    cir::EntityId instantiate_function_template_by_clone(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        cir::EntityId declaration_shell = {},
        const collect::Session::TemplateArgumentBindings* exact_bindings =
            nullptr);
    cir::EntityId instantiate_member_function_template(
        const collect::Session::TemplateInfo& info,
        const std::vector<collect::Session::TemplateArgument>& arguments,
        SrcLoc loc,
        cir::EntityId declaration_shell = {},
        const collect::Session::TemplateArgumentBindings* exact_bindings =
            nullptr);
    int pending_template_closes_ = 0;
    FunctionDeclaratorResult handle_out_of_line_function(
        const ParsedDeclarator& declarator,
        std::vector<ParsedParam> body_params,
        std::vector<collect::ParamInput> collect_params,
        cir::TypeRef result_type,
        std::vector<NodeId>& children,
        collect::DeclFlags flags);
    collect::DeclResult handle_typedef_declarator(const ParsedDeclarator& declarator);
    bool validate_literal_operator_declaration(
        const ParsedDeclarator& declarator,
        const collect::Session::TemplateInfo* template_info,
        bool is_friend);
    bool validate_symbolic_operator_membership(
        const ParsedDeclarator& declarator,
        const collect::DeclFlags& flags);
    FunctionDeclaratorResult handle_function_declarator(ParsedDeclarator declarator,
                                                        std::vector<NodeId>& children,
                                                        collect::DeclFlags flags);
    FunctionDeclaratorResult handle_abbreviated_function_template(
        ParsedDeclarator declarator,
        collect::Session::TemplateInfo info,
        std::vector<NodeId>& children,
        collect::DeclFlags flags,
        size_t definition_begin,
        bool top_level);
    collect::DeclResult handle_variable_declarator(const ParsedDeclarator& declarator,
                                                   bool top_level,
                                                   std::vector<NodeId>& children,
                                                   collect::DeclFlags flags,
                                                   bool structured_binding_backing = false);
    collect::StructuredBindingTupleInput resolve_structured_binding_tuple(
        const collect::DeclResult& backing,
        size_t binding_count,
        size_t pack_position,
        SrcLoc loc);
    NodeId parse_type_name(cir::TypeId* type_out = nullptr,
                           bool* is_typedef_out = nullptr,
                           StorageClass* storage_class_out = nullptr,
                           cir::TypeRef* type_ref_out = nullptr,
                           cir::Fragment* vla_bounds_out = nullptr,
                           bool* type_originates_from_template_parameter_out = nullptr,
                           TypeParseContext context = TypeParseContext{});

    ParsedDecl parse_objc_at_declaration();
    ParsedExpr parse_objc_at_expression();
    ParsedExpr parse_objc_message_expression();
    std::string objc_directive_spelling() const;
    bool take_objc_selector_piece(std::string& piece);
    ParsedDecl parse_objc_class_forward(size_t begin);
    ParsedDecl parse_objc_protocol(size_t begin);
    void parse_objc_property(cir::EntityId container,
                             std::vector<NodeId>& children);
    std::vector<std::string> parse_objc_angle_name_list(bool* saw_modifiers);
    ParsedStmt parse_objc_at_statement();
    bool objc_for_in_ahead() const;
    ParsedStmt parse_objc_for_in_statement();
    void skip_objc_angle_suffix();
    ParsedDecl parse_objc_interface(size_t begin);
    ParsedDecl parse_objc_implementation(size_t begin);
    void parse_objc_ivar_block(cir::EntityId interface,
                               std::vector<NodeId>& children);
    std::optional<collect::ObjCMethodInput> parse_objc_method_signature(
        std::vector<NodeId>& children);
    NodeId parse_record_specifier(cir::TypeId* type_out = nullptr);
    NodeId parse_enum_specifier(cir::TypeId* type_out = nullptr);
    ParsedDeclarator parse_declarator(
        cir::TypeRef base_type,
        bool allow_abstract = false,
        TypeParseContext context = TypeParseContext{});
    NodeId parse_name_node(NodeKind kind);
    ParsedParam parse_parameter(
        bool instantiate_default_argument = false,
        TypeParseContext context = TypeParseContext{});
    void rewrite_abbreviated_function_parameter(
        DeclarationParser& owner,
        ParsedDeclarator& parameter,
        bool is_parameter_pack,
        uint32_t function_parameter_index,
        const std::vector<std::optional<ParsedTypeConstraint>>& constraints,
        SrcLoc loc);
    bool append_concrete_type_parameter_pack(
        ParsedParam param,
        std::vector<ParsedParam>& destination);
    void append_decorated_parameter_pack(
        ParsedParam& pattern_param,
        const std::vector<collect::Session::ParameterPackIdentity>& packs,
        size_t pattern_cursor,
        size_t pattern_last_consumed_raw_end,
        std::vector<ParsedParam>& destination);
    std::vector<ParsedParam> parse_parameter_list(
        bool instantiate_default_arguments = false,
        TypeParseContext context = TypeParseContext{},
        bool* is_variadic_out = nullptr,
        const std::function<void(ParsedParam&, uint32_t)>&
            on_finalized_parameter = {},
        ParameterListPolicy policy = ParameterListPolicy::Function);
    bool is_attribute_start() const;
    ParsedAttributes try_parse_attributes();
    ParsedAttributes try_parse_standard_or_gnu_attributes();
    ParsedAttribute parse_alignas_attribute();
    ParsedAttributes parse_gnu_attribute_list();
    ParsedAttributes parse_cxx_standard_attribute_list();
    ParsedAttribute parse_single_gnu_attribute();
    NodeId parse_gnu_attribute_syntax();
    NodeId parse_asm_label_syntax(std::string* label_out = nullptr);
    NodeId parse_cxx_standard_attribute_syntax();
    bool declaration_attributes_terminate_template_head_constraint();
    ParsedStmt parse_statement();
    ParsedStmt parse_statement_inner();
    ParsedStmt parse_compound_statement();
    ParsedStmt parse_return_statement();
    ParsedStmt parse_co_return_statement();
    ParsedStmt parse_if_statement();
    bool cxx_condition_is_declaration();
    ParsedExpr parse_cxx_condition_declaration();
    bool cxx_if_has_init_statement() const;
    NodeId skip_discarded_if_substatement();
    void skip_discarded_parenthesized_tokens();
    void skip_discarded_statement_tokens();
    ParsedStmt parse_while_statement();
    ParsedStmt parse_do_while_statement();
    ParsedStmt parse_for_statement();
    ForControlScan scan_for_control() const;
    ParsedStmt parse_range_for_statement(size_t begin,
                                         SrcLoc loc,
                                         collect::ForControl control,
                                         bool has_init_statement);
    ParsedStmt parse_expansion_statement();
    RangeDeclarationRecipe parse_range_declaration(
        RangeDeclarationContext context);
    cir::TypeId deduce_auto_copy_list_type(
        const collect::ExprResult& initializer,
        SrcLoc loc);
    collect::DeclResult materialize_range_declaration(
        const RangeDeclarationRecipe& declaration,
        collect::ExprResult initializer);
    ParsedStmt parse_switch_statement();
    ParsedStmt parse_case_or_default_statement();
    ParsedStmt parse_label_statement();
    ParsedStmt parse_local_label_declaration_statement();
    ParsedStmt parse_goto_statement();
    ParsedStmt parse_asm_statement();
    ParsedStmt parse_expression_statement();
    StmtDeclDisambiguation classify_stmt_or_decl();
    bool probe_declaration_statement_start();
    bool probe_expression_statement_start();
    struct PackExpansionPattern {
        NodeId syntax = InvalidNodeId;
        std::vector<collect::Session::ParameterPackIdentity> packs;
        size_t replay_cursor = 0;
        size_t replay_last_consumed_raw_end = 0;
        size_t replay_end_cursor = 0;
        size_t after_ellipsis_cursor = 0;
        size_t after_ellipsis_last_consumed_raw_end = 0;
        SrcLoc ellipsis_loc{};

        bool has_pack_names() const {
            return !packs.empty();
        }
    };
    bool expression_list_element_has_pack_ellipsis(
        TokenType first_terminator,
        TokenType second_terminator) const;
    bool template_argument_has_pack_ellipsis() const;
    ParsedExpr parse_template_argument_constant_expression();
    bool at_template_argument_expression_close() const;
    std::optional<PackExpansionPattern> try_parse_pack_expansion_pattern(
        const std::function<void()>& parse_pattern,
        bool expect_trailing_ellipsis = true);
    std::optional<size_t> resolve_pack_expansion_element_count(
        const PackExpansionPattern& pattern,
        bool* dependent);
    cir::TemplateValuePackReference retained_pack_reference(
        const collect::Session::ParameterPackIdentity& pack);
    void replay_pack_expansion_elements(
        const PackExpansionPattern& pattern,
        size_t count,
        const std::function<void(size_t element_index)>& replay_element);
    void parse_pack_expansion_pattern_deferred(
        const std::function<void()>& parse_pattern);
    std::optional<PackExpansionPattern>
    try_parse_expression_pack_expansion(TokenType terminator);
    bool expand_expression_pack(const PackExpansionPattern& pattern,
                                std::vector<collect::ExprResult>& elements);
    struct ParsedExpressionList {
        std::vector<NodeId> syntax;
        std::vector<collect::ExprResult> sem;
        bool has_dependent_pack_expansion = false;
    };
    ParsedExpressionList parse_expression_list(TokenType terminator);
    ParsedExpr parse_expression(PrecLevel min_prec = PrecLevel::COMMA);
    ParsedExpr parse_assignment_expression();
    ParsedExpr parse_conditional_expression();
    ParsedExpr parse_constraint_expression();
    uint32_t normalize_direct_constraint_expression_syntax(
        NodeId syntax,
        collect::Session::NormalizedConstraint& normal_form);
    uint32_t expand_concept_pack_fold_constraints(
        collect::Session::NormalizedConstraint& normal_form,
        uint32_t root,
        SrcLoc loc);
    void stamp_constraint_declaration_keys(
        collect::Session::NormalizedConstraint& normal_form,
        const std::vector<collect::Session::TemplateParameter>& parameters);
    bool parse_and_validate_constraint_expression(SrcLoc loc,
                                                  size_t& begin,
                                                  size_t& end,
                                                  std::optional<bool>* value_out =
                                                      nullptr,
                                                  collect::Session::
                                                      NormalizedConstraint*
                                                          normal_form_out =
                                                              nullptr);
    ParsedExpr parse_throw_expression();
    ParsedExpr parse_yield_expression();
    ParsedStmt parse_try_statement();
    ParsedStmt parse_constructor_function_try();
    bool parse_handler_sequence(collect::TryControl& control,
                                std::vector<NodeId>& children);
    size_t skip_function_try_block_tokens();
    ParsedExpr parse_binary_expression(PrecLevel min_prec);
    ParsedExpr parse_cast_expression();
    NodeId retain_replayed_fold_operand_syntax(
        size_t operand_cursor,
        size_t operand_last_consumed_raw_end,
        size_t operand_end_cursor,
        SrcLoc ellipsis_loc);
    ParsedExpr retain_replayed_fold_operand_semantics(
        size_t operand_cursor,
        size_t operand_last_consumed_raw_end,
        size_t operand_end_cursor,
        size_t restore_cursor,
        size_t restore_last_consumed_raw_end,
        SrcLoc ellipsis_loc,
        std::vector<collect::Session::ParameterPackIdentity>* packs = nullptr);
    bool parse_requires_parameter_list(
        std::vector<NodeId>& children,
        collect::Session::PrototypeParameterScope& parameter_scope);
    ParsedRequiresRequirement parse_requires_type_requirement();
    ParsedRequiresRequirement parse_requires_compound_requirement();
    ParsedRequiresRequirement parse_requires_nested_requirement();
    ParsedExpr parse_requires_expression();
    ParsedExpr parse_unary_expression();
    ParsedExpr parse_statement_expression();
    ParsedExpr parse_block_literal_expression();
    ParsedExpr parse_lambda_expression();
    std::optional<ParsedExpr> parse_cxx_named_cast_expression();
    ParsedExpr parse_postfix_expression();
    ParsedExpr parse_postfix_suffixes(ParsedExpr expr);
    ParsedExpr parse_primary_expression();
    std::optional<ParsedExpr> parse_direct_unary_left_fold_expression();
    std::optional<ParsedExpr> parse_direct_unary_right_fold_expression();
    std::optional<ParsedExpr> parse_replayed_unary_left_fold_expression();
    std::optional<ParsedExpr> parse_replayed_unary_right_fold_expression();
    std::optional<ParsedExpr> parse_replayed_binary_left_fold_expression();
    std::optional<ParsedExpr> parse_replayed_binary_right_fold_expression();
    std::optional<ParsedExpr> parse_direct_binary_left_fold_expression();
    std::optional<ParsedExpr> parse_direct_binary_right_fold_expression();
    std::optional<ParsedExpr> parse_invalid_fold_expression();
    ParsedExpr parse_generic_selection_expression();
    std::optional<ParsedExpr> parse_builtin_primary_expression();
    ParsedExpr parse_init_list_expression(
        bool* has_dependent_pack_expansion = nullptr);
    bool is_init_designator_start() const;
    ParsedDesignatorList parse_designator_list();
    ParsedDesignatorList parse_offsetof_designator_list();
    ParsedAsmString parse_asm_string_literal(std::string_view context);
    bool at_asm_section_colon(int pending_colons) const;
    bool match_asm_section_colon(int& pending_colons);
    ParsedAsmOperandList parse_asm_operand_list(int& pending_colons);
    std::vector<NodeId> parse_asm_clobber_list(
        std::vector<std::string>& clobbers,
        int& pending_colons);
    std::vector<NodeId> parse_asm_goto_label_list(std::vector<std::string>& labels);
    NodeId parse_error_node(std::string message, size_t begin, size_t end);
    NodeId make_node(NodeKind kind,
                     size_t begin,
                     size_t end,
                     const std::vector<NodeId>& children = {},
                     NodePayload payload = {},
                     uint16_t flags = NodeFlagNone,
                     uint16_t opcode = 0);

    bool is_type_start(TokenType type);
    bool is_decl_specifier(TokenType type);
    bool is_identifier_token(TokenType type) const;
    bool is_integer_token(TokenType type) const;
    bool is_floating_token(TokenType type) const;
    bool is_imaginary_token(TokenType type) const;
    UnaryOperator unary_operator_for(TokenType type) const;
    BinaryOperator binary_operator_for(TokenType type) const;
    bool is_right_associative(TokenType type) const;
    void adjust_function_parameter_type(cir::TypeRef& type_ref);
    size_t skip_balanced_until_semicolon();
    size_t skip_balanced_until_semicolon_or_brace();
    size_t skip_until_statement_boundary();
    bool span_has_macro_expansion(size_t begin, size_t end) const;
    void diagnose(DiagnosticLevel level, std::string message, SrcLoc loc);
    void diagnose_flagged(WarningId id, std::string message, SrcLoc loc);
    bool in_constraint_substitution_failure_context() const {
        return constraint_substitution_failure_depth_ > 0;
    }
    void note_constraint_substitution_failure() {
        if (in_constraint_substitution_failure_context()) {
            constraint_substitution_failure_ = true;
        }
    }
    void apply_weak_directives(bool apply_all);
    void apply_visibility_directives(bool apply_all);
    SrcLoc loc_for_index(size_t index) const;
    std::string token_range_display(size_t begin, size_t end) const;
    cir::TypeRef parse_splice_type_specifier();
    size_t begin_tentative_context(TentativeMode mode);
    void commit_tentative_context(size_t context_id);
    void rollback_tentative_context(size_t context_id);
    bool is_in_tentative_context() const { return !tentative_context_stack_.empty(); }
    ParserCheckpoint capture_parser_checkpoint() const;
    void restore_parser_checkpoint(const ParserCheckpoint& checkpoint);

    const std::vector<Token>& tokens_;
    LangOptions lang_opts_;
    std::shared_ptr<SourceManager> source_manager_;
    size_t weak_directives_applied_ = 0;
    size_t visibility_directives_applied_ = 0;
    collect::Session& collect_session_;
    Tree tree_;
    ParserAnnotationStore annotation_store_;
    std::vector<std::optional<ConstraintConceptIdSyntaxInfo>>
        constraint_concept_id_syntax_;
    std::vector<std::optional<ConstraintFoldOperandSyntaxInfo>>
        constraint_fold_operand_syntax_;
    bool retain_constraint_normal_form_syntax_ = false;
    size_t constraint_expression_replay_end_ = SIZE_MAX;
    size_t deferred_static_initializer_capture_depth_ = 0;
    cir::EntityId deferred_static_initializer_dependency_{};
    bool deferred_static_initializer_probe_transaction_active_ = false;
    std::vector<
        collect::Session::TemplateInfo::StaticDataMemberInitializer>*
        static_data_member_initializer_capture_ = nullptr;
    bool validating_literal_operator_template_definition_ = false;
    size_t template_head_constraint_attribute_boundary_depth_ = 0;
    std::vector<size_t> template_argument_expression_begins_;
    size_t requires_expression_template_context_depth_ = 0;
    std::vector<Diagnostic> diagnostics_;
    bool module_unit_replay_ = false;
    cir::ModuleAttachmentId module_replay_unit_{};
    ModuleParserRegistry local_module_parser_registry_;
    ModuleParserRegistry* module_parser_registry_ =
        &local_module_parser_registry_;
    std::vector<size_t> cooked_to_raw_;
    size_t cursor_ = 0;
    size_t last_consumed_raw_end_ = 0;
    std::vector<TentativeContextFrame> tentative_context_stack_;
    size_t next_tentative_context_id_ = 1;
    size_t constraint_substitution_failure_depth_ = 0;
    bool constraint_substitution_failure_ = false;
    bool qualified_declarator_template_head_wins_ = false;
};

} // namespace aburi::syntax

#endif // ABURI_SYNTAX_PARSER_H
