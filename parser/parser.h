#ifndef ABURI_PARSER_H
#define ABURI_PARSER_H
#include <vector>
#include <memory>
#include "../ast/ast.h"
#include "../ast/ast_context.h"
#include "../helpers/casting.h"
#include "../lexer.h"
#include "../ast/types.h"
#include "../abi/target_info.h"
#include "../ast/symbols.h"
#include "../ast/attributes.h"
#include "../abi/darwin_blocks.h"
#include "../lang_options.h"
#include "../diagnostics.h"
#include "../collect/collect.h"
#include "tentative_syntax_probe.h"
#include <cctype>
#include <chrono>
#include <cstdint>
#include <source_location>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

class PerfProfiler;

enum class PrecLevel {
    UNKNOWN = 0,
    COMMA = 1, // ,
    ASSIGNMENT = 2, // =, +=, -=, *=, /=, %=, <<= (this is right associative)
    CONDITIONAL = 3, // ?
    LOGICAL_OR = 4, // ||
    LOGICAL_AND = 5, // &&
    INCLUSIVE_OR = 6, // |
    EXCLUSIVE_OR = 7, // ^
    AND = 8, // &
    EQUALITY = 9, // ==, !=
    RELATIONAL = 10, // < <= > >=
    THREE_WAY = 11, // <=>
    SHIFT, // << >>
    ADDSUB, // +, -
    MULTDIV, // *, /, %
    PM, // .* ->*

};
PrecLevel get_prec(TokenType tok);

inline bool is_gnu_attribute_token(const Token &t) {
    if (t.type == TokenType::ATTRIBUTE_KW) {
        return true;
    }
    if (t.type != TokenType::IDENTIFIER) {
        return false;
    }
    return t.value == "__attribute__" || t.value == "__attribute";
}
struct DeclarationRet {
    std::string name; // name of the declaration
    CType type_constructed; // what we know of the type so far
    DeclarationRet(): name(""), type_constructed(CType()) {};
};
// tyehnically we only need to keep track of new types in the parser for now
struct DeclarationParser;
class Parser {
private:
    struct CxxTentativeDisambiguationState {
        // Future C++ hook: dependent-name lookup where 'typename' may be required.
        bool typename_context_dependent_lookup = false;
        // Future C++ hook: prefer template-id interpretation over relational expression.
        bool template_id_vs_relational = false;
        // Future C++ hook: declaration-vs-expression bias in ambiguous contexts.
        bool prefer_declaration = true;
    };

    struct TentativeParserState {
        size_t token_idx = 0;
        TokenMgnt::SplitTokenState split_token_state;
        std::shared_ptr<CType> func_type;
        LanguageLinkage active_language_linkage = LanguageLinkage::None;
        std::unordered_set<std::string> seen_stmt_labels;
        std::unordered_set<std::string> stmt_labels;
        std::vector<std::unordered_map<std::string, std::string>> local_label_scopes;
        uint64_t local_label_unique_id = 0;
        int loop_count = 0;
        int switch_count = 0;
        bool has_default = false;
        std::unordered_set<int> case_values;
        uint32_t template_pattern_depth = 0;
        uint32_t template_parameter_depth = 0;
        uint32_t template_argument_expression_depth = 0;
        uint32_t template_argument_group_depth = 0;
        uint32_t cpp_template_declaration_subject_parse_depth = 0;
    };

    struct ParsedCppTypeNameSpecifier {
        QualType type = nullptr;
        std::shared_ptr<Symbol> typedef_symbol = nullptr;
        std::string spelling;
    };

    enum class CppTypeNameParseContext {
        General,
        BaseSpecifier,
        TypeRequirement,
    };

    struct CppTypeComponentResolution {
        QualType type = nullptr;
        std::shared_ptr<Symbol> typedef_symbol = nullptr;
        bool names_current_instantiation_member = false;

        explicit operator bool() const {
            return static_cast<bool>(type);
        }
    };

    struct CppCtorBaseInitializerTarget {
        QualType type = nullptr;
        std::string base_name;
        bool is_virtual = false;
        bool found_non_base_type = false;

        explicit operator bool() const {
            return static_cast<bool>(type);
        }
    };

    struct CppDependentOwnerAnalysis {
        QualType owner_type = nullptr;
        bool is_current_instantiation = false;
        bool is_dependent = false;

        bool is_dependent_context() const {
            return is_current_instantiation || is_dependent;
        }

        bool requires_typename_keyword() const {
            return is_dependent && !is_current_instantiation;
        }

        bool requires_template_keyword() const {
            return is_dependent && !is_current_instantiation;
        }
    };

    struct CppQualifiedNameComponent {
        std::string name;
        std::vector<TemplateArgument> template_arguments;
        bool has_template_argument_list = false;
        bool preceded_by_template_keyword = false;
        SrcLoc loc;

        std::string spelling() const {
            if (!has_template_argument_list) {
                return name;
            }
            std::string spelled = name;
            spelled += "<";
            for (size_t idx = 0; idx < template_arguments.size(); ++idx) {
                if (idx > 0) {
                    spelled += ", ";
                }
                spelled += template_arguments[idx].to_string();
            }
            spelled += ">";
            return spelled;
        }
    };

    struct CppQualifiedOwnerChainResolution {
        std::shared_ptr<Scope> lookup_scope;
        const DeclContext* lookup_context = nullptr;
        QualType owner_type = nullptr;
        bool is_current_instantiation = false;
        bool is_dependent = false;
        bool lookup_failed = false;
        std::vector<std::string> qualifier_spellings;
        std::string qualifier_chain_spelling;
        std::string failed_prefix_spelling;

        bool has_owner_type() const {
            return static_cast<bool>(owner_type);
        }

        bool is_dependent_context() const {
            return is_dependent || is_current_instantiation;
        }

        bool requires_template_keyword() const {
            return is_dependent && !is_current_instantiation;
        }

        bool requires_typename_keyword() const {
            return is_dependent && !is_current_instantiation;
        }
    };

    struct CppQualifiedOwnerSeed {
        QualType owner_type = nullptr;
        std::string spelling;
        SrcLoc loc;
        bool is_current_instantiation = false;
        bool is_dependent = false;
        bool requires_class_or_enum = false;
    };

    struct PendingCppExplicitSpecializationInfo {
        const ClassTemplateDecl* owner_primary_template = nullptr;
        const FunctionTemplateDecl* primary_member_template = nullptr;
        std::vector<TemplateArgument> specialization_arguments;
        std::vector<TemplateArgument> owner_specialization_arguments;
        const Decl* primary_member_decl = nullptr;
    };

    struct ScopeContextSnapshot {
        std::shared_ptr<Scope> scope;
        std::shared_ptr<DeclContext> decl_context;
    };

    struct QualifiedDeclaratorInfo {
        bool has_global_qualifier = false;
        std::vector<std::string> qualifiers;
        std::shared_ptr<DeclContext> target_context;
        std::shared_ptr<Scope> target_scope;
        const ObjectDecl* owner_record_decl = nullptr;
        const ClassTemplateDecl* owner_class_template = nullptr;
        QualType owner_type = nullptr;
        std::vector<TemplateArgument> owner_template_arguments;
        bool owner_has_specialization_argument_list = false;
        bool targets_template_pattern = false;
        const RecordSemanticState::Method* method_match = nullptr;
        const RecordSemanticState::MethodTemplate* method_template_match = nullptr;
        std::vector<TemplateArgument> method_template_specialization_arguments;
        const RecordSemanticState::StaticDataMember* static_data_match = nullptr;
        SrcLoc loc;
    };

    struct QualifiedDeclaratorContext {
        ScopeContextSnapshot scope_snapshot;
        QualifiedDeclaratorInfo info;
    };

    enum class DeclaratorHandlingResult : uint8_t {
        Continue,
        Return
    };

    struct TentativeContextFrame {
        size_t id = 0;
        TentativeParserState parser_checkpoint;
        DiagnosticEngine::Checkpoint diag_checkpoint;
        CxxTentativeDisambiguationState cxx_disambiguation_state;
    };

public:
    enum class TPResult : uint8_t {
        True,
        False,
        Ambiguous,
        Error
    };

private:
    enum class CxxStmtDisambiguation : uint8_t {
        Declaration,
        Expression,
        Ambiguous,
        Invalid
    };

public:

    class TentativeParsingAction {
    public:
        explicit TentativeParsingAction(
            Parser& parser,
            std::source_location loc = std::source_location::current());
        TentativeParsingAction(const TentativeParsingAction&) = delete;
        TentativeParsingAction& operator=(const TentativeParsingAction&) = delete;
        ~TentativeParsingAction();

        void commit();
        void revert();
        bool is_active() const { return active_; }

    protected:
        Parser& parser_;
        size_t context_id_ = 0;
        bool active_ = true;
        PerfProfiler* tentative_profiler_ = nullptr;
        const char* tentative_file_ = "";
        const char* tentative_function_ = "";
        uint32_t tentative_line_ = 0;
        size_t tentative_start_token_idx_ = 0;
        size_t tentative_depth_ = 0;
        std::chrono::steady_clock::time_point tentative_start_;

        void record_tentative_outcome(bool committed);
    };
    // for optics only, this code is the same as class above
    class RevertingTentativeParsingAction final : public TentativeParsingAction {
    public:
        explicit RevertingTentativeParsingAction(
            Parser& parser,
            std::source_location loc = std::source_location::current())
            : TentativeParsingAction(parser, loc) {}
        ~RevertingTentativeParsingAction() { revert(); }
    };

    TokenMgnt tok_mgnt;
    std::shared_ptr<ASTContext> ast_ctx;
private:
    size_t begin_tentative_context();
    void commit_tentative_context(size_t context_id);
    void rollback_tentative_context(size_t context_id);
    bool is_in_tentative_context() const;

    void restore_tentative_context_frame(const TentativeContextFrame& frame);
    TentativeParserState capture_tentative_state();
    void restore_tentative_state(const TentativeParserState& state);

    // function stuff
    std::shared_ptr<CType> func_type = nullptr; // todo: update
    std::unordered_set<std::string> seen_stmt_labels;
    std::unordered_set<std::string> stmt_labels;
    std::vector<std::unordered_map<std::string, std::string>> local_label_scopes_;
    uint64_t local_label_unique_id_ = 0;
    int loop_count = 0;
    int switch_count = 0;
    // switch stuff
    bool has_default = false;
    std::unordered_set<int> case_values;
  //  std::shared_ptr<Types> types;
    std::shared_ptr<TypeContext> type_ctx;
    Token current_token();
    size_t get_token_idx();

    void set_token_idx(size_t idx);

    Token peek_token(size_t offset = 1);

    Token peek_token_shortcut(size_t offset);
    bool skip_balanced_tokens_for_lookahead(size_t& offset,
                                            TokenType open_tok,
                                            TokenType close_tok);
    bool skip_attribute_specifier_sequence_for_lookahead(size_t& offset);

    void advance();
    bool gentle_check_and_consume(TokenType type);
    bool gentle_check(TokenType type);
    void check_custom(TokenType type, std::string &message);
    void check_and_consume(TokenType type);
    void check(TokenType type);
    void error(std::string err);

    void error_custloc(std::string err, SrcLoc loc);

    // Error recovery: skip to next synchronization point
    void skip_to_stmt_sync_point();
    void skip_to_next_top_level_decl();
    // Reset parser state to "between top-level declarations"
    void reset_top_level_state();
    void skip_to_field_sync_point();
    void skip_to_enum_sync_point();
    void skip_to_init_list_sync_point();
    void skip_to_param_sync_point();

    std::unique_ptr<Expr> parse_assignment_expression();

    std::unique_ptr<Stmt> parse_goto();

    std::unique_ptr<Stmt> parse_break();

    std::unique_ptr<Stmt> parse_continue();

    std::unique_ptr<Expr> parse_primary_expression();
    std::unique_ptr<Expr> parse_cpp_requires_expression();
    std::optional<CppTypeConstraint> parse_cpp_type_constraint(
        bool diagnose_on_failure = true);
    bool can_start_cpp_constrained_placeholder_type_specifier_for_lookahead();
    std::unique_ptr<Expr> parse_block_literal_expression();
    std::unique_ptr<Expr> parse_cpp_lambda_expression();
    bool is_lambda_declarator_parameter_clause_ahead();
    TemplateParameterList lower_generic_lambda_parameter_placeholders(
        std::vector<std::unique_ptr<Decl>>& parameters,
        TemplateParameterList template_parameters,
        const std::string& closure_name,
        uint32_t parameter_depth,
        SrcLoc lambda_loc);
    bool function_type_has_ordinary_cxx_auto_parameters(
        const std::shared_ptr<CType>& type) const;
    void validate_function_parameter_auto_placeholders(
        const std::shared_ptr<FunctionType>& function_type,
        SrcLoc loc);
    void lower_cxx_auto_function_parameter_placeholders(
        std::vector<std::unique_ptr<Decl>>& parameters,
        const std::shared_ptr<FunctionType>& function_type,
        TemplateParameterList& template_parameters,
        uint32_t parameter_depth,
        SrcLoc loc);
    TemplateParameterList* active_abbreviated_function_template_parameters();
    uint32_t active_abbreviated_function_template_parameter_depth() const;
    std::unique_ptr<Decl> wrap_abbreviated_function_template_if_needed(
        std::unique_ptr<Decl> function_decl,
        TemplateParameterList template_parameters,
        SrcLoc loc,
        bool publish_namespace_template);
    std::unique_ptr<Expr> maybe_parse_pack_expansion_expression(
        std::unique_ptr<Expr> expr);
    std::unique_ptr<Expr> parse_assignment_expression_with_optional_pack_expansion();
    std::unique_ptr<Expr> parse_call_argument_expression();
    std::unique_ptr<Expr> try_parse_fold_expression(SrcLoc lparen_loc);

    std::unique_ptr<Expr> parse_postfix_expression();

    std::unique_ptr<Expr> parse_unary_expression();

    std::unique_ptr<Expr> parse_cast_expression();
    void retain_type_specifier_decl_if_needed(DeclarationParser& decl_parser);

    bool is_init_designator_start();
    std::vector<Designator> parse_designator_list();
    std::unique_ptr<Expr> parse_init_list();
    std::unique_ptr<Expr> parse_paren_init_list();

    std::unique_ptr<Stmt> parse_return();

    std::unique_ptr<Stmt> parse_stmt_or_decl();
    std::unique_ptr<Decl> parse_static_assert_declaration();

    std::unique_ptr<Stmt> parse_if_stmt();
    std::optional<size_t> find_cpp_if_init_semicolon();
    ControlCondition parse_control_condition(TokenType terminator,
                                             const char* statement_name);
    bool should_parse_control_condition_as_declaration(
        TokenType terminator,
        const char* statement_name);
    ControlCondition parse_control_condition_declaration(
        TokenType terminator,
        const char* statement_name);

    std::unique_ptr<Stmt> parse_switch();

    std::unique_ptr<Stmt> parse_case_stmt();

    std::unique_ptr<Stmt> parse_default_stmt();

    std::unique_ptr<Stmt> parse_while_stmt();

    std::unique_ptr<Stmt> parse_do_while_stmt();

    std::unique_ptr<Stmt> parse_for_stmt();
    std::optional<size_t> find_cpp_range_for_colon_semicolon_count();
    CppRangeForDeclarationInfo parse_cpp_range_for_declaration();

    std::unique_ptr<Stmt> parse_stmt();
    std::unique_ptr<Stmt> parse_asm_stmt();
    std::string parse_asm_string_literal();
    std::unique_ptr<Stmt> parse_compound_stmt(std::shared_ptr<Scope> use_scope = nullptr);
    std::unique_ptr<Decl> parse_function(DeclarationParser *decl_parser,
                                         SrcLoc loc,
                                         std::shared_ptr<Symbol> predecl_sym = nullptr,
                                         TemplateParameterList*
                                             abbreviated_template_parameters_out = nullptr);
    void parse_kr_declaration_list(DeclarationParser *decl_parser,
                                   FuncDecl *func_decl,
                                   QualType visible_prototype_type);
    std::unique_ptr<Decl> parse_translation_unit();

    std::optional<std::vector<std::unique_ptr<Decl>>> try_parse_extern_linkage_declaration();
    std::optional<std::vector<std::unique_ptr<Decl>>> try_parse_cpp_standalone_record_declaration();
    std::optional<std::vector<std::unique_ptr<Decl>>> try_parse_special_declaration();
    void validate_declaration_start(Token start_token);
    void emit_declaration_head_side_decls(DeclarationParser& decl_parser,
        const std::shared_ptr<CType>& parsed_type,
        std::vector<std::unique_ptr<Decl>>& ret_vec);
    std::shared_ptr<CType> parse_declaration_head(Token start_token,
        DeclarationParser& decl_parser,
        std::vector<std::unique_ptr<Decl>>& ret_vec);
    QualifiedDeclaratorContext prepare_qualified_declarator_context(
        DeclarationParser& decl_parser);
    bool qualified_variable_types_compatible(QualType declared_type,
        QualType member_type);
    bool record_method_signature_matches(
        const RecordSemanticState::Method& method,
        const std::shared_ptr<CType>& parsed_decl_type,
        uint8_t parsed_trailing_cv_qualifiers);
    bool record_method_declarator_prefix_matches(
        const RecordSemanticState::Method& method,
        const std::shared_ptr<CType>& parsed_decl_type,
        uint8_t parsed_trailing_cv_qualifiers);
    bool build_cpp_member_declarator_expression_context(
        const DeclarationParser& decl_parser,
        const FunctionType& function_type,
        Collect::CppThisContext& cpp_this_context_out,
        QualType& record_lookup_type_out);
    bool build_cpp_current_record_declarator_expression_context(
        bool is_static_member,
        uint8_t cv_qualifiers,
        Collect::CppThisContext& cpp_this_context_out,
        QualType& record_lookup_type_out);
    bool active_template_parameter_list_matches(
        const TemplateParameterList& parameters);
    bool record_method_template_signature_matches(
        const RecordSemanticState::MethodTemplate& method_template,
        const std::shared_ptr<CType>& parsed_decl_type,
        uint8_t parsed_trailing_cv_qualifiers);
    bool record_method_template_explicit_specialization_matches(
        const RecordSemanticState::MethodTemplate& method_template,
        const std::shared_ptr<CType>& parsed_decl_type,
        uint8_t parsed_trailing_cv_qualifiers,
        const ClassTemplateDecl* owner_class_template,
        const std::vector<TemplateArgument>& owner_template_arguments,
        bool owner_has_specialization_argument_list,
        bool targets_template_pattern,
        SrcLoc declarator_loc,
        std::vector<TemplateArgument>& deduced_arguments_out);
    void resolve_qualified_declarator_match(
        QualifiedDeclaratorInfo& qualified_declarator,
        const DeclarationParser& decl_parser,
        const std::shared_ptr<CType>& parsed_decl_type);
    void merge_function_asm_label(DeclarationParser& decl_parser,
        const std::shared_ptr<Symbol>& sym,
        SrcLoc loc);
    void remap_out_of_line_primary_template_method(
        CppMethodDecl* method_decl,
        const ClassTemplateDecl* owner_class_template,
        SrcLoc declarator_loc);
    void remap_out_of_line_constructor_with_parameter_rebinds(
        CppConstructorDecl* ctor_decl,
        const std::unordered_map<const TemplateParameterDecl*,
                                 const TemplateParameterDecl*>& parameter_rebinds,
        SrcLoc declarator_loc);
    void remap_out_of_line_primary_template_static_member(
        QualType& declared_type,
        std::unique_ptr<Expr>& init_expr,
        const ClassTemplateDecl* owner_class_template,
        SrcLoc declarator_loc);
    DeclaratorHandlingResult handle_typedef_declarator(
        DeclarationParser& decl_parser,
        Token declarator_token,
        std::shared_ptr<CType>& parsed_decl_type,
        std::vector<ParsedAttribute>& trailing_attrs,
        bool declaration_is_constexpr,
        bool declaration_is_consteval,
        std::vector<std::unique_ptr<Decl>>& ret_vec);
    DeclaratorHandlingResult handle_function_declarator(
        DeclarationParser& decl_parser,
        Token declarator_token,
        const std::shared_ptr<CType>& parsed_decl_type,
        std::vector<ParsedAttribute>& trailing_attrs,
        StorageClass storage_class,
        bool declaration_is_constexpr,
        bool declaration_is_consteval,
        LanguageLinkage declaration_language_linkage,
        QualifiedDeclaratorInfo& qualified_declarator,
        std::vector<std::unique_ptr<Decl>>& ret_vec);
    DeclaratorHandlingResult handle_variable_declarator(
        DeclarationParser& decl_parser,
        Token declarator_token,
        const std::shared_ptr<CType>& parsed_decl_type,
        std::vector<ParsedAttribute>& trailing_attrs,
        StorageClass storage_class,
        bool declaration_is_constexpr,
        bool declaration_is_consteval,
        LanguageLinkage declaration_language_linkage,
        QualifiedDeclaratorInfo& qualified_declarator,
        std::optional<QualType>& first_cxx_auto_deduced_type,
        std::vector<std::unique_ptr<Decl>>& ret_vec);
    std::vector<std::unique_ptr<Decl>> parse_declaration();

    std::unique_ptr<Decl> parse_parameter_declaration();

    // === Record and declarator parsing ===
    // Owns struct/union/class syntax, class-member declaration matching, and
    // deferred inline member body replay. Ordinary record semantic completion
    // is delegated to Collect.
    std::unique_ptr<Decl> parse_struct_specifier();
    std::unique_ptr<Decl> parse_cpp_record_specifier(
        std::vector<TemplateArgument>* specialization_arguments_out = nullptr,
        bool* has_specialization_argument_list_out = nullptr,
        bool suppress_placeholder_type = false,
        const ClassTemplateDecl* current_primary_class_template = nullptr);
    CppCtorInitializer parse_cpp_ctor_mem_initializer(
        const std::string& record_name);
    std::vector<CppCtorInitializer> parse_cpp_ctor_mem_initializer_list(
        const std::string& record_name);
    std::unique_ptr<Decl> parse_cpp_constructor_member();
    std::unique_ptr<Decl> parse_cpp_destructor_member();
    std::unique_ptr<Decl> build_cpp_record_semantic_decl(
        const CppRecordDecl& record,
        std::optional<std::string> semantic_tag_name = std::nullopt,
        bool allow_parent_tag_lookup_for_non_definition = false);
    struct CppRecordDeferredParseContext {
        const CppRecordDecl& record;
        std::shared_ptr<ObjectType> record_type;
        RecordSemanticState semantic_state;
        const ObjectDecl* semantic_owner = nullptr;
        const ClassTemplateDecl* primary_class_template = nullptr;
        QualType current_instantiation_type = nullptr;
    };
    void build_cpp_record_parse_deferred_bodies(
        const CppRecordDeferredParseContext& ctx);
    const ObjectDecl* ensure_cpp_specialized_record_semantic_owner(
        CppRecordKind record_kind,
        const std::string& name,
        const std::vector<TemplateArgument>& specialization_arguments,
        SrcLoc loc,
        const ClassTemplateDecl* primary_class_template = nullptr,
        bool has_specialization_argument_list = false);
    template <typename TemplateDeclT>
    void prepare_cpp_template_pattern_record_impl(TemplateDeclT& class_template);
    void prepare_cpp_template_pattern_record(ClassTemplateDecl& class_template);
    void prepare_cpp_template_pattern_record(
        ClassTemplatePartialSpecializationDecl& class_template);
    void ensure_cpp_record_placeholder_type(const std::string& name,
                                            bool is_union_record,
                                            SrcLoc loc);
    const ObjectDecl* ensure_cpp_template_pattern_nested_record_semantics(
        CppRecordDecl& record);
    std::unique_ptr<ObjectDecl> take_cpp_transient_semantic_object_decl(
        const std::string& tag_name);
    std::unique_ptr<ObjectDecl> take_cpp_transient_semantic_object_decl(
        const ObjectDecl* target_decl);
    bool can_parse_namespace_scope_template_declaration() const;
    bool is_in_template_pattern_context() const;
    bool is_parsing_cpp_record_body() const;
    std::string current_cpp_record_qualifier_prefix() const;
    std::shared_ptr<Scope> nearest_cpp_friend_namespace_scope() const;
    void apply_cpp_friend_namespace_prefix(FuncDecl* function_decl) const;
    void register_cpp_friend_function_template_decl(FriendDecl* friend_decl);
    bool active_template_parameters_match_for_redeclaration(
        const TemplateParameterList& parameters) const;
    const FunctionTemplateDecl*
    find_hidden_friend_function_template_redeclaration(
        const FuncDecl* function_decl) const;
    const FunctionTemplateDecl*
    find_hidden_friend_function_template_redeclaration(
        const FunctionTemplateDecl* function_template) const;
    const ClassTemplateDecl*
    find_hidden_friend_class_template_redeclaration(
        const std::string& template_name,
        const std::shared_ptr<Scope>& namespace_scope,
        const ClassTemplateDecl* current_template) const;
    const ClassTemplateDecl* materialize_cpp_hidden_friend_class_template_decl(
        FriendDecl* friend_decl,
        TemplateParameterList parameters,
        std::unique_ptr<Expr> associated_constraint,
        SrcLoc template_loc);
    QualType lookup_friend_access_type_for_current_function_template_redeclaration(
        const FuncDecl* function_decl) const;
    void propagate_function_template_friend_access(
        FunctionTemplateDecl* function_template);

    // === Template and qualified-name parsing ===
    // These helpers are parser-owned classification/resolution seams used by
    // both declaration and expression parsing. Keep semantic construction in
    // Collect, but keep qualified/dependent-name parsing decisions here.
    std::vector<std::unique_ptr<Decl>> parse_cpp_template_declaration();
    std::vector<std::unique_ptr<Decl>> parse_cpp_explicit_specialization_declaration(
        Token template_tok,
        bool member_template_declaration,
        bool angle_brackets_already_consumed = false);
    bool is_cpp_deduction_guide_declaration_start();
    std::unique_ptr<CppDeductionGuideDecl> parse_cpp_deduction_guide_declaration(
        TemplateParameterList template_parameters = {},
        std::unique_ptr<Expr> leading_requires_clause = nullptr,
        SrcLoc template_loc = SrcLoc());
    bool cpp_template_parameter_lists_match_for_redeclaration(
        const TemplateParameterList& lhs,
        const TemplateParameterList& rhs) const;
    bool cpp_type_matches_for_template_redeclaration(
        QualType lhs,
        QualType rhs,
        bool ignore_top_level_qualifiers,
        SrcLoc loc,
        unsigned depth = 0) const;
    bool cpp_function_type_matches_for_template_redeclaration(
        QualType existing_type,
        QualType current_type,
        SrcLoc loc) const;
    bool cpp_function_template_decls_match_for_redeclaration(
        const FunctionTemplateDecl* existing,
        const FunctionTemplateDecl* current) const;
    bool cpp_template_decls_match_for_redeclaration(
        const TemplateDecl* existing,
        const TemplateDecl* current,
        const std::string* current_template_name = nullptr) const;
    const TemplateDecl* resolve_matching_primary_template_redeclaration(
        const std::string& template_name,
        LookupNamespace lookup_namespace,
        const TemplateDecl* current_template) const;
    void set_primary_template_canonical_identity(
        TemplateDecl* template_decl,
        const std::string& template_name,
        LookupNamespace lookup_namespace);
    void validate_template_default_argument_rules(
        const TemplateDecl* template_decl);
    void finalize_primary_template_decl(
        TemplateDecl* template_decl,
        const std::string& template_name,
        LookupNamespace lookup_namespace);
    VariableTemplateDecl* try_publish_pending_primary_variable_template_pattern(
        const std::string& name,
        QualType declared_type,
        const std::shared_ptr<Symbol>& declared_sym,
        StorageClass storage_class,
        bool is_inline,
        bool is_constexpr,
        bool is_thread_local,
        bool is_block_byref,
        const std::optional<std::string>& asm_label,
        LanguageLinkage language_linkage,
        SrcLoc loc);
    TemplateParameterList parse_cpp_template_parameter_list(uint32_t depth);
    std::unique_ptr<Expr> parse_cpp_constraint_expression();
    std::unique_ptr<Expr> parse_cpp_template_constraint_expression();
    std::unique_ptr<Expr> parse_cpp_constraint_logical_or_expression();
    std::unique_ptr<Expr> parse_cpp_constraint_primary_expression();
    bool is_cpp_template_argument_list_close_here();
    bool is_cpp_template_argument_boundary_here();
    bool skip_balanced_group_for_template_id_lookahead(
        size_t& offset,
        TokenType open_tok,
        TokenType close_tok);
    bool skip_template_argument_list_for_expression_probe(size_t& offset);
    const TemplateParameterDecl* find_active_template_parameter(
        std::string_view name) const;
    const TemplateParameterDecl* find_active_template_parameter_pack(
        std::string_view name) const;
    const TemplateNonTypeParmDecl* find_active_non_type_template_parameter(
        const Symbol* sym) const;
    bool expr_depends_on_active_template_parameter(const Expr* expr) const;
    struct ParsedCppTemplateTypeArgument {
        QualType type;
        bool followed_by_left_brace = false;
    };
    bool can_direct_parse_cpp_template_type_argument_for_lookahead();
    std::optional<ParsedCppTemplateTypeArgument>
    try_parse_cpp_direct_template_type_argument();
    std::unique_ptr<Expr>
    parse_cpp_typed_braced_template_argument_expr_after_type(
        QualType target_type);
    std::optional<TemplateArgument> try_parse_cpp_template_name_argument();
    TemplateArgument parse_cpp_template_argument();
    std::vector<TemplateArgument> parse_cpp_template_argument_list();
    void consume_cpp_template_argument_list_close();
    bool try_consume_cpp_decltype_specifier_for_lookahead();
    bool can_start_cpp_named_type_specifier_for_lookahead();
    QualType parse_cpp_decltype_type_specifier();
    std::optional<ParsedCppTypeNameSpecifier> try_parse_cpp_named_type_specifier(
        CppTypeNameParseContext context = CppTypeNameParseContext::General);
    std::unique_ptr<Expr> try_parse_cpp_constraint_name_expression(
        bool append_placeholder_type_argument,
        uint32_t depth,
        uint32_t index,
        bool is_parameter_pack,
        SrcLoc start_loc = SrcLoc());
    CppTypeComponentResolution resolve_cpp_unqualified_type_component(
        const std::string& component_name,
        const std::vector<TemplateArgument>& component_arguments,
        bool component_has_template_argument_list,
        SrcLoc component_loc);
    QualType build_cpp_current_instantiation_type(
        const ClassTemplateDecl* primary_template,
        std::string_view type_name,
        const std::vector<TemplateArgument>& arguments) const;
    std::optional<std::vector<TemplateArgument>>
    build_cpp_current_instantiation_arguments(
        const ClassTemplateDecl* class_template,
        SrcLoc loc);
    QualType build_cpp_primary_current_instantiation_type(
        const ClassTemplateDecl* class_template,
        std::string_view type_name,
        SrcLoc loc);
    QualType try_build_cpp_injected_current_instantiation_type(
        std::string_view type_name,
        SrcLoc loc);
    std::optional<std::vector<TemplateArgument>>
    complete_cpp_template_id_arguments(
        const TemplateDecl* template_decl,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        std::string* error_out = nullptr);
    const TemplateDecl* cpp_template_decl_for_default_arguments(
        const Decl* decl) const;
    QualType lookup_cpp_current_record_nested_type(
        const std::string& component_name) const;
    const RecordSemanticState::NestedTemplate*
    lookup_cpp_current_record_nested_type_template(
        const std::string& component_name,
        QualType* owner_lookup_type_out = nullptr) const;
    QualType prepare_cpp_qualified_type_owner(
        QualType owner_type,
        bool is_current_instantiation = false);
    const Decl* lookup_cpp_unqualified_type_template_decl(
        const std::string& component_name,
        const std::shared_ptr<Scope>& start_scope,
        bool allow_enclosing_lookup) const;
    std::optional<CppDependentOwnerAnalysis> analyze_cpp_qualified_type_owner(
        std::string_view qualifier_name,
        const std::vector<TemplateArgument>& qualifier_arguments,
        bool qualifier_has_template_argument_list,
        SrcLoc qualifier_loc);
    CppQualifiedOwnerChainResolution resolve_cpp_qualified_owner_chain(
        const std::vector<CppQualifiedNameComponent>& qualifiers,
        bool has_global_qualifier,
        SrcLoc start_loc,
        bool diagnose_dependent_names = true,
        std::optional<CppQualifiedOwnerSeed> initial_owner = std::nullopt);
    CppDependentOwnerAnalysis analyze_cpp_member_access_base(
        QualType base_type,
        bool is_arrow) const;
    bool starts_with_cpp_dependent_qualified_call_expression();
    std::string format_cpp_dependent_name_for_diagnostic(
        std::string_view terminal_name,
        std::string_view qualifier_name = {}) const;
    void diagnose_missing_cpp_template_keyword(std::string_view terminal_name,
                                               SrcLoc loc);
    void diagnose_missing_cpp_template_keyword(std::string_view qualifier_name,
                                               std::string_view terminal_name,
                                               SrcLoc loc);
    void diagnose_missing_cpp_typename_keyword(std::string_view qualifier_name,
                                               std::string_view terminal_name,
                                               SrcLoc loc);
    bool cpp_qualifier_is_current_instantiation(
        std::string_view qualifier_name,
        QualType qualifier_type) const;
    bool cpp_type_lookup_names_current_instantiation_member(
        const DeclContext* owner_context,
        QualType type,
        std::string_view name) const;
    CppCtorBaseInitializerTarget resolve_cpp_ctor_base_initializer_target(
        const RecordSemanticState& semantic_state,
        QualType owner_type,
        const CppCtorInitializer& initializer);

    std::vector<std::unique_ptr<Decl>> parse_struct_declaration(bool leading_virtual_specifier = false);

    std::unique_ptr<Decl> parse_enum_specifier();

    // === Shared C/C++ declaration and parser control ===
    bool isTokenDeclarationSpec(Token s);
    bool is_c23_constexpr_enabled() const;
    bool is_cxx_mode_active() const;
    LanguageLinkage current_decl_language_linkage() const;
    std::string make_cpp_unsupported_message(std::string_view feature) const;
    void fail_cpp_unsupported(std::string_view feature, SrcLoc loc);
    bool is_cpp_operator_function_name(std::string_view name) const;
    std::optional<std::string> try_parse_cpp_operator_function_id_name();
    bool is_cpp_member_only_operator_name(std::string_view name) const;
    void validate_cpp_operator_function_declaration(std::string_view name,
                                                    bool in_class_member_context,
                                                    bool is_static_member,
                                                    SrcLoc loc);
    bool is_cpp_scope_resolution_here();
    bool consume_cpp_scope_resolution();
    bool is_cpp_qualified_id_start();
    bool is_cpp_out_of_line_constructor_declaration_start();
    bool is_cpp_out_of_line_destructor_declaration_start();
    std::vector<std::unique_ptr<Decl>> parse_cpp_out_of_line_constructor_definition();
    std::vector<std::unique_ptr<Decl>> parse_cpp_out_of_line_destructor_definition();
    std::vector<std::unique_ptr<Decl>> parse_cpp_namespace_definition();
    std::vector<std::unique_ptr<Decl>> parse_cpp_using_alias_declaration();
    std::unique_ptr<Expr> try_parse_cpp_type_construction_expression();
    std::unique_ptr<Expr> parse_cpp_qualified_primary_expression();
    std::unique_ptr<Expr> parse_cpp_named_cast_expression();
    std::unique_ptr<Expr> parse_cpp_typeid_expression();
    std::unique_ptr<Expr> parse_cpp_throw_expression();
    std::unique_ptr<Expr> parse_cpp_new_expression(bool is_global_allocation);
    std::unique_ptr<Expr> parse_cpp_delete_expression(bool is_global_delete);
    std::unique_ptr<Expr> parse_cpp_postfix_pseudo_destructor_expression(
        std::unique_ptr<Expr> base,
        bool is_arrow,
        SrcLoc operator_loc);
    CppCatchClause parse_cpp_catch_clause();
    std::unique_ptr<Stmt> parse_cpp_try_statement(
        std::shared_ptr<Scope> try_scope = nullptr,
        bool allow_ctor_mem_initializer_after_try = false);
    void skip_balanced_token_sequence_tokens(TokenType open_tok,
                                             TokenType close_tok,
                                             const std::string& missing_close_diag);
    void skip_cpp_constructor_mem_initializer_list_tokens();
    void skip_cpp_function_try_block_tail_tokens();
    void skip_cpp_function_try_block_tokens(
        bool allow_ctor_mem_initializer_after_try);
    void parse_cpp_optional_noexcept_spec(
        FunctionType& function_type,
        const Collect::CppThisContext* cpp_this_context = nullptr,
        QualType record_lookup_type = QualType());
    CppExplicitSpecifier parse_cpp_optional_explicit_specifier();
    std::shared_ptr<Scope> resolve_named_namespace_scope(
        const DeclContext* start_context,
        const std::string& namespace_name,
        bool allow_enclosing_lookup) const;
    std::string make_cpp_future_work_message(std::string_view feature,
                                             std::string_view future_work_item) const;
    void fail_cpp_future_work(std::string_view feature,
                              std::string_view future_work_item,
                              SrcLoc loc);

    // === Tentative parsing and syntax probes ===
    // These APIs may classify syntax and rewind parser state, but they must
    // not mutate the long-lived parser/collect state on success or failure.
    TPResult try_parse_type_name();
    TPResult try_parse_declarator();
    TPResult try_parse_simple_declaration();
    TPResult try_parse_expression_statement_start();
    TPResult try_parse_cpp_qualified_id();
    TPResult try_parse_cpp_qualified_declarator();
    CxxStmtDisambiguation classify_cxx_stmt_disambiguation();
    tentative_syntax_probe::Config syntax_probe_config() const;
    tentative_syntax_probe::Result probe_type_name_syntax();
    tentative_syntax_probe::Result probe_declarator_syntax();
    tentative_syntax_probe::Result
    probe_cxx_constrained_placeholder_type_specifier_syntax();
    tentative_syntax_probe::Result probe_cpp_qualified_id_start_syntax();
    tentative_syntax_probe::Result probe_cpp_qualified_declarator_syntax();
    tentative_syntax_probe::Result probe_cpp_template_name_argument_prefix_syntax();
    tentative_syntax_probe::TemplateArgumentListScopeFollow
    classify_template_argument_list_scope_follow_syntax();

    // Attribute parsing
    std::vector<ParsedAttribute> try_parse_attributes();
    std::vector<ParsedAttribute> parse_gnu_attribute_list();
    std::vector<ParsedAttribute> parse_c23_attribute_list();
    ParsedAttribute parse_single_attribute();
    void skip_balanced_parens();
    void skip_balanced_brackets();
    std::vector<const Expr*> collect_decl_default_arguments(const FuncDecl* decl) const;
    void register_function_default_arguments(const std::shared_ptr<Symbol>& sym,
                                             const FuncDecl* decl,
                                             SrcLoc fallback_loc);
    std::string resolve_local_label_name(const std::string& name) const;
    void declare_local_labels(const std::vector<std::string>& labels, SrcLoc loc);

public:
    LangOptions lang_opts;
    std::shared_ptr<DiagnosticEngine> diag_engine;
    std::unique_ptr<Collect> collect_;

    explicit Parser(const std::vector<Token>& tokens, std::shared_ptr<SourceManager> src_mgnt)
    : tok_mgnt(tokens, src_mgnt),
    ast_ctx(std::make_shared<ASTContext>()),
    type_ctx(ast_ctx->type_ctx),
    diag_engine(std::make_shared<DiagnosticEngine>(src_mgnt)),
    collect_(std::make_unique<Collect>(ast_ctx, src_mgnt, diag_engine, lang_opts)) {
        tok_mgnt.diag_engine = diag_engine;
    }

    Parser(const std::vector<Token>& tokens, std::shared_ptr<SourceManager> src_mgnt,
           std::shared_ptr<TargetInfo> ti)
    : tok_mgnt(tokens, src_mgnt),
    ast_ctx(std::make_shared<ASTContext>(std::move(ti))),
    type_ctx(ast_ctx->type_ctx),
    diag_engine(std::make_shared<DiagnosticEngine>(src_mgnt)),
    collect_(std::make_unique<Collect>(ast_ctx, src_mgnt, diag_engine, lang_opts)) {
        tok_mgnt.diag_engine = diag_engine;
    }

    std::unique_ptr<Decl> parse();
    std::optional<std::string>
    try_parse_cpp_overloadable_operator_function_id_name_after_operator_keyword();
    std::unique_ptr<Expr> parse_expression();
    // also const expression
    std::unique_ptr<Expr> parse_conditional_expression();
    std::unique_ptr<Expr> parse_binary_expression(int min_precedence = 0);
    void enter_template_argument_expression() {
        ++template_argument_expression_depth_;
    }
    void leave_template_argument_expression() {
        if (template_argument_expression_depth_ > 0) {
            --template_argument_expression_depth_;
        }
    }
    bool is_parsing_template_argument_expression() const {
        return template_argument_expression_depth_ > 0;
    }
    bool is_at_top_level_template_argument_expression() const {
        return template_argument_expression_depth_ > 0 &&
               template_argument_group_depth_ == 0;
    }
    void enter_template_argument_group() {
        ++template_argument_group_depth_;
    }
    void leave_template_argument_group() {
        if (template_argument_group_depth_ > 0) {
            --template_argument_group_depth_;
        }
    }
    void set_tentative_typename_context_dependent_lookup(bool enabled) {
        cxx_tentative_state_.typename_context_dependent_lookup = enabled;
    }
    bool tentative_typename_context_dependent_lookup() const {
        return cxx_tentative_state_.typename_context_dependent_lookup;
    }
    void set_tentative_template_id_vs_relational(bool enabled) {
        cxx_tentative_state_.template_id_vs_relational = enabled;
    }
    bool tentative_template_id_vs_relational() const {
        return cxx_tentative_state_.template_id_vs_relational;
    }
    void set_tentative_prefer_declaration(bool enabled) {
        cxx_tentative_state_.prefer_declaration = enabled;
    }
    bool tentative_prefer_declaration() const {
        return cxx_tentative_state_.prefer_declaration;
    }
    friend struct DeclarationParser;

private:
    std::vector<TentativeContextFrame> tentative_context_stack_;
    size_t next_tentative_context_id_ = 1;
    CxxTentativeDisambiguationState cxx_tentative_state_;
    LanguageLinkage current_language_linkage_ = LanguageLinkage::None;
    std::unordered_map<const DeclContext*, NamespaceDecl*>
        cxx_namespace_canonical_decl_cache_;
    std::unordered_map<const DeclContext*, NamespaceDecl*>
        cxx_namespace_latest_decl_cache_;
    uint32_t template_pattern_depth_ = 0;
    uint32_t template_parameter_depth_ = 0;
    uint32_t template_argument_expression_depth_ = 0;
    uint32_t template_argument_group_depth_ = 0;
    uint32_t template_head_requires_clause_depth_ = 0;
    uint32_t lambda_template_requires_clause_depth_ = 0;
    uint32_t cpp_explicit_specialization_parse_depth_ = 0;
    uint32_t cpp_template_declaration_subject_parse_depth_ = 0;
    struct ActiveAbbreviatedFunctionTemplateContext {
        TemplateParameterList* parameters = nullptr;
        uint32_t parameter_depth = 0;
    };
    ActiveAbbreviatedFunctionTemplateContext*
        active_abbreviated_function_template_context_ = nullptr;
    std::vector<std::vector<const TemplateParameterDecl*>>
        active_template_parameter_stack_;
    std::optional<PendingCppExplicitSpecializationInfo>
        pending_cpp_explicit_specialization_info_;
    struct PendingPrimaryVariableTemplatePattern {
        TemplateParameterList* parameters = nullptr;
        std::unique_ptr<Expr>* leading_requires_clause = nullptr;
        SrcLoc template_loc;
        bool member_template_declaration = false;
        bool consumed = false;
        std::string name;
        std::unique_ptr<VariableTemplateDecl> provisional_template;
    };
    PendingPrimaryVariableTemplatePattern*
        pending_primary_variable_template_pattern_ = nullptr;
    struct CppRecordParseFrame {
        CppRecordKind kind = CppRecordKind::Class;
        std::string name;
        const ObjectDecl* semantic_owner = nullptr;
        const ClassTemplateDecl* primary_class_template = nullptr;
        QualType current_instantiation_type = nullptr;
    };
    std::vector<CppRecordParseFrame> cxx_record_parse_stack_;
    struct ActiveCppQualifiedDeclaratorContext {
        const ObjectDecl* owner_record_decl = nullptr;
        QualType owner_type = nullptr;
    };
    ActiveCppQualifiedDeclaratorContext active_cpp_qualified_declarator_context_;
    // Owns temporary semantic decls created during C++ class parsing before
    // final semantic record decl emission in parse_declaration.
    std::vector<std::unique_ptr<Decl>> cpp_transient_semantic_decls_;
    // Friend function templates first declared inside classes are namespace
    // members, but not ordinary lookup candidates until a matching namespace
    // declaration appears. Keep them out of normal lookup while still allowing
    // later redeclarations to inherit friendship.
    std::vector<const FunctionTemplateDecl*> hidden_friend_function_templates_;
    struct HiddenFriendClassTemplate {
        const ClassTemplateDecl* decl = nullptr;
        std::shared_ptr<Scope> namespace_scope;
    };
    std::vector<HiddenFriendClassTemplate> hidden_friend_class_templates_;

    bool is_parsing_cpp_explicit_specialization() const {
        return cpp_explicit_specialization_parse_depth_ > 0;
    }
};
bool is_integer_literal(TokenType tok);

// technically parses declarators
struct DeclarationParser {
    // We track the tally of keywords found in a single declaration-specifier list
    std::string name; // name of identifier
    StorageClass str_class;
    TokenMgnt * mgnt;
    Parser * pars;
    SrcLoc begin_loc;
    std::shared_ptr<CType> first_half; // declaration_specifiers

    std::shared_ptr<CType> result_type;
    bool is_inline = false;
    bool is_thread_local = false;
    bool is_block_byref = false;
    bool is_constexpr = false;
    bool is_consteval = false;
    bool is_friend = false;
    CppExplicitSpecifier explicit_specifier;
    std::unique_ptr<Expr> trailing_requires_clause = nullptr;
    uint8_t qualifiers = QUAL_NONE; // outermost type qualifiers (for the variable itself)
    std::optional<std::string> asm_label;
    uint8_t base_qualifiers = QUAL_NONE; // qualifiers from declaration specifiers (preserved across declarators)
    // todo: can we combine this potentially?
    std::unique_ptr<Decl> cpp_record_obj;
    std::unique_ptr<Decl> struct_obj;
    std::unique_ptr<Decl> enum_obj;
    std::vector<std::unique_ptr<DeclarationParser>> func_args;
    bool captured_func_args = false;
    uint8_t trailing_function_cv_qualifiers = QUAL_NONE;
    // 0 = none, 1 = lvalue (&), 2 = rvalue (&&)
    uint8_t trailing_function_ref_qualifier = 0;
    bool allow_typeless_conversion_function = false;
    bool is_conversion_function = false;
    QualType conversion_target_type = nullptr;
    std::vector<TemplateArgument> explicit_specialization_arguments;
    bool has_explicit_specialization_argument_list = false;
    std::vector<std::string> kr_param_names;  // K&R identifier-list parameter names
    std::shared_ptr<Symbol> preparsed_sym = nullptr;
    std::unique_ptr<Expr> default_argument = nullptr;
    bool is_kr_style = false;
    bool is_parameter_pack = false;
    bool is_mutable = false;
    SrcLoc loc;
    bool arrays_are_pointers; // If this is true, then arrays are parsed as pointer types
    bool in_function_parameter; // Parsing a parameter declarator (enables C array-parameter forms)
    // C++ new-expression parsing mode for unparenthesized new-type-id:
    // stop declarator parsing before function-style "(...)" so outer parser
    // can consume it as new-initializer.
    bool parse_new_type_id_context;
    std::shared_ptr<CType> typedef_resolved_type = nullptr; // set when an identifier type-name is used as type specifier
    uint8_t typedef_resolved_qualifiers = QUAL_NONE;
    std::shared_ptr<CppTypeConstraint> pending_cxx_auto_type_constraint = nullptr;
    struct TypeTally {
        int void_count = 0, char_count = 0, short_count = 0, int_count = 0,
            long_count = 0, float_count = 0, double_count = 0, bool_count = 0,
            wchar_count = 0, char16_count = 0, char32_count = 0,
            signed_count = 0, unsigned_count = 0, complex_count = 0, int128_count = 0,
            float16_count = 0;
        int static_count = 0, extern_count = 0, auto_count = 0, register_count = 0, typedef_count = 0;
        int mutable_count = 0;
        int constexpr_count = 0;
        int consteval_count = 0;
        int inline_count = 0;
        int thread_local_count = 0;
        int block_byref_count = 0;
        int auto_type_count = 0;
        int cxx_auto_count = 0;
        int decltype_auto_count = 0;
    };
   // DeclarationParser(TypeTally tally): tally(tally) {};
    DeclarationParser(Parser * pars): str_class(StorageClass::NONE), result_type(nullptr)
    , arrays_are_pointers(false), in_function_parameter(false),
      parse_new_type_id_context(false) {
        this->pars = pars;
        mgnt = &pars->tok_mgnt;
    };
    TypeTally tally;
    void error(std::string err) {
        SrcLoc loc;
        Token curr_tok = mgnt->current_token();
        if (curr_tok.type != TokenType::Eof) {
            loc = curr_tok.loc;
        }
        pars->diag_engine->report_error(err, loc);
        throw ParseError(err, loc);
    }
    void error_custloc(std::string err, SrcLoc loc) {
        pars->diag_engine->report_error(err, loc);
        throw ParseError(err, loc);
    }
    static std::shared_ptr<CType> resolveBuiltinType(const TypeTally& tally, TypeContext& ctx) {
        // Handle _Complex types, including GNU integer complex extension.
        if (tally.complex_count) {
            TypeTally base = tally;
            base.complex_count = 0;
            auto base_type = resolveBuiltinType(base, ctx);
            auto builtin = dyn_cast_shared<BuiltinType>(base_type);
            if (!builtin) return nullptr; // validateTally should have caught invalid combos
            return ctx.get_complex(builtin->builtin_kind);
        }

        if (tally.void_count == 1) return ctx.get_builtin(BuiltinTypes::Void);
        if (tally.bool_count == 1) return ctx.get_builtin(BuiltinTypes::Bool);
        if (tally.wchar_count == 1) return ctx.get_builtin(BuiltinTypes::WChar);
        if (tally.char16_count == 1) return ctx.get_builtin(BuiltinTypes::Char16);
        if (tally.char32_count == 1) return ctx.get_builtin(BuiltinTypes::Char32);
        // Handle Character Types
        if (tally.char_count == 1) {
            if (tally.unsigned_count == 1) return ctx.get_builtin(BuiltinTypes::UChar);
            if (tally.signed_count == 1) return ctx.get_builtin(BuiltinTypes::SChar);
            return ctx.get_builtin(BuiltinTypes::Char);
        }

        // Handle 128-bit integer types
        if (tally.int128_count == 1) {
            if (tally.unsigned_count) return ctx.get_builtin(BuiltinTypes::UInt128);
            return ctx.get_builtin(BuiltinTypes::Int128);
        }

        // Handle Integer Types (The most complex part)
        if (tally.long_count == 2) { // "long long"
            if (tally.unsigned_count) return ctx.get_builtin(BuiltinTypes::ULongLong);
            return ctx.get_builtin(BuiltinTypes::LongLong);
        }

        if (tally.long_count == 1) { // "long"
            if (tally.double_count == 1) return ctx.get_builtin(BuiltinTypes::LongDouble);
            if (tally.unsigned_count)    return ctx.get_builtin(BuiltinTypes::ULong);
            return ctx.get_builtin(BuiltinTypes::Long);
        }

        if (tally.short_count == 1) {
            if (tally.unsigned_count) return ctx.get_builtin(BuiltinTypes::UShort);
            return ctx.get_builtin(BuiltinTypes::Short);
        }

        if (tally.float16_count == 1) return ctx.get_builtin(BuiltinTypes::Float16);
        if (tally.float_count == 1)  return ctx.get_builtin(BuiltinTypes::Float);
        if (tally.double_count == 1) return ctx.get_builtin(BuiltinTypes::Double);

        // Default to Int if "int", "signed", "unsigned", or nothing is provided
        if (tally.int_count || tally.signed_count || tally.unsigned_count) {
            if (tally.unsigned_count) return ctx.get_builtin(BuiltinTypes::UInt);
            return ctx.get_builtin(BuiltinTypes::Int);
        }
        // if no type specifiers, default to int. This is not supported post 1999 C
        if (tally.static_count || tally.extern_count || tally.auto_count) {
             // return ctx.get_builtin(BuiltinTypes::Int);
        }
        return nullptr;
    }
    void validateTally(const TypeTally& tally) {
        // C11 Clause 6.7.2 Constraints:
        if (tally.signed_count && tally.unsigned_count)
            error_custloc("Cannot have both signed and unsigned", begin_loc);

        // __int128 constraints
        if (tally.int128_count > 1)
            error_custloc("duplicate '__int128' specifier", begin_loc);
        if (tally.int128_count && (tally.char_count || tally.short_count || tally.long_count ||
            tally.int_count || tally.float_count || tally.double_count || tally.void_count ||
            tally.bool_count || tally.wchar_count || tally.char16_count ||
            tally.char32_count))
            error_custloc("'__int128' cannot be combined with other type specifiers", begin_loc);

        if (tally.wchar_count > 1) {
            error_custloc("duplicate 'wchar_t' specifier", begin_loc);
        }
        if (tally.wchar_count &&
            (tally.void_count || tally.char_count || tally.short_count || tally.int_count ||
             tally.long_count || tally.float_count || tally.double_count || tally.bool_count ||
             tally.signed_count || tally.unsigned_count || tally.int128_count ||
             tally.float16_count || tally.complex_count ||
             tally.char16_count || tally.char32_count)) {
            error_custloc("'wchar_t' cannot be combined with other type specifiers", begin_loc);
        }
        if (tally.char16_count > 1) {
            error_custloc("duplicate 'char16_t' specifier", begin_loc);
        }
        if (tally.char16_count &&
            (tally.void_count || tally.char_count || tally.short_count || tally.int_count ||
             tally.long_count || tally.float_count || tally.double_count || tally.bool_count ||
             tally.wchar_count || tally.signed_count || tally.unsigned_count ||
             tally.int128_count || tally.float16_count || tally.complex_count ||
             tally.char32_count)) {
            error_custloc("'char16_t' cannot be combined with other type specifiers", begin_loc);
        }
        if (tally.char32_count > 1) {
            error_custloc("duplicate 'char32_t' specifier", begin_loc);
        }
        if (tally.char32_count &&
            (tally.void_count || tally.char_count || tally.short_count || tally.int_count ||
             tally.long_count || tally.float_count || tally.double_count || tally.bool_count ||
             tally.wchar_count || tally.signed_count || tally.unsigned_count ||
             tally.int128_count || tally.float16_count || tally.complex_count ||
             tally.char16_count)) {
            error_custloc("'char32_t' cannot be combined with other type specifiers", begin_loc);
        }

        // __auto_type constraints
        if (tally.auto_type_count > 1)
            error_custloc("duplicate '__auto_type' specifier", begin_loc);
        if (tally.auto_type_count && (tally.void_count || tally.char_count || tally.short_count ||
            tally.int_count || tally.long_count || tally.float_count || tally.double_count ||
            tally.bool_count || tally.wchar_count || tally.char16_count ||
            tally.char32_count || tally.signed_count || tally.unsigned_count ||
            tally.int128_count))
            error_custloc("'__auto_type' cannot be combined with other type specifiers", begin_loc);
        if (tally.auto_type_count && tally.typedef_count)
            error_custloc("'__auto_type' cannot be combined with 'typedef'", begin_loc);

        // C++ auto placeholder constraints
        if (tally.cxx_auto_count > 1)
            error_custloc("duplicate 'auto' specifier", begin_loc);
        if (tally.cxx_auto_count && tally.auto_type_count)
            error_custloc("'auto' cannot be combined with '__auto_type'", begin_loc);
        if (tally.cxx_auto_count && (tally.void_count || tally.char_count || tally.short_count ||
            tally.int_count || tally.long_count || tally.float_count || tally.double_count ||
            tally.bool_count || tally.wchar_count || tally.char16_count ||
            tally.char32_count || tally.signed_count || tally.unsigned_count ||
            tally.int128_count || tally.float16_count || tally.complex_count))
            error_custloc("'auto' cannot be combined with other type specifiers", begin_loc);
        if (tally.cxx_auto_count && tally.typedef_count)
            error_custloc("'auto' cannot be combined with 'typedef'", begin_loc);

        // C++ decltype(auto) placeholder constraints
        if (tally.decltype_auto_count > 1)
            error_custloc("duplicate 'decltype(auto)' specifier", begin_loc);
        if (tally.decltype_auto_count &&
            (tally.auto_type_count || tally.cxx_auto_count))
            error_custloc("'decltype(auto)' cannot be combined with 'auto' or '__auto_type'", begin_loc);
        if (tally.decltype_auto_count &&
            (tally.void_count || tally.char_count || tally.short_count ||
             tally.int_count || tally.long_count || tally.float_count ||
             tally.double_count || tally.bool_count || tally.wchar_count ||
             tally.char16_count || tally.char32_count || tally.signed_count ||
             tally.unsigned_count || tally.int128_count || tally.float16_count ||
             tally.complex_count))
            error_custloc("'decltype(auto)' cannot be combined with other type specifiers", begin_loc);
        if (tally.decltype_auto_count && tally.typedef_count)
            error_custloc("'decltype(auto)' cannot be combined with 'typedef'", begin_loc);

        if (tally.long_count > 2)
            error_custloc("Too many 'long' specifiers", begin_loc);
        if (tally.int_count > 1 || tally.signed_count > 1 || tally.unsigned_count > 1) {
            error_custloc("Too many 'int', 'signed', or 'unsigned' specifiers", begin_loc);
        }
        if (tally.static_count + tally.extern_count + tally.auto_count + tally.register_count + tally.typedef_count > 1) {
            if (tally.typedef_count) {
                error_custloc("'typedef' cannot be combined with other storage class specifiers", begin_loc);
            } else {
                error_custloc("Too many storage class specifiers", begin_loc);
            }
        }
        if (tally.mutable_count > 1) {
            error_custloc("duplicate 'mutable' specifier", begin_loc);
        }
        // _Thread_local can only combine with static or extern
        if (tally.thread_local_count) {
            if (tally.auto_count || tally.register_count || tally.typedef_count) {
                error_custloc("'_Thread_local' cannot be combined with 'auto', 'register', or 'typedef'", begin_loc);
            }
        }
        if (tally.block_byref_count > 1) {
            error_custloc("duplicate '__block' specifier", begin_loc);
        }
        if (tally.block_byref_count &&
            (tally.static_count || tally.extern_count || tally.register_count ||
             tally.typedef_count || tally.thread_local_count || tally.auto_count)) {
            error_custloc(
                "'__block' cannot be combined with storage-class specifiers",
                begin_loc);
        }
        if (tally.typedef_count > 1) {
            error_custloc("duplicate 'typedef' specifier", begin_loc);
        }
        if (tally.constexpr_count > 1) {
            error_custloc("duplicate 'constexpr' specifier", begin_loc);
        }
        if (tally.consteval_count > 1) {
            error_custloc("duplicate 'consteval' specifier", begin_loc);
        }
        if (tally.constexpr_count && tally.consteval_count) {
            error_custloc("'constexpr' cannot be combined with 'consteval'", begin_loc);
        }
        if (tally.constexpr_count && tally.typedef_count) {
            error_custloc("'constexpr' cannot be combined with 'typedef'", begin_loc);
        }
        if (tally.consteval_count && tally.typedef_count) {
            error_custloc("'consteval' cannot be combined with 'typedef'", begin_loc);
        }
        // Floating-point types cannot be combined with signed/unsigned
        if ((tally.float_count || tally.double_count) && (tally.signed_count || tally.unsigned_count)) {
            if (!(tally.long_count == 1 && tally.double_count == 1)) // long double is ok
                error_custloc("Cannot combine 'signed'/'unsigned' with floating-point type", begin_loc);
        }
        // float/double cannot be combined with each other or with integer type specifiers
        if (tally.float_count > 1 || tally.double_count > 1)
            error_custloc("duplicate type specifier", begin_loc);
        if (tally.float_count && tally.double_count)
            error_custloc("Cannot combine 'float' and 'double'", begin_loc);
        if ((tally.float_count || tally.double_count) &&
            (tally.char_count || tally.short_count || tally.int_count || tally.void_count ||
             tally.bool_count || tally.wchar_count || tally.char16_count ||
             tally.char32_count)) {
            error_custloc("Cannot combine floating-point type with other type specifiers", begin_loc);
        }
        // double can only combine with long (long double)
        if (tally.double_count && tally.long_count > 1)
            error_custloc("Cannot have 'long long double'", begin_loc);
        if (tally.float_count && tally.long_count)
            error_custloc("Cannot combine 'long' with 'float'", begin_loc);

        // _Complex constraints: GNU extension allows integer complex types too.
        if (tally.complex_count) {
            if (tally.complex_count > 1)
                error_custloc("duplicate '_Complex' specifier", begin_loc);
            if (tally.void_count || tally.bool_count) {
                error_custloc("'_Complex' cannot be combined with 'void' or '_Bool'", begin_loc);
            }
            bool has_arithmetic_specifier =
                (tally.char_count || tally.short_count || tally.int_count ||
                 tally.long_count || tally.float_count || tally.double_count ||
                 tally.float16_count || tally.int128_count ||
                 tally.signed_count || tally.unsigned_count);
            if (!has_arithmetic_specifier) {
                error_custloc("'_Complex' requires an arithmetic type specifier", begin_loc);
            }
        }
    }
    static StorageClass resolveStorageClass(const TypeTally& tally) {
        if (tally.typedef_count) return StorageClass::TYPEDEF;
        if (tally.static_count) return StorageClass::STATIC;
        if (tally.extern_count) return StorageClass::EXTERN;
        if (tally.auto_count) return StorageClass::AUTO;
        if (tally.register_count) return StorageClass::REGISTER;
        return StorageClass::NONE;
    }
    std::shared_ptr<CType> apply_declspec_type_attributes(std::shared_ptr<CType> type) {
        auto result = type;
        auto normalize_mode_name = [](std::string mode) {
            if (mode.size() >= 4 && mode.rfind("__", 0) == 0 &&
                mode.substr(mode.size() - 2) == "__") {
                mode = mode.substr(2, mode.size() - 4);
            }
            for (char& ch : mode) {
                ch = static_cast<char>(std::toupper(static_cast<unsigned char>(ch)));
            }
            return mode;
        };
        for (const auto& attr : leading_attrs) {
            std::string canon = attr.canonical_name();

            if (canon == "mode") {
                if (attr.args.empty()) {
                    error("mode attribute requires a mode name");
                }
                if (!result || !result->isInteger()) {
                    error("mode attribute currently requires an integer base type");
                }
                std::string mode_name;
                if (attr.args[0].kind == AttributeArg::Kind::IDENTIFIER ||
                    attr.args[0].kind == AttributeArg::Kind::STRING ||
                    attr.args[0].kind == AttributeArg::Kind::KEY_VALUE) {
                    mode_name = normalize_mode_name(attr.args[0].str_value);
                } else {
                    error("mode attribute requires an identifier argument");
                }

                auto pick_int_mode = [&](bool is_unsigned) -> std::shared_ptr<CType> {
                    if (mode_name == "QI" || mode_name == "BYTE") {
                        return pars->type_ctx->get_builtin(
                            is_unsigned ? BuiltinTypes::UChar : BuiltinTypes::SChar);
                    }
                    if (mode_name == "HI") {
                        return pars->type_ctx->get_builtin(is_unsigned ? BuiltinTypes::UShort : BuiltinTypes::Short);
                    }
                    if (mode_name == "SI") {
                        return pars->type_ctx->get_builtin(is_unsigned ? BuiltinTypes::UInt : BuiltinTypes::Int);
                    }
                    if (mode_name == "WORD") {
                        return pars->type_ctx->get_builtin(is_unsigned ? BuiltinTypes::ULong : BuiltinTypes::Long);
                    }
                    if (mode_name == "DI") {
                        return pars->type_ctx->get_builtin(is_unsigned ? BuiltinTypes::ULongLong : BuiltinTypes::LongLong);
                    }
                    if (mode_name == "TI") {
                        return pars->type_ctx->get_builtin(is_unsigned ? BuiltinTypes::UInt128 : BuiltinTypes::Int128);
                    }
                    return nullptr;
                };

                auto replacement = pick_int_mode(result->isUnsigned());
                if (!replacement) {
                    error("unsupported mode attribute '" + mode_name + "'");
                }
                result = replacement;
                continue;
            }

            if (canon == "aligned") {
                auto obj = result ? dyn_cast_shared<ObjectType>(result) : nullptr;
                if (obj && !attr.args.empty() &&
                    attr.args[0].kind == AttributeArg::Kind::INTEGER &&
                    attr.args[0].int_value > 0) {
                    size_t requested = static_cast<size_t>(attr.args[0].int_value);
                    if (requested > obj->requested_alignment) {
                        obj->requested_alignment = requested;
                    }
                }
                continue;
            }

            if (canon != "vector_size" || attr.args.empty() ||
                attr.args[0].kind != AttributeArg::Kind::INTEGER) {
                if (canon == "transparent_union") {
                    auto obj = result ? dyn_cast_shared<ObjectType>(result) : nullptr;
                    if (obj && obj->is_union) {
                        obj->is_transparent_union = true;
                    }
                }
                continue;
            }
            if (result && canonical_type_kind(result) == TypeKind::Vector) {
                continue;
            }
            if (!result || !result->isArithmetic() || result->isVoid()) {
                error("vector_size attribute requires an integer or floating-point base type");
            }
            size_t vec_bytes = static_cast<size_t>(attr.args[0].int_value);
            if (vec_bytes == 0 || (vec_bytes & (vec_bytes - 1)) != 0) {
                error("vector_size must be a power of 2");
            }
            int64_t elem_bytes = result->getWidthBytes();
            if (elem_bytes <= 0 || vec_bytes % static_cast<size_t>(elem_bytes) != 0) {
                error("vector_size must be a multiple of the base type size");
            }
            result = std::make_shared<VectorType>(QualType(result), vec_bytes);
        }
        return result;
    }
    // handles specifiers
    // todo: fail gracefully
    std::vector<ParsedAttribute> leading_attrs; // attributes parsed during declaration specifiers
    std::shared_ptr<CType> parse_declaration(bool run_second_half = true);

    // get ready to parse a new declarator
    void reset_declarator_parsing_state();

    // Handles pointers *, block pointers ^, and type qualifiers (const, volatile, restrict, _Atomic)
    std::shared_ptr<CType> parse_declarator(std::shared_ptr<CType> base);

    std::optional<QualType> parse_cpp_trailing_return_type();

    // int (*const [])(unsigned int, ...) turns to
    // Array(Pointer(Placeholder) -> Array(Pointer(Function)
    std::shared_ptr<CType> parse_direct_declarator(std::shared_ptr<CType> base);
    std::shared_ptr<CType> replace_placeholder(std::shared_ptr<CType> wrap,
                                                std::shared_ptr<CType> insert);

};
#endif //ABURI_PARSER_H
