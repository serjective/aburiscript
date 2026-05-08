#ifndef ABURI_COLLECT_H
#define ABURI_COLLECT_H

#include <cstdint>
#include <cctype>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "../ast/ast.h"
#include "../ast/ast_context.h"
#include "../builtin_registry.h"
#include "../constexpr/consteval_compat.h"
#include "../diagnostics.h"
#include "../lang_options.h"
#include "../source_mgnt.h"
#include "query_context.h"
#include "decl_context.h"

class CollectRecordBuilder;

// Bundles the boolean mode flags for collect_variable_declaration.
// Using a struct avoids long chains of positional booleans at call sites.
struct VariableDeclFlags {
    bool is_constexpr = false;
    bool is_inline = false;
    bool is_file_scope = false;
    bool is_cpp_static_data_member = false;
    bool allow_constexpr_redeclaration_without_initializer = false;
    bool is_thread_local = false;
    bool is_block_byref = false;
    bool is_copy_initialization = false;
    bool allow_abstract_object_type_instantiation = false;
    bool caller_tracks_symbol_definition = false;
};

// Parser-facing semantic action surface.
// This owns semantic lifecycle state and is the single AST node construction
// entrypoint for parser reductions.
class Collect {
public:
    using CppThisContext = ::CppThisContext;

    enum class ValueCategory {
        Unknown,
        LValue,
        XValue,
        PRValue
    };

    enum class ExprUseContext {
        RValue,
        Condition,
        CallCallee,
        CallArgument,
        ArraySubscriptBase,
        ArraySubscriptIndex,
        ConditionalOperand,
        InitScalar,
        InitAggregate,
        LValueRequired,
        Unevaluated,
        ExpressionStatement
    };

    enum class CppNamedCastKind : uint8_t {
        Static,
        Const,
        Reinterpret,
        Dynamic
    };

    struct ScopeEnterResult {
        std::shared_ptr<Scope> scope;
        bool created_new = false;
    };

    struct LookupResult {
        std::string name;
        std::vector<std::shared_ptr<Symbol>> candidates;
        std::shared_ptr<Symbol> selected = nullptr;
        bool ambiguous = false;
    };

    using CppRecordDeferredBodyCallback = std::function<void(
        const CppRecordDecl& record,
        const std::shared_ptr<ObjectType>& record_type,
        const RecordSemanticState& semantic_state)>;

    enum class ConversionSequenceKind {
        Identity,
        LValueToRValue,
        ArrayToPointer,
        FunctionToPointer,
        Numeric,
        Qualification,
        Pointer,
        UserDefined,
        Failed
    };

    enum class ConversionSequenceRank {
        ExactMatch = 0,
        Promotion = 1,
        Conversion = 2,
        NoMatch = 3
    };

    enum class ConversionSequenceDetailKind : uint8_t {
        None,
        ReferenceDirectBinding,
        ReferenceTemporaryBinding,
        ReferenceRefQualifierMismatch,
        NullPointerConstant,
        MemberPointer,
        LambdaFunctionPointer,
        BracedInit
    };

    struct ImplicitConversionSequence {
        ConversionSequenceKind kind = ConversionSequenceKind::Identity;
        ConversionSequenceRank rank = ConversionSequenceRank::ExactMatch;
        ConversionSequenceDetailKind detail_kind =
            ConversionSequenceDetailKind::None;
        QualType from = nullptr;
        QualType to = nullptr;
        bool viable = true;
        // Optional tie-break subrank for ExactMatch sequences.
        // -1 means "use default ordering by kind".
        int exact_subrank = -1;
        std::string note;
    };

    enum class MemberPointerConversionIssue : uint8_t {
        None,
        NotMemberPointerType,
        MemberTypeMismatch,
        QualificationDrops,
        UnrelatedClass,
        AmbiguousBase,
        VirtualBase,
        InaccessibleBase
    };

    struct MemberPointerConversionResult {
        bool viable = false;
        int64_t owner_adjustment = 0;
        MemberPointerConversionIssue issue = MemberPointerConversionIssue::None;
    };

    struct ArrayBoundResult {
        std::optional<size_t> constant_size;
        std::shared_ptr<Expr> variable_size_expr = nullptr;
    };

    // === Lifecycle and configuration ===

    Collect(std::shared_ptr<ASTContext> ast_ctx,
            std::shared_ptr<SourceManager> sm,
            std::shared_ptr<DiagnosticEngine> diag_engine,
            LangOptions lang_opts);
    ~Collect();

    void set_lang_options(LangOptions lang_opts) ;

    // === Speculation and session isolation ===

    void collect_begin_session_isolation() ;

    void collect_commit_session_isolation() ;

    void collect_rollback_session_isolation() ;

    bool collect_is_session_isolating() const ;

    void collect_begin_speculative_parse() ;

    void collect_commit_speculative_parse() ;

    void collect_rollback_speculative_parse() ;

    bool collect_is_speculative_parsing() const ;

    void collect_start_translation_unit() ;

    std::unique_ptr<TranslationUnit> collect_finish_translation_unit(std::vector<std::unique_ptr<Decl>> decls,
                                                                     SrcLoc loc) ;

    // === Function definition management ===

    void collect_start_function_definition(const std::string& name,
                                           QualType function_type,
                                           CppThisContext cpp_this_context) ;

    void collect_finish_function_definition(const std::shared_ptr<Scope>& function_scope) ;

    void collect_abort_function_definition() ;

    // === Scope management ===

    std::shared_ptr<Scope> collect_current_scope() const ;

    std::shared_ptr<DeclContext> get_translation_unit_decl_context() const ;

    std::shared_ptr<DeclContext> get_current_decl_context() const ;

    void collect_register_namespace_binding(
        const std::shared_ptr<DeclContext>& owner_context,
        NamespaceBindingEntry binding);

    void collect_register_namespace_alias(
        const std::shared_ptr<DeclContext>& owner_context,
        NamespaceBindingEntry alias);

    void collect_register_namespace_nomination(
        const std::shared_ptr<DeclContext>& owner_context,
        NamespaceNominationRecord nomination);

    void collect_set_namespace_inline_metadata(
        const std::shared_ptr<DeclContext>& namespace_context,
        bool is_inline,
        DeclContext* enclosing_namespace);

    CppThisContext collect_current_cpp_this_context() const ;
    QualType collect_current_cpp_record_lookup_type() const ;
    void collect_set_current_cpp_record_lookup_type(QualType record_type) ;

    bool with_function_definition_state(
        const FuncDecl* function_decl,
        const std::function<bool()>& action) ;

    bool resolve_dependent_expr_after_substitution(
        std::unique_ptr<Expr>& expr,
        QualType implicit_this_type,
        std::string* error_out) ;

    void set_current_decl_context(std::shared_ptr<DeclContext> decl_context) ;

    void collect_set_current_scope(std::shared_ptr<Scope> scope) ;

    bool collect_is_file_scope() const ;

    ScopeEnterResult collect_enter_scope(std::shared_ptr<Scope> current_scope,
                                         std::shared_ptr<Scope> use_scope = nullptr) const ;

    ScopeEnterResult collect_enter_scope(ScopeFlags scope_flags,
                                         std::shared_ptr<Scope> use_scope = nullptr) ;

    ScopeEnterResult collect_enter_scope(std::shared_ptr<Scope> use_scope = nullptr) ;

    std::shared_ptr<Scope> collect_leave_scope(std::shared_ptr<Scope> current_scope) const ;

    std::shared_ptr<Scope> collect_leave_scope() ;

    // === Symbol lookup ===

    std::shared_ptr<Symbol> collect_lookup_typedef_symbol(const std::string& name,
                                                          bool look_parents = true) const ;

    QualType collect_lookup_type_name(const std::string& name,
                                      bool look_parents = true,
                                      bool include_tag_types = false) const ;

    std::shared_ptr<Symbol> collect_lookup_variable_symbol(const std::string& name,
                                                           bool look_parents = true) const ;

    TagDecl* collect_lookup_tag_decl(const std::string& tag,
                                     bool look_parents = true) const ;

    std::shared_ptr<CType> collect_lookup_tag_type(const std::string& tag,
                                                   bool look_parents = true) const ;

    std::unique_ptr<Decl> collect_build_cpp_record_semantic_decl(
        const CppRecordDecl& record,
        std::optional<std::string> semantic_tag_name = std::nullopt,
        std::vector<std::unique_ptr<Decl>>* transient_decls_out = nullptr,
        CppRecordDeferredBodyCallback deferred_body_callback = {}) ;

    ObjectDecl* collect_instantiate_class_template_specialization(
        const ClassTemplateDecl* class_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    // === Type operations ===

    QualType collect_try_realize_deferred_semantic_type(
        QualType type) {
        return try_realize_deferred_semantic_type(type);
    }

    QualType collect_finalize_deferred_semantic_type(
        QualType type,
        SrcLoc loc = SrcLoc()) {
        return finalize_deferred_semantic_type(type, loc);
    }

    std::unique_ptr<Expr> collect_process_initializer_for_type(
        std::unique_ptr<Expr> init,
        QualType declared_type,
        SrcLoc loc) {
        return process_initializer_for_type(std::move(init), declared_type, loc);
    }
    void collect_resolve_auto_variable_type_from_expr(
        QualType& declared_type,
        const Expr* init_expr,
        const std::shared_ptr<Symbol>& sym,
        const std::string& name,
        SrcLoc loc) {
        resolve_auto_variable_type_from_expr(
            declared_type,
            init_expr,
            sym,
            name,
            loc);
    }

    QualType collect_lookup_record_nested_type(QualType owner_type,
                                               const std::string& name) const ;
    std::shared_ptr<Symbol> collect_lookup_record_enumerator(
        QualType owner_type,
        const std::string& name) const;
    std::shared_ptr<Symbol> collect_lookup_enum_enumerator(
        QualType owner_type,
        const std::string& name) const;

    const RecordSemanticState::NestedTemplate* collect_lookup_record_nested_template(
        QualType owner_type,
        const std::string& name) const ;

    QualType collect_lookup_record_nested_template_type(
        QualType owner_type,
        const std::string& name,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        bool* matched_template = nullptr) ;

    // === Tag and symbol registration ===

    void collect_add_tag_decl(const std::string& tag, TagDecl* decl) ;

    void collect_bind_symbol_in_current_scope(const std::string& name,
                                              std::shared_ptr<Symbol> sym) ;

    void collect_add_global_symbol(std::shared_ptr<Symbol> sym) ;

    // === Control flow (loop/switch) ===

    void collect_enter_loop() ;

    void collect_leave_loop() ;

    void collect_enter_switch() ;

    void collect_leave_switch() ;

    // === Label management ===

    void collect_register_label_definition(const std::string& label, SrcLoc loc = SrcLoc()) ;

    void collect_register_label_reference(const std::string& label, SrcLoc loc = SrcLoc()) ;

    // === Literal creation ===

    template <typename NodeT, typename... Args>
    std::unique_ptr<NodeT> collect_make(Args&&... args) const {
        return make_ast<NodeT>(*ast_ctx_, std::forward<Args>(args)...);
    }

    std::unique_ptr<Expr> collect_integer_literal(const std::string& value,
                                                  std::shared_ptr<CType> int_type,
                                                  SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_floating_literal(const std::string& value,
                                                   std::shared_ptr<CType> float_type,
                                                   bool is_imaginary,
                                                   SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_character_literal(const std::string& value,
                                                    int32_t int_value,
                                                    QualType char_type,
                                                    SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_string_literal(const std::string& value,
                                                 QualType array_type,
                                                 SrcLoc loc) const ;

    // === Expression collection ===

    std::unique_ptr<Expr> collect_cpp_this_expression(SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_unqualified_identifier_expression(const std::string& name,
                                                                    bool looks_like_call,
                                                                    bool might_be_template_id,
                                                                    SrcLoc loc) ;

    std::unique_ptr<Expr> collect_identifier_reference(const std::string& name,
                                                       std::shared_ptr<Symbol> sym,
                                                       SrcLoc loc) const ;
    std::unique_ptr<Expr> collect_unresolved_lookup_expression(
        std::string name,
        DependentLookupQualifier qualifier,
        bool requires_template_keyword,
        SrcLoc loc) const ;

    LookupResult collect_lookup_result(const std::string& name,
                                       std::shared_ptr<Symbol> selected) const ;

    std::unique_ptr<Expr> collect_identifier_reference(LookupResult lookup,
                                                       SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_error_expression(const std::string& message,
                                                   SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_statement_expression(std::unique_ptr<CompoundStmt> compound_stmt,
                                                       SrcLoc loc) const ;
    std::unique_ptr<Expr> collect_block_expression(
        BlockSemanticInfo semantic_info,
        QualType block_type,
        std::vector<std::unique_ptr<Decl>> parameters,
        std::unique_ptr<CompoundStmt> body,
        std::unordered_set<std::string> stmt_labels,
        QualType explicit_return_type,
        bool has_parameter_clause,
        bool has_explicit_return_type,
        SrcLoc loc) ;
    std::unique_ptr<Expr> collect_cpp_lambda_expression(
        LambdaClosureInfo closure_info,
        LambdaSemanticInfo semantic_info,
        QualType written_call_operator_type,
        TemplateParameterList call_operator_template_parameters,
        std::vector<std::unique_ptr<Decl>> parameters,
        std::unique_ptr<CompoundStmt> body,
        std::unordered_set<std::string> stmt_labels,
        QualType explicit_return_type,
        bool has_parameter_clause,
        bool is_mutable,
        bool has_noexcept,
        bool has_trailing_return,
        bool is_generic,
        SrcLoc loc) ;
    bool collect_finalize_block_expression(BlockExpr& block,
                                           std::string* error_out = nullptr) ;
    bool collect_finalize_cpp_lambda_expression(CppLambdaExpr& lambda,
                                                std::string* error_out = nullptr) ;

    std::unique_ptr<Expr> collect_compound_literal_expression(QualType type,
                                                              std::unique_ptr<Expr> init,
                                                              SrcLoc loc) ;

    std::unique_ptr<Expr> collect_label_address_expression(const std::string& label,
                                                           SrcLoc loc) ;

    std::unique_ptr<Expr> collect_va_arg_expression(std::unique_ptr<Expr> va_list_expr,
                                                    QualType arg_type,
                                                    SrcLoc loc) ;

    std::unique_ptr<Expr> collect_builtin_types_compatible_expression(QualType lhs,
                                                                      QualType rhs,
                                                                      SrcLoc loc) ;
    std::unique_ptr<Expr> collect_builtin_type_trait_expression(
        BuiltinKind kind,
        std::vector<QualType> type_args,
        SrcLoc loc) ;
    std::optional<bool> evaluate_builtin_type_trait(
        BuiltinKind kind,
        const std::vector<QualType>& type_args,
        SrcLoc loc)  ;
    std::unique_ptr<Expr> collect_concept_specialization_expression(
        const ConceptDecl* concept_decl,
        std::string concept_name,
        std::vector<TemplateArgument> arguments,
        SrcLoc loc) ;
    std::optional<bool> evaluate_concept_specialization(
        const ConceptDecl* concept_decl,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;
    std::unique_ptr<Expr> collect_requires_expression(
        std::vector<std::unique_ptr<ParamDecl>> parameters,
        std::vector<ConstraintRequirement> requirements,
        SrcLoc loc) ;
    std::optional<bool> evaluate_requires_expression(
        const RequiresExpr* requires_expr,
        SrcLoc loc) ;
    bool are_template_constraints_satisfied(
        const TemplateDecl* template_decl,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;
    bool are_template_constraints_satisfied_with_bindings(
        const TemplateDecl* template_decl,
        const TemplateArgumentBindings& bindings,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_builtin_choose_expression(std::unique_ptr<Expr> const_expr,
                                                            std::unique_ptr<Expr> true_expr,
                                                            std::unique_ptr<Expr> false_expr,
                                                            SrcLoc loc) const ;
    std::unique_ptr<Expr> collect_builtin_convertvector_expression(std::unique_ptr<Expr> vector_expr,
                                                                   QualType target_type,
                                                                   SrcLoc loc) ;

    std::unique_ptr<Expr> collect_offsetof_expression(QualType type_operand,
                                                      const std::string& member_name,
                                                      std::vector<OffsetOfComponent> designator_path,
                                                      SrcLoc loc) ;

    std::unique_ptr<InitListExpr> collect_initializer_list_expression(SrcLoc loc) const ;

    // === Statement collection ===

    std::unique_ptr<Stmt> collect_empty_statement(SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_expression_statement(std::unique_ptr<Expr> expr,
                                                       SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_error_statement(const std::string& message,
                                                  SrcLoc loc) const ;

    // === Declaration collection ===

    std::unique_ptr<Decl> collect_error_declaration(const std::string& message,
                                                    SrcLoc loc) const ;

    std::unique_ptr<Decl> collect_file_scope_asm_declaration(std::string asm_text,
                                                             SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_asm_statement(std::string asm_template,
                                                bool is_volatile,
                                                bool is_inline,
                                                bool is_goto,
                                                bool has_colon,
                                                std::vector<AsmOperand> outputs,
                                                std::vector<AsmOperand> inputs,
                                                std::vector<std::string> clobbers,
                                                std::vector<std::string> goto_labels,
                                                SrcLoc loc) ;

    std::unique_ptr<Expr> collect_value_expression(std::unique_ptr<Expr> expr) const ;

    std::unique_ptr<Expr> collect_apply_standard_conversions(std::unique_ptr<Expr> expr,
                                                             ExprUseContext context,
                                                             QualType target_type = QualType()) const ;

    std::unique_ptr<Expr> collect_condition_expression(std::unique_ptr<Expr> condition,
                                                       SrcLoc loc,
                                                       const std::string& stmt_name) const ;

    std::unique_ptr<Expr> collect_explicit_cast(std::unique_ptr<Expr> expr,
                                                QualType target_type,
                                                SrcLoc loc) ;

    std::unique_ptr<Expr> collect_cpp_named_cast(CppNamedCastKind cast_kind,
                                                 std::unique_ptr<Expr> expr,
                                                 QualType target_type,
                                                 SrcLoc loc) ;
    std::unique_ptr<Expr> collect_cpp_typeid_type(QualType type_operand,
                                                  SrcLoc loc) ;
    std::unique_ptr<Expr> collect_cpp_typeid_expression(std::unique_ptr<Expr> expr_operand,
                                                        SrcLoc loc) ;
    std::unique_ptr<Expr> collect_cpp_throw_expression(std::unique_ptr<Expr> thrown_expr,
                                                       SrcLoc loc) const ;
    std::unique_ptr<Expr> collect_cpp_new_expression(
        QualType allocated_type,
        std::vector<std::unique_ptr<Expr>> placement_args,
        std::unique_ptr<Expr> initializer,
        bool is_global_allocation,
        SrcLoc loc) ;
    std::unique_ptr<Expr> collect_cpp_delete_expression(
        std::unique_ptr<Expr> operand,
        bool is_array_form,
        bool is_global_delete,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_sizeof_type(QualType type, SrcLoc loc) ;

    std::unique_ptr<Expr> collect_sizeof_pack_expression(
        std::string pack_name,
        const TemplateParameterDecl* parameter_pack,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_sizeof_expression(std::unique_ptr<Expr> expr,
                                                    SrcLoc loc) ;

    std::unique_ptr<Expr> collect_alignof_type(QualType type, SrcLoc loc) ;

    std::unique_ptr<Expr> collect_alignof_expression(std::unique_ptr<Expr> expr,
                                                     SrcLoc loc) ;

    std::unique_ptr<Expr> collect_cpp_noexcept_expression(
        std::unique_ptr<Expr> expr,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_unary_operation(UnaryOpTypes uop,
                                                  std::unique_ptr<Expr> expr,
                                                  SrcLoc loc) ;

    std::unique_ptr<Expr> collect_function_call(std::unique_ptr<Expr> callee,
                                                std::vector<std::unique_ptr<Expr>> args,
                                                std::vector<TemplateArgument> explicit_template_args,
                                                SrcLoc loc) ;

    std::unique_ptr<Expr> collect_function_call(std::unique_ptr<Expr> callee,
                                                std::vector<std::unique_ptr<Expr>> args,
                                                std::vector<TemplateArgument> explicit_template_args,
                                                bool has_explicit_template_args,
                                                SrcLoc loc) ;

    std::unique_ptr<Expr> collect_function_call(std::unique_ptr<Expr> callee,
                                                std::vector<std::unique_ptr<Expr>> args,
                                                SrcLoc loc) ;

    std::unique_ptr<Expr> collect_explicit_function_template_call(
        std::unique_ptr<Expr> callee,
        std::vector<TemplateArgument> explicit_template_args,
        std::vector<std::unique_ptr<Expr>> args,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_explicit_template_id_expression(
        std::unique_ptr<Expr> callee,
        std::vector<TemplateArgument> explicit_template_args,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_pack_expansion_expression(
        std::unique_ptr<Expr> pattern,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_fold_expression(
        BinOpTypes op,
        FoldDirection direction,
        std::unique_ptr<Expr> pattern,
        std::unique_ptr<Expr> init,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_array_subscript(std::unique_ptr<Expr> array,
                                                  std::unique_ptr<Expr> index,
                                                  SrcLoc loc) ;

    std::unique_ptr<Expr> collect_member_expression(std::unique_ptr<Expr> base,
                                                    const std::string& member_name,
                                                    bool is_arrow,
                                                    SrcLoc loc,
                                                    bool allow_overloaded_method_set = false,
                                                    bool suppress_virtual_dispatch = false,
                                                    bool requires_template_keyword = false) ;

    std::unique_ptr<Expr> collect_cpp_pseudo_destructor_expression(
        std::unique_ptr<Expr> base,
        QualType destroyed_type,
        bool is_arrow,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_member_pointer_literal_expression(
        const std::string& owner_name,
        const std::string& member_name,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_member_pointer_access_expression(
        std::unique_ptr<Expr> base,
        std::unique_ptr<Expr> member_pointer,
        bool is_arrow,
        SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_break_statement(SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_continue_statement(SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_case_statement(std::unique_ptr<Expr> const_expr,
                                                 std::unique_ptr<Expr> range_end,
                                                 std::unique_ptr<Stmt> stmt,
                                                 SrcLoc loc) ;

    std::unique_ptr<Stmt> collect_default_statement(std::unique_ptr<Stmt> stmt, SrcLoc loc) ;

    std::unique_ptr<Stmt> collect_if_statement(std::unique_ptr<Expr> condition,
                                               std::unique_ptr<Stmt> then_stmt,
                                               std::unique_ptr<Stmt> else_stmt,
                                               SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_switch_condition(std::unique_ptr<Expr> condition, SrcLoc loc) ;

    std::unique_ptr<Stmt> collect_switch_statement(std::unique_ptr<Expr> condition,
                                                   std::unique_ptr<Stmt> stmt,
                                                   SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_while_statement(std::unique_ptr<Expr> condition,
                                                  std::unique_ptr<Stmt> body_stmt,
                                                  SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_do_while_statement(std::unique_ptr<Expr> condition,
                                                     std::unique_ptr<Stmt> body_stmt,
                                                     SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_for_statement(std::unique_ptr<Stmt> init,
                                                std::unique_ptr<Expr> condition,
                                                std::unique_ptr<Expr> action,
                                                std::unique_ptr<Stmt> body_stmt,
                                                std::shared_ptr<Scope> scope,
                                                SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_goto_statement(const std::string& name, SrcLoc loc) ;

    std::unique_ptr<Stmt> collect_computed_goto_statement(std::unique_ptr<Expr> expr,
                                                          SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_labeled_statement(const std::string& name,
                                                    std::unique_ptr<Stmt> stmt,
                                                    SrcLoc loc) ;

    std::unique_ptr<Stmt> collect_return_statement(std::unique_ptr<Expr> expr,
                                                   SrcLoc loc,
                                                   QualType expected_return_type = QualType()) ;
    std::unique_ptr<Stmt> collect_cpp_try_statement(std::unique_ptr<Stmt> try_block,
                                                    std::vector<CppCatchClause> handlers,
                                                    SrcLoc loc) const ;

    std::unique_ptr<Stmt> collect_compound_statement(std::vector<std::unique_ptr<Stmt>> stmts,
                                                     std::shared_ptr<Scope> scope,
                                                     SrcLoc loc) ;

    std::unique_ptr<Stmt> collect_decl_statement(std::vector<std::unique_ptr<Decl>> decls,
                                                 SrcLoc loc = SrcLoc()) const ;

    std::unique_ptr<Stmt> collect_decl_statement(std::unique_ptr<Decl> decl,
                                                 SrcLoc loc = SrcLoc()) const ;

    std::unique_ptr<Decl> collect_nop_declaration(SrcLoc loc = SrcLoc()) const ;
    std::unique_ptr<Decl> collect_typedef_declaration(const std::string& name,
                                                      QualType type,
                                                      std::shared_ptr<Symbol> sym,
                                                      SrcLoc loc = SrcLoc()) const ;

    ArrayBoundResult collect_array_bound_expression(std::unique_ptr<Expr> expr) const ;

    std::unique_ptr<Decl> collect_static_assert_declaration(std::unique_ptr<Expr> condition,
                                                            std::string message,
                                                            bool has_message,
                                                            SrcLoc loc) const ;

    std::unique_ptr<FuncDecl> collect_function_declaration(const std::string& name,
                                                           std::shared_ptr<CType> type,
                                                           StorageClass storage_class,
                                                           bool is_inline,
                                                           std::optional<std::string> asm_label,
                                                           SrcLoc loc,
                                                           LanguageLinkage language_linkage = LanguageLinkage::None) ;

    std::unique_ptr<Decl> collect_field_declaration(QualType type,
                                                    const std::string& name,
                                                    SrcLoc loc) ;

    std::unique_ptr<Decl> collect_field_declaration(QualType type,
                                                    const std::string& name,
                                                    uint32_t bitfield_width,
                                                    SrcLoc loc) ;

    std::unique_ptr<ObjectDecl> collect_record_declaration(std::string tag,
                                                           std::vector<std::unique_ptr<Decl>> fields,
                                                           std::shared_ptr<CType> record_type,
                                                           bool is_union,
                                                           SrcLoc loc) const ;

    std::unique_ptr<ObjectDecl> collect_record_declaration(std::string tag,
                                                           std::shared_ptr<CType> record_type,
                                                           bool is_union,
                                                           SrcLoc loc) const ;

    std::unique_ptr<EnumConstantDecl> collect_enum_constant_declaration(std::string name,
                                                                        std::unique_ptr<Expr> init,
                                                                        SrcLoc loc) const ;

    std::unique_ptr<EnumDecl> collect_enum_declaration(std::string tag,
                                                       std::vector<std::unique_ptr<EnumConstantDecl>> constants,
                                                       std::shared_ptr<CType> enum_type,
                                                       SrcLoc loc) const ;

    std::unique_ptr<EnumDecl> collect_enum_declaration(std::string tag,
                                                       std::shared_ptr<CType> enum_type,
                                                       SrcLoc loc) const ;

    std::unique_ptr<Decl> collect_variable_declaration(QualType declared_type,
                                                       const std::string& name,
                                                       std::unique_ptr<Expr> init,
                                                       std::shared_ptr<Symbol> sym,
                                                       StorageClass storage_class,
                                                       const VariableDeclFlags& flags,
                                                       SrcLoc loc,
                                                       LanguageLinkage language_linkage = LanguageLinkage::None) ;

    std::unique_ptr<Decl> collect_parameter_declaration(QualType type,
                                                        const std::string& name,
                                                        std::shared_ptr<Symbol> sym,
                                                        StorageClass storage_class,
                                                        SrcLoc loc) ;

    std::shared_ptr<Symbol> collect_declare_variable_symbol(std::shared_ptr<Scope> scope,
                                                            std::shared_ptr<GlobalIdentTracker> global_scope,
                                                            const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            bool is_inline,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool skip_template_parameter_scopes = false) ;

    std::shared_ptr<Symbol> collect_declare_variable_symbol(std::shared_ptr<Scope> scope,
                                                            std::shared_ptr<GlobalIdentTracker> global_scope,
                                                            const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None) ;

    std::shared_ptr<Symbol> collect_declare_variable_symbol(const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            bool is_inline,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool skip_template_parameter_scopes = false) ;

    std::shared_ptr<Symbol> collect_declare_variable_symbol(const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None) ;

    std::shared_ptr<Symbol> collect_declare_function_symbol(std::shared_ptr<Scope> scope,
                                                            std::shared_ptr<GlobalIdentTracker> global_scope,
                                                            const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            bool is_consteval,
                                                            bool is_inline,
                                                            bool is_definition,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool is_cpp_member_function = false,
                                                            bool is_deleted = false,
                                                            bool is_defaulted = false) ;

    std::shared_ptr<Symbol> collect_declare_function_symbol(std::shared_ptr<Scope> scope,
                                                            std::shared_ptr<GlobalIdentTracker> global_scope,
                                                            const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            bool is_inline,
                                                            bool is_definition,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool is_cpp_member_function = false,
                                                            bool is_deleted = false,
                                                            bool is_defaulted = false) ;

    std::shared_ptr<Symbol> collect_declare_function_symbol(std::shared_ptr<Scope> scope,
                                                            std::shared_ptr<GlobalIdentTracker> global_scope,
                                                            const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_inline,
                                                            bool is_definition,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool is_cpp_member_function = false,
                                                            bool is_deleted = false,
                                                            bool is_defaulted = false) ;

    std::shared_ptr<Symbol> collect_declare_function_symbol(const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            bool is_consteval,
                                                            bool is_inline,
                                                            bool is_definition,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool is_cpp_member_function = false,
                                                            bool is_deleted = false,
                                                            bool is_defaulted = false) ;

    std::shared_ptr<Symbol> collect_declare_function_symbol(const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_constexpr,
                                                            bool is_inline,
                                                            bool is_definition,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool is_cpp_member_function = false,
                                                            bool is_deleted = false,
                                                            bool is_defaulted = false) ;

    std::shared_ptr<Symbol> collect_declare_function_symbol(const std::string& name,
                                                            QualType type,
                                                            StorageClass storage_class,
                                                            bool is_inline,
                                                            bool is_definition,
                                                            SrcLoc loc,
                                                            LanguageLinkage language_linkage = LanguageLinkage::None,
                                                            bool is_cpp_member_function = false,
                                                            bool is_deleted = false,
                                                            bool is_defaulted = false) ;

    std::shared_ptr<Symbol> collect_declare_typedef_symbol(std::shared_ptr<Scope> scope,
                                                           std::shared_ptr<GlobalIdentTracker> global_scope,
                                                           const std::string& name,
                                                           QualType type,
                                                           SrcLoc loc) ;

    std::shared_ptr<Symbol> collect_declare_typedef_symbol(const std::string& name,
                                                           QualType type,
                                                           SrcLoc loc) ;

    std::shared_ptr<Symbol> collect_declare_type_name_symbol(
        std::shared_ptr<Scope> scope,
        const std::string& name,
        QualType type,
        SrcLoc loc) ;

    std::shared_ptr<Symbol> collect_declare_type_name_symbol(
        const std::string& name,
        QualType type,
        SrcLoc loc) ;

    void collect_bind_template_decl(const std::string& name,
                                    const Decl* decl,
                                    LookupNamespace lookup_namespace) ;

    void collect_add_function_template_decl(const std::string& name,
                                            const Decl* decl) ;

    void collect_add_class_template_decl(const std::string& name,
                                         const Decl* decl) ;

    void collect_add_alias_template_decl(const std::string& name,
                                         const Decl* decl) ;

    void collect_add_variable_template_decl(const std::string& name,
                                            const Decl* decl) ;
    void collect_add_concept_decl(const std::string& name,
                                  const Decl* decl) ;

    std::unique_ptr<Expr> collect_binary_operation(std::unique_ptr<Expr> lhs,
                                                   std::unique_ptr<Expr> rhs,
                                                   BinOpTypes bop,
                                                   SrcLoc loc) ;

    std::unique_ptr<Expr> collect_compound_assign_operation(std::unique_ptr<Expr> lhs,
                                                            std::unique_ptr<Expr> rhs,
                                                            BinOpTypes bop,
                                                            SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_conditional_expression(std::unique_ptr<Expr> cond,
                                                         std::unique_ptr<Expr> true_expr,
                                                         std::unique_ptr<Expr> false_expr,
                                                         QualType forced_type,
                                                         SrcLoc loc) const ;

    std::unique_ptr<Expr> collect_generic_expression(std::unique_ptr<Expr> controlling,
                                                     std::vector<GenericAssociation> associations,
                                                     SrcLoc loc) ;

    // === Utility ===

    ValueCategory classify_value_category(Expr* expr) const ;

    static Expr* strip_implicit_casts(Expr* expr) ;

    bool expression_depends_on_template_parameters(
        const Expr* expr) const ;

    std::unique_ptr<Expr> collect_member_initializer_expression(
        std::unique_ptr<Expr> init,
        QualType member_type,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_member_initializer_expression(
        std::vector<std::unique_ptr<Expr>> init_args,
        QualType member_type,
        bool is_list_init,
        SrcLoc loc,
        bool allow_abstract_object_type_instantiation = false) ;

    // === Template operations ===

    bool deduce_function_template_specialization_arguments(
        const FunctionTemplateDecl* function_template,
        QualType specialized_function_type,
        std::vector<TemplateArgument>& deduced_arguments_out,
        const TemplateArgumentBindings* initial_bindings = nullptr) ;

    bool deduce_function_template_specialization_arguments_from_pattern(
        QualType pattern_function_type,
        const TemplateParameterList& template_parameters,
        const TemplateDecl* template_decl_for_defaults,
        QualType specialized_function_type,
        std::vector<TemplateArgument>& deduced_arguments_out,
        const TemplateArgumentBindings* initial_bindings = nullptr,
        uint8_t parsed_trailing_cv_qualifiers = QUAL_NONE,
        size_t implicit_object_parameter_count = 0) ;

    QualType collect_substitute_template_type(
        QualType type,
        const TemplateParameterList& parameters,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) {
        return substitute_template_type(type, parameters, arguments, loc);
    }

    QualType collect_partially_substitute_template_type(
        QualType type,
        const TemplateParameterList& parameters,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) {
        return partially_substitute_template_type(
            type,
            parameters,
            arguments,
            loc);
    }

    bool is_definition_bearing_variable_declaration(
        StorageClass storage_class,
        const VariableDeclFlags& flags,
        const Expr* init) const ;

    bool is_inline_equivalent_variable_definition(
        StorageClass storage_class,
        const VariableDeclFlags& flags,
        const Expr* init) const ;

    void enter_unevaluated_context(const char* reason) ;

    void leave_unevaluated_context() ;

    bool in_unevaluated_context() const ;

    class UnevaluatedContextScope {
    public:
        UnevaluatedContextScope(Collect* collect, const char* reason)
            : collect_(collect) {
            if (collect_) {
                collect_->enter_unevaluated_context(reason);
            }
        }
        ~UnevaluatedContextScope() {
            if (collect_) {
                collect_->leave_unevaluated_context();
            }
        }
        UnevaluatedContextScope(const UnevaluatedContextScope&) = delete;
        UnevaluatedContextScope& operator=(const UnevaluatedContextScope&) = delete;
    private:
        Collect* collect_ = nullptr;
    };

    void enter_immediate_function_context() ;

    void leave_immediate_function_context() ;

    bool in_immediate_function_context() const ;

    class ImmediateFunctionContextScope {
    public:
        ImmediateFunctionContextScope(Collect* collect, bool active)
            : collect_(collect), active_(active) {
            if (collect_ && active_) {
                collect_->enter_immediate_function_context();
            }
        }

        ~ImmediateFunctionContextScope() {
            if (collect_ && active_) {
                collect_->leave_immediate_function_context();
            }
        }

        ImmediateFunctionContextScope(const ImmediateFunctionContextScope&) = delete;
        ImmediateFunctionContextScope& operator=(
            const ImmediateFunctionContextScope&) = delete;

    private:
        Collect* collect_ = nullptr;
        bool active_ = false;
    };

private:
    friend class CollectRecordBuilder;

    struct CollectRecordBuildContext {
        const CppRecordDecl* record = nullptr;
        SrcLoc loc;
        std::string record_name;
        std::string tag;
        bool is_union_record = false;
        std::shared_ptr<ObjectType> record_type;
        ObjectDecl* semantic_decl = nullptr;
        std::vector<std::unique_ptr<Decl>>* transient_decls_out = nullptr;
        CppRecordDeferredBodyCallback deferred_body_callback;

        std::vector<RecordSemanticState::Base> bases;
        std::vector<RecordSemanticState::VirtualBase> virtual_bases;

        std::vector<ObjectType::Field> fields;
        std::vector<RecordSemanticState::Method> methods;
        std::vector<RecordSemanticState::MethodTemplate> method_templates;
        std::vector<RecordSemanticState::StaticDataMember> static_data_members;
        std::vector<RecordSemanticState::NestedType> nested_types;
        std::vector<RecordSemanticState::NestedTemplate> nested_templates;
        std::vector<RecordSemanticState::EnumeratorMember> enumerator_members;
        std::unordered_set<std::string> seen_static_data_member_names;
        std::vector<RecordSemanticState::Constructor> constructors;
        std::vector<RecordSemanticState::Destructor> destructors;
        std::vector<const FieldDecl*> required_ctor_member_init_fields;

        std::vector<RecordSemanticState::VirtualSlot> semantic_virtual_slots;
        RecordSemanticState semantic_state;
    };

    struct DelayedDiagnostic {
        bool is_error = true;
        std::string message;
        SrcLoc loc;
    };

    struct SwitchContext {
        bool has_default = false;
        std::unordered_set<int64_t> case_values;
        QualType switch_type = nullptr;
    };

public:
    bool finalize_cpp_lambda_semantics(CppLambdaExpr& lambda,
                                       std::string* error_out = nullptr);

    VariableDecl* instantiate_variable_template_specialization_for_clone(
        const VariableTemplateDecl* variable_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        std::shared_ptr<Symbol>* specialization_symbol_out = nullptr) {
        return instantiate_variable_template_specialization(
            variable_template,
            arguments,
            loc,
            specialization_symbol_out);
    }

    void collect_record_register_function_default_arguments(
        const std::shared_ptr<Symbol>& sym,
        const FuncDecl* decl,
        SrcLoc fallback_loc) const;

    void collect_record_resolve_bases(CollectRecordBuildContext& ctx) const;
    void collect_record_walk_virtual_bases(CollectRecordBuildContext& ctx) const;
    void collect_record_collect_members(CollectRecordBuildContext& ctx);
    void collect_record_synthesize_implicit_members(
        CollectRecordBuildContext& ctx) const;
    void collect_record_materialize_defaulted_method_bodies(
        CollectRecordBuildContext& ctx);
    bool collect_materialize_defaulted_constructor(
        CppConstructorDecl* ctor_decl,
        const ObjectDecl* owner_record_decl,
        const RecordSemanticState& owner_state);
    bool collect_materialize_defaulted_assignment_body(
        CppMethodDecl* method_decl,
        const ObjectDecl* owner_record_decl,
        const RecordSemanticState& owner_state,
        bool use_move);
    bool collect_materialize_defaulted_copy_assignment_body(
        CppMethodDecl* method_decl,
        const ObjectDecl* owner_record_decl,
        const RecordSemanticState& owner_state);
    bool collect_materialize_defaulted_move_assignment_body(
        CppMethodDecl* method_decl,
        const ObjectDecl* owner_record_decl,
        const RecordSemanticState& owner_state);
    void collect_record_resolve_virtual_dispatch(
        CollectRecordBuildContext& ctx) const;
    void collect_record_compute_layout(CollectRecordBuildContext& ctx) const;
    const RecordSemanticState* query_lookup_record_semantics(
        const ObjectDecl* record_decl) const;
    const RecordSemanticState* query_publish_record_semantics(
        const ObjectDecl* record_decl,
        RecordSemanticState state);
    void query_erase_record_semantics(const ObjectDecl* record_decl);
    bool query_lookup_enum_semantics(
        const EnumDecl* enum_decl,
        EnumSemanticState& state_out) const;
    void query_publish_enum_semantics(
        const EnumDecl* enum_decl,
        EnumSemanticState state);
    QualType query_lookup_template_specialization_resolved_type(
        const TemplateSpecializationType* type) const;
    void query_publish_template_specialization_resolved_type(
        const TemplateSpecializationType* type,
        QualType resolved_type);
    QualType query_lookup_dependent_name_resolved_type(
        const DependentNameType* type) const;
    void query_publish_dependent_name_resolved_type(
        const DependentNameType* type,
        QualType resolved_type);

private:
    void collect_record_publish_state(ObjectDecl* semantic_decl,
                                      const std::shared_ptr<ObjectType>& record_type,
                                      const RecordSemanticState& state);
    void collect_record_publish_semantics(CollectRecordBuildContext& ctx);

    struct FunctionDefinitionState {
        bool in_function = false;
        std::string current_function_name;
        std::string current_pretty_function_name;
        QualType current_function_type = nullptr;
        QualType current_function_return_type = nullptr;
        bool current_function_has_return_statement = false;
        bool current_function_has_cxx_auto_return_deduction = false;
        bool current_function_has_deferred_cxx_auto_return_deduction = false;
        QualType current_function_cxx_auto_return_pattern = nullptr;
        bool current_function_is_cpp_member = false;
        bool current_function_is_static_cpp_member = false;
        QualType current_function_cpp_this_type = nullptr;
        int loop_depth = 0;
        int switch_depth = 0;
        std::vector<SwitchContext> switch_context_stack;
        std::unordered_set<std::string> labels_defined;
        std::unordered_set<std::string> labels_referenced;
        std::unordered_map<std::string, SrcLoc> label_definition_locs;
        std::unordered_map<std::string, SrcLoc> label_reference_locs;
        std::vector<DelayedDiagnostic> delayed_diagnostics;
        int unevaluated_depth = 0;
        int immediate_function_context_depth = 0;
        std::vector<std::string> unevaluated_context_stack;

        CppThisContext cpp_this_context() const {
            return CppThisContext{
                current_function_is_cpp_member,
                current_function_is_static_cpp_member,
                current_function_cpp_this_type
            };
        }
    };

    struct TentativeSnapshot {
        bool materialized = false;

        // Scope state
        std::shared_ptr<Scope> current_scope;
        std::shared_ptr<DeclContext> translation_unit_decl_context;
        std::shared_ptr<DeclContext> current_decl_context;
        std::shared_ptr<GlobalIdentTracker> current_global_scope_ptr;
        std::unordered_map<std::string, std::vector<std::shared_ptr<Symbol>>> global_symbols;

        // Function body state (bundled)
        FunctionDefinitionState func_state;
        QualType current_cpp_record_lookup_type = nullptr;
        std::vector<FunctionDefinitionState> function_definition_stack;

        struct DeclContextMutationCheckpoint {
            std::shared_ptr<DeclContext> context;
            size_t declaration_count = 0;
            size_t lexical_child_count = 0;
            size_t namespace_binding_count = 0;
            size_t namespace_alias_count = 0;
            size_t namespace_nomination_count = 0;
            bool is_inline_namespace = false;
            DeclContext* inline_enclosing_namespace = nullptr;
            uint64_t next_lookup_event_index = 1;
        };

        struct ScopeMutationCheckpoint {
            std::shared_ptr<Scope> scope;
            Scope state;
        };

        struct GlobalScopeMutationCheckpoint {
            std::shared_ptr<GlobalIdentTracker> scope;
            std::unordered_map<std::string, std::vector<std::shared_ptr<Symbol>>>
                all_variables;
        };

        std::unordered_map<const DeclContext*, DeclContextMutationCheckpoint>
            decl_context_mutations;
        std::unordered_map<const Scope*, ScopeMutationCheckpoint> scope_mutations;
        std::unordered_map<const GlobalIdentTracker*, GlobalScopeMutationCheckpoint>
            global_scope_mutations;
    };

    struct FieldLookupResult {
        const ObjectType::Field* field = nullptr;
        const ObjectDecl* owner_record_decl = nullptr;
        const ObjectDecl* virtual_base_record_decl = nullptr;
        std::vector<uint32_t> path;
        size_t byte_offset = 0;
        size_t relative_byte_offset = 0;
        int matches = 0;
    };

    enum class OverloadImplicitObjectArgKind {
        None,
        MemberObject,
        Regular
    };

    struct OverloadCallCandidate {
        std::shared_ptr<Symbol> symbol = nullptr;
        OverloadImplicitObjectArgKind implicit_object_arg_kind =
            OverloadImplicitObjectArgKind::None;
    };

    enum class OverloadCandidateKind : uint8_t {
        Function,
        ConversionConstructor,
        ConversionFunction
    };

    enum class OverloadFailureKind : uint8_t {
        None,
        NotCallable,
        ArityTooFew,
        ArityTooMany,
        ImplicitObjectMissing,
        ImplicitObjectRefQualifierMismatch,
        ImplicitObjectConversionFailure,
        ArgumentConversionFailure,
        DeletedCandidate,
        InaccessibleCandidate,
        InvalidCandidateState
    };

    struct OverloadFailure {
        OverloadFailureKind kind = OverloadFailureKind::None;
        size_t argument_index = std::numeric_limits<size_t>::max();
        size_t required_arg_count = 0;
        size_t provided_arg_count = 0;
        bool arity_is_minimum = false;
        QualType from = nullptr;
        QualType to = nullptr;
        FunctionRefQualifierKind ref_qualifier =
            FunctionRefQualifierKind::None;
        std::string note;

        bool has_failure() const {
            return kind != OverloadFailureKind::None;
        }
    };

    struct OverloadCandidateEval {
        OverloadCandidateKind candidate_kind = OverloadCandidateKind::Function;
        std::shared_ptr<Symbol> symbol = nullptr;
        std::shared_ptr<FunctionType> function_type = nullptr;
        std::vector<ImplicitConversionSequence> conversions;
        bool viable = false;
        bool is_deleted = false;
        OverloadImplicitObjectArgKind implicit_object_arg_kind =
            OverloadImplicitObjectArgKind::None;
        OverloadFailure failure;
        const RecordSemanticState::Constructor* constructor = nullptr;
        const RecordSemanticState::Method* conversion_function = nullptr;
        const ObjectDecl* owner_record_decl = nullptr;
        size_t user_param_start = 0;
        size_t max_user_param_count = 0;
        size_t required_user_param_count = 0;
    };

    struct OverloadCandidateSet {
        std::vector<OverloadCandidateEval> evaluated;
        std::vector<size_t> viable_indices;
    };

    struct OverloadConversionMemoKey {
        const Expr* arg = nullptr;
        const CType* to_type = nullptr;
        uint8_t to_qualifiers = 0;
        bool allow_user_defined = true;

        bool operator==(const OverloadConversionMemoKey& other) const {
            return arg == other.arg &&
                   to_type == other.to_type &&
                   to_qualifiers == other.to_qualifiers &&
                   allow_user_defined == other.allow_user_defined;
        }
    };

    struct OverloadConversionMemoKeyHash {
        size_t operator()(const OverloadConversionMemoKey& key) const;
    };

    using OverloadConversionMemoCache = std::unordered_map<
        OverloadConversionMemoKey,
        ImplicitConversionSequence,
        OverloadConversionMemoKeyHash>;

    struct MemberCallSelection {
        bool selected = false;
        bool is_arrow = false;
        bool suppress_virtual_dispatch = false;
        bool has_implicit_object_argument = false;
        std::string name;
        std::shared_ptr<Symbol> symbol = nullptr;
        const ObjectDecl* record_decl = nullptr;
    };

    struct CallFinalizationContext {
        bool member_pointer_function_call = false;
        std::shared_ptr<FunctionType> function_type = nullptr;
        bool constructor_call = false;
        std::shared_ptr<Symbol> constructor_symbol = nullptr;
        QualType constructor_object_type = nullptr;
        std::shared_ptr<Symbol> callee_symbol = nullptr;
        size_t named_param_count = 0;
        size_t implicit_param_count = 0;
        size_t explicit_named_param_count = 0;
        size_t required_explicit_named_param_count = 0;
    };

    struct CppConversionConstructorMatch {
        std::shared_ptr<Symbol> ctor_symbol = nullptr;
        std::shared_ptr<FunctionType> ctor_function_type = nullptr;
        size_t user_param_start = 0;
        size_t max_user_param_count = 0;
    };

    struct CppLambdaFunctionPointerConversionMatch {
        const ObjectDecl* closure_owner = nullptr;
        const FuncDecl* invoker_decl = nullptr;
        std::shared_ptr<FunctionType> invoker_function_type = nullptr;
    };

    struct CppConversionFunctionMatch {
        const RecordSemanticState::Method* method = nullptr;
        const ObjectDecl* owner_record_decl = nullptr;
        std::shared_ptr<Symbol> method_symbol = nullptr;
        std::shared_ptr<FunctionType> method_function_type = nullptr;
        QualType conversion_target_type = nullptr;
    };

    enum class CppUserDefinedConversionKind : uint8_t {
        Constructor,
        LambdaFunctionPointer,
        ConversionFunction,
    };

    struct CppUserDefinedConversionMatch {
        CppUserDefinedConversionKind kind =
            CppUserDefinedConversionKind::Constructor;
        CppConversionConstructorMatch constructor;
        CppLambdaFunctionPointerConversionMatch lambda_function_pointer;
        CppConversionFunctionMatch conversion_function;
    };

    struct VariableInitializationSelection {
        std::shared_ptr<Symbol> constructor_symbol = nullptr;
        std::vector<std::unique_ptr<Expr>> constructor_args;
        bool constructor_is_list_init = false;
        std::unique_ptr<Expr> nonconstructor_init_expr = nullptr;
        bool used_constructor_initialization = false;
        std::shared_ptr<Symbol> destructor_symbol = nullptr;
    };

    struct ConstructorCandidateEval {
        const RecordSemanticState::Constructor* ctor = nullptr;
        std::shared_ptr<FunctionType> function_type = nullptr;
        size_t user_param_start = 0;
        size_t max_user_param_count = 0;
        size_t required_user_param_count = 0;
        std::vector<ImplicitConversionSequence> conversions;
        bool viable = false;
        bool is_synthesized_implicit_ctor = false;
        bool is_synthesized_implicit_copy = false;
        QualType synthesized_param_type = nullptr;
    };

    void find_field_recursive(const ObjectType* record,
                              const std::string& name,
                              std::vector<uint32_t>& path,
                              size_t base_offset,
                              FieldLookupResult& result) const ;

    int classify_type(QualType type) const ;

    bool contains_auto_type(const std::shared_ptr<CType>& type) const ;

    std::shared_ptr<CType> replace_auto_type(const std::shared_ptr<CType>& type,
                                             const std::shared_ptr<CType>& deduced) const ;

    bool contains_typeof_expr_type(const std::shared_ptr<CType>& type) const ;

    QualType resolve_typeof_types(QualType type, SrcLoc loc = SrcLoc()) ;

    enum class DeferredTypeResolutionMode : uint8_t {
        TryRealize,
        Finalize
    };

    bool contains_deferred_semantic_type(const std::shared_ptr<CType>& type) const ;

    QualType try_realize_deferred_semantic_type(QualType type) ;

    QualType finalize_deferred_semantic_type(QualType type,
                                             SrcLoc loc = SrcLoc()) ;

    QualType resolve_deferred_semantic_type_impl(
        QualType type,
        SrcLoc loc,
        DeferredTypeResolutionMode mode) ;

    bool decltype_expression_requires_deferred_resolution(
        const Expr* expr) const ;

    QualType resolve_deferred_decltype_expr_type(
        const DecltypeExprType& decltype_type,
        QualType original_type,
        SrcLoc loc,
        DeferredTypeResolutionMode mode) ;

    void rewrite_deferred_template_arguments_in_place(
        std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        DeferredTypeResolutionMode mode) ;

    QualType resolve_deferred_template_specialization_type(
        TemplateSpecializationType& specialization,
        QualType original_type,
        SrcLoc loc,
        DeferredTypeResolutionMode mode) ;

    QualType lookup_deferred_dependent_name_type(
        const DependentNameType& dependent_name,
        SrcLoc loc,
        bool* matched_nested_template) ;

    QualType handle_unresolved_dependent_name_type_lookup(
        const DependentNameType& dependent_name,
        QualType original_type,
        SrcLoc loc,
        bool matched_nested_template,
        DeferredTypeResolutionMode mode) const ;

    QualType resolve_deferred_dependent_name_type(
        DependentNameType& dependent_name,
        QualType original_type,
        SrcLoc loc,
        DeferredTypeResolutionMode mode) ;

    ObjectDecl* try_instantiate_class_template_specialization(
        const ClassTemplateDecl* class_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    QualType try_instantiate_alias_template_specialization(
        const AliasTemplateDecl* alias_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    bool complete_template_argument_bindings_with_substituted_defaults(
        const TemplateDecl* template_decl,
        TemplateArgumentBindings& bindings_out,
        SrcLoc loc,
        std::string* error_out = nullptr) ;

    bool bind_template_arguments_for_specialization(
        const TemplateDecl* template_decl,
        const std::vector<TemplateArgument>& arguments,
        TemplateArgumentBindings& bindings_out,
        SrcLoc loc,
        std::string* error_out = nullptr) ;

    struct ClassTemplateSpecializationInstantiator;
    struct FunctionTemplateSpecializationInstantiator;
    struct VariableTemplateSpecializationInstantiator;

    ObjectDecl* instantiate_class_template_specialization(
        const ClassTemplateDecl* class_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    QualType instantiate_alias_template_specialization(
        const AliasTemplateDecl* alias_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    bool deduce_function_template_call_arguments(
        const FunctionTemplateDecl* function_template,
        const std::vector<std::unique_ptr<Expr>>& call_args,
        std::vector<TemplateArgument>& deduced_arguments_out,
        const TemplateArgumentBindings* initial_bindings = nullptr) ;

    bool deduce_function_template_call_arguments(
        const FunctionTemplateDecl* function_template,
        const std::vector<Expr*>& call_args,
        std::vector<TemplateArgument>& deduced_arguments_out,
        const TemplateArgumentBindings* initial_bindings = nullptr) ;

    bool probe_function_template_call_specialization(
        const FunctionTemplateDecl* function_template,
        const std::vector<Expr*>& call_args,
        SrcLoc loc,
        std::shared_ptr<Symbol>& specialization_symbol_out,
        const TemplateArgumentBindings* initial_bindings = nullptr,
        std::vector<TemplateArgument>* specialization_arguments_out = nullptr) ;

    enum class TemplatePartialOrderingResult : uint8_t {
        Unordered,
        Equivalent,
        LhsMoreSpecialized,
        RhsMoreSpecialized,
    };

    TemplatePartialOrderingResult compare_function_template_partial_ordering(
        const FunctionTemplateDecl* lhs_template,
        const FunctionTemplateDecl* rhs_template) ;

    bool is_function_template_more_specialized(
        const FunctionTemplateDecl* lhs_template,
        const FunctionTemplateDecl* rhs_template) ;

    FuncDecl* instantiate_function_template_specialization(
        const FunctionTemplateDecl* function_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        std::shared_ptr<Symbol>* specialization_symbol_out = nullptr,
        bool instantiate_definition = true) ;

    VariableDecl* instantiate_variable_template_specialization(
        const VariableTemplateDecl* variable_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        std::shared_ptr<Symbol>* specialization_symbol_out = nullptr) ;

    QualType substitute_template_type(
        QualType type,
        const TemplateParameterList& parameters,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    std::vector<TemplateArgument> substitute_template_arguments(
        const std::vector<TemplateArgument>& arguments,
        const TemplateParameterList& parameters,
        const std::vector<TemplateArgument>& specialization_arguments,
        SrcLoc loc) ;

    QualType substitute_class_template_type(
        QualType type,
        const ClassTemplateDecl* class_template,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc) ;

    std::vector<TemplateArgument> substitute_class_template_arguments(
        const std::vector<TemplateArgument>& arguments,
        const ClassTemplateDecl* class_template,
        const std::vector<TemplateArgument>& specialization_arguments,
        SrcLoc loc) ;

    QualType substitute_template_type_with_bindings(
        QualType type,
        const TemplateParameterList& parameters,
        const TemplateArgumentBindings& argument_bindings,
        SrcLoc loc,
        bool allow_unsubstituted_parameters = false) ;

    std::vector<TemplateArgument> substitute_template_arguments_with_bindings(
        const std::vector<TemplateArgument>& arguments,
        const TemplateParameterList& parameters,
        const TemplateArgumentBindings& argument_bindings,
        SrcLoc loc,
        bool allow_unsubstituted_parameters = false) ;

    QualType partially_substitute_template_type(
        QualType type,
        const TemplateParameterList& parameters,
        const std::vector<TemplateArgument>& specialization_arguments,
        SrcLoc loc) ;

    struct ResolvedInitPath {
        std::vector<size_t> path;
        std::shared_ptr<CType> target_type;
    };

    bool is_aggregate_type(const std::shared_ptr<CType>& type) const ;

    bool eval_designator_index_expr(Expr* expr, int64_t& out) const ;

    std::shared_ptr<CType> init_get_child_type(std::shared_ptr<CType> parent_type,
                                               size_t index,
                                               SrcLoc loc) const ;

    void init_assign_to_path(InitListExpr* out,
                             std::shared_ptr<CType> cur_type,
                             const std::vector<size_t>& path,
                             size_t depth,
                             std::shared_ptr<Expr> value,
                             SrcLoc loc) const ;

    bool resolve_initializer_designators(const std::vector<Designator>& designators,
                                         std::shared_ptr<CType> base_type,
                                         std::vector<ResolvedInitPath>& out_paths,
                                         size_t& outer_end,
                                         bool& has_range) const ;

    std::unique_ptr<Expr> transform_init_value(std::unique_ptr<Expr> expr,
                                                       std::shared_ptr<CType> type) const ;

    std::unique_ptr<Expr> init_from_single_value(std::unique_ptr<Expr> value,
                                                         std::shared_ptr<CType> type,
                                                         SrcLoc loc) const ;

    std::unique_ptr<Expr> consume_for_type(std::vector<InitElement>& elements,
                                                   size_t& index,
                                                   std::shared_ptr<CType> type,
                                                   bool ignore_first_designators,
                                                   size_t array_start_index = 0) const ;

    std::unique_ptr<Expr> process_init_list_expression(std::unique_ptr<InitListExpr> init_list,
                                                               std::shared_ptr<CType> type) const ;

    std::unique_ptr<Expr> process_initializer_for_type(std::unique_ptr<Expr> init,
                                                               QualType declared_type,
                                                               SrcLoc loc) ;

    void resolve_auto_variable_type(QualType& declared_type,
                                    std::unique_ptr<Expr>& init,
                                    const std::shared_ptr<Symbol>& sym,
                                    const std::string& name,
                                            SrcLoc loc) ;
    void resolve_auto_variable_type_from_expr(
        QualType& declared_type,
        const Expr* init_expr,
        const std::shared_ptr<Symbol>& sym,
        const std::string& name,
        SrcLoc loc) ;

    void reconcile_array_declared_type_with_symbol(
        QualType& declared_type,
        const std::shared_ptr<Symbol>& sym) const ;

    void validate_variable_declared_type(QualType& declared_type,
                                                 const std::string& name,
                                                 const std::unique_ptr<Expr>& init,
                                                 StorageClass storage_class,
                                                 bool is_inline,
                                                 bool is_file_scope,
                                                 bool is_cpp_static_data_member,
                                                 SrcLoc loc) const ;

    bool select_constructor_for_variable_initialization(
        std::shared_ptr<ObjectType> record_type,
        std::vector<std::unique_ptr<Expr>> ctor_args,
        bool ctor_is_list_init,
        bool ctor_is_copy_initialization,
        QualType declared_type,
        SrcLoc loc,
        VariableInitializationSelection& selection) ;

    ConstructorCandidateEval evaluate_variable_constructor_candidate(
        const RecordSemanticState::Constructor& ctor,
        const ObjectDecl* record_decl,
        const std::vector<std::unique_ptr<Expr>>& ctor_args,
        bool ctor_is_copy_initialization) ;

    std::string describe_variable_constructor_candidate(
        const ConstructorCandidateEval& eval,
        const ObjectDecl* record_decl,
        QualType declared_type) const ;

    std::string describe_variable_constructor_candidates(
        const std::vector<ConstructorCandidateEval>& evaluated,
        const std::vector<size_t>& indices,
        const ObjectDecl* record_decl,
        QualType declared_type) const ;

    bool is_better_variable_constructor_candidate(
        const ConstructorCandidateEval& lhs,
        const ConstructorCandidateEval& rhs) const ;

    std::optional<size_t> select_best_variable_constructor_candidate_index(
        const std::vector<ConstructorCandidateEval>& evaluated,
        const std::vector<size_t>& viable_indices) const ;

    bool materialize_variable_constructor_selection(
        const ConstructorCandidateEval& chosen,
        std::vector<std::unique_ptr<Expr>> ctor_args,
        bool ctor_is_list_init,
        QualType declared_type,
        SrcLoc loc,
        VariableInitializationSelection& selection) ;

    std::shared_ptr<Symbol> select_destructor_for_variable(
        const std::string& name,
        QualType declared_type,
        const std::shared_ptr<ObjectType>& record_type,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> builtin_call_expression(BuiltinKind kind,
                                                          std::vector<std::unique_ptr<Expr>> args,
                                                          SrcLoc loc) const ;

    std::unique_ptr<Expr> builtin_call_expression_special_cases(
        BuiltinKind kind,
        std::vector<std::unique_ptr<Expr>>& args,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> builtin_call_expression_fixed_cases(
        BuiltinKind kind,
        std::vector<std::unique_ptr<Expr>>& args,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> builtin_call_expression_atomic_cases(
        BuiltinKind kind,
        std::vector<std::unique_ptr<Expr>>& args,
        SrcLoc loc) const ;

    void finalize_sizeof_node(SizeOfExpr* node,
                              const std::shared_ptr<CType>& target_type,
                              SrcLoc loc) ;

    void finalize_alignof_node(AlignOfExpr* node,
                               const std::shared_ptr<CType>& target_type,
                               SrcLoc loc) ;

    void report_error(const std::string& message, SrcLoc loc) const ;

    void report_warning(const std::string& message, SrcLoc loc) const ;

    void queue_delayed_error(const std::string& message, SrcLoc loc) ;

    void queue_delayed_warning(const std::string& message, SrcLoc loc) ;

    void flush_delayed_diagnostics() ;

    std::unique_ptr<Expr> prepare_unevaluated_operand(std::unique_ptr<Expr> expr,
                                                               const char* reason) ;

    ImplicitConversionSequence build_implicit_conversion_sequence(QualType from,
                                                                  QualType to,
                                                                  ExprUseContext context) const ;
    ImplicitConversionSequence build_cpp_overload_conversion_sequence(Expr* arg,
                                                                      QualType to,
                                                                      bool allow_user_defined = true) ;

    ImplicitConversionSequence build_cpp_overload_reference_conversion_sequence(
        Expr* arg,
        QualType from,
        QualType to,
        bool allow_user_defined) ;

    ImplicitConversionSequence build_cpp_overload_nonreference_conversion_sequence(
        Expr* arg,
        QualType from,
        QualType to,
        bool allow_user_defined) ;

    std::optional<CppConversionConstructorMatch>
    select_cpp_conversion_constructor(Expr* arg,
                                              QualType target_object_type,
                                              bool allow_explicit_constructors) ;

    std::optional<CppUserDefinedConversionMatch>
    select_cpp_user_defined_conversion(
        Expr* arg,
        QualType target_type,
        bool allow_explicit_constructors = false,
        bool allow_explicit_conversion_functions = false) ;

    std::unique_ptr<Expr> build_cpp_user_defined_conversion_expr(
        std::unique_ptr<Expr> arg,
        QualType target_type,
        SrcLoc loc) ;

    std::unique_ptr<Expr> build_cpp_selected_user_defined_conversion_expr(
        std::unique_ptr<Expr> arg,
        QualType target_type,
        const CppUserDefinedConversionMatch& conversion_match,
        SrcLoc loc) ;

    std::unique_ptr<Expr> convert_cpp_braced_init_argument(
        std::unique_ptr<Expr> arg,
        QualType target_type,
        SrcLoc loc) ;

    bool probe_cpp_braced_init_argument_conversion(
        Expr* arg,
        QualType target_type,
        SrcLoc loc,
        ImplicitConversionSequence& seq_out) ;

    std::unique_ptr<Expr> build_overload_implicit_object_arg(
        OverloadImplicitObjectArgKind implicit_arg_kind,
        std::unique_ptr<Expr> object_expr,
        bool object_expr_is_pointer,
        SrcLoc loc) ;

    std::shared_ptr<Symbol> make_default_allocation_like_operator_symbol(
        const std::string& operator_name) const ;

    std::unique_ptr<Expr> select_cpp_allocation_like_function(
        const std::string& operator_name,
        const std::shared_ptr<ObjectType>& lookup_record,
        bool force_global_lookup,
        const std::vector<std::unique_ptr<Expr>>& call_args,
        SrcLoc loc,
        std::shared_ptr<Symbol>& selected_symbol_out) ;

    std::unique_ptr<Expr> named_cast_error(
        const std::string& message,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> cpp_const_named_cast(
        std::unique_ptr<Expr> expr,
        QualType target_type,
        QualType target_no_ref,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> cpp_dynamic_named_cast(
        std::unique_ptr<Expr> expr,
        QualType target_type,
        QualType target_no_ref,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> cpp_reinterpret_named_cast(
        std::unique_ptr<Expr> expr,
        QualType source_type,
        QualType target_type,
        QualType target_no_ref,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> cpp_static_named_cast(
        std::unique_ptr<Expr> expr,
        QualType source_type,
        QualType target_type,
        QualType target_no_ref,
        SrcLoc loc) const ;

    void report_conversion_failure(const std::string& context,
                                   QualType from,
                                   QualType to,
                                   SrcLoc loc) const ;

    void report_invalid_binary_operands(const std::string& op,
                                        QualType lhs,
                                        QualType rhs,
                                        SrcLoc loc) const ;

    void report_invalid_compound_assign_operands(const std::string& op,
                                                 QualType lhs,
                                                 QualType rhs,
                                                 SrcLoc loc) const ;

    std::shared_ptr<CType> get_builtin_int() const ;

    std::shared_ptr<CType> get_builtin_uint() const ;

    std::shared_ptr<CType> get_builtin_longlong() const ;

    std::shared_ptr<CType> get_builtin_double() const ;

    std::shared_ptr<CType> get_builtin_float() const ;

    std::shared_ptr<CType> get_builtin_long_double() const ;

    std::shared_ptr<CType> get_builtin_long() const ;

    std::shared_ptr<CType> get_builtin_ulong() const ;

    std::shared_ptr<CType> get_builtin_char() const ;

    std::shared_ptr<CType> get_builtin_void() const ;

    std::shared_ptr<CType> get_builtin_bool() const ;

    QualType integer_promotion_type(QualType type) const ;

    QualType decay_parameter_type(QualType type) const ;

    std::unique_ptr<Expr> cast_if_needed(std::unique_ptr<Expr> expr, QualType target_type) const ;

    std::unique_ptr<Expr> apply_default_argument_promotions(std::unique_ptr<Expr> expr) const ;

    QualType usual_arithmetic_conversion_type(QualType lhs, QualType rhs) const ;

    QualType unsigned_counterpart(QualType type) const ;

    bool is_null_pointer_constant_expr(Expr* expr) const ;

    bool are_char_family_compatible(const CType& a, const CType& b) const ;

    bool pointers_to_compatible_types(QualType lhs, QualType rhs) const ;
    MemberPointerConversionResult analyze_member_pointer_conversion(
        QualType from, QualType to) const ;
    bool member_pointer_convertible_to(QualType from, QualType to) const ;
    bool member_pointers_to_compatible_types(QualType lhs, QualType rhs) const ;

    bool is_const_qualified_lvalue(Expr* expr) const ;

    bool is_modifiable_lvalue(Expr* expr) const ;

    std::unique_ptr<Expr> resolve_overloaded_function_call(FuncCall* call,
                                                                    VarRef* callee_ref,
                                                                    SrcLoc loc) ;

    std::unique_ptr<Expr> finalize_call_expression(
        std::unique_ptr<FuncCall> call,
        const MemberCallSelection& member_call_selection,
        SrcLoc loc) ;

    std::unique_ptr<Expr> try_function_object_call_overload(
        std::unique_ptr<FuncCall>& call,
        SrcLoc loc) ;

    std::unique_ptr<Expr> try_builtin_or_overloaded_varref_call(
        std::unique_ptr<FuncCall>& call,
        SrcLoc loc) ;

    std::unique_ptr<Expr> collect_explicit_template_call_impl(
        std::unique_ptr<Expr> callee,
        std::vector<TemplateArgument> explicit_template_args,
        std::vector<std::unique_ptr<Expr>> args,
        SrcLoc loc,
        QualType implicit_this_type = QualType()) ;
    std::unique_ptr<Expr> collect_explicit_template_id_impl(
        std::unique_ptr<Expr> callee,
        std::vector<TemplateArgument> explicit_template_args,
        SrcLoc loc) ;
    std::unique_ptr<Expr> collect_dependent_call_expression(
        std::unique_ptr<Expr> callee,
        std::vector<std::unique_ptr<Expr>> args,
        SrcLoc loc) ;

    std::unique_ptr<Expr> build_dependent_explicit_template_call(
        std::unique_ptr<Expr> callee,
        std::vector<TemplateArgument> explicit_template_args,
        std::vector<std::unique_ptr<Expr>> args,
        SrcLoc loc) ;
    std::unique_ptr<Expr> materialize_concrete_qualified_lookup_expression(
        const std::string& name,
        const DependentLookupQualifier& qualifier,
        bool looks_like_call,
        SrcLoc loc,
        QualType implicit_this_type) ;

    std::unique_ptr<Expr> try_member_function_overload_call(
        std::unique_ptr<FuncCall>& call,
        MemberCallSelection& member_call_selection,
        SrcLoc loc) ;

    std::unique_ptr<Expr> resolve_call_function_type(
        std::unique_ptr<FuncCall>& call,
        SrcLoc loc,
        CallFinalizationContext& context_out) ;

    void capture_call_target_metadata(
        FuncCall* call,
        CallFinalizationContext& context_out) const ;

    void note_specialization_use_for_symbol(
        const std::shared_ptr<Symbol>& symbol,
        SrcLoc loc) const ;

    void configure_call_parameter_counts(
        Expr* raw_member_pointer_callee,
        CallFinalizationContext& context_out,
        SrcLoc loc) const ;

    void validate_call_argument_count(
        size_t provided_arg_count,
        const CallFinalizationContext& context,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> prepare_call_finalization(
        std::unique_ptr<FuncCall>& call,
        SrcLoc loc,
        CallFinalizationContext& context_out) ;

    std::unique_ptr<Expr> append_missing_call_default_arguments(
        FuncCall* call,
        const CallFinalizationContext& context,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> convert_call_argument_to_parameter(
        std::unique_ptr<Expr> arg,
        QualType param_type,
        SrcLoc loc) ;

    bool is_transparent_union_call_argument_viable(
        Expr* arg,
        QualType param_type) const ;

    std::unique_ptr<Expr> apply_variadic_call_argument_conversions(
        std::unique_ptr<Expr> arg) const ;

    void convert_call_arguments(
        FuncCall* call,
        const CallFinalizationContext& context,
        SrcLoc loc) ;

    std::unique_ptr<Expr> wrap_member_call_expression(
        std::unique_ptr<FuncCall> call,
        const MemberCallSelection& member_call_selection,
        SrcLoc loc) const ;


    std::unique_ptr<Expr> maybe_wrap_immediate_invocation(
        std::unique_ptr<Expr> invocation,
        const std::shared_ptr<Symbol>& callee_symbol,
        SrcLoc loc) ;

    std::unique_ptr<Expr> append_member_overload_candidates(
        const ObjectType* record_type,
        std::string_view member_name,
        Expr* access_expr,
        OverloadImplicitObjectArgKind static_member_arg_kind,
        std::vector<OverloadCallCandidate>& candidates_out,
        bool& had_member_match_out,
        bool& saw_private_member_out,
        bool& saw_protected_member_out,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> append_member_template_overload_candidates(
        const ObjectType* record_type,
        std::string_view member_name,
        Expr* access_expr,
        bool access_expr_is_arrow,
        const std::vector<std::unique_ptr<Expr>>& explicit_args,
        std::vector<OverloadCallCandidate>& candidates_out,
        bool& had_member_match_out,
        bool& had_template_member_match_out,
        bool& saw_private_member_out,
        bool& saw_protected_member_out,
        bool& saw_template_instantiation_out,
        SrcLoc loc) ;

    void append_unqualified_overload_candidates(
        std::string_view function_name,
        OverloadImplicitObjectArgKind implicit_arg_kind,
        std::vector<OverloadCallCandidate>& candidates_out) ;

    void append_unqualified_function_template_overload_candidates(
        std::string_view function_name,
        Expr* implicit_object_arg,
        OverloadImplicitObjectArgKind implicit_arg_kind,
        const std::vector<std::unique_ptr<Expr>>& explicit_args,
        std::vector<OverloadCallCandidate>& candidates_out,
        SrcLoc loc) ;
    void append_unqualified_function_template_overload_candidates(
        std::string_view function_name,
        Expr* implicit_object_arg,
        OverloadImplicitObjectArgKind implicit_arg_kind,
        const std::vector<Expr*>& explicit_args,
        std::vector<OverloadCallCandidate>& candidates_out,
        SrcLoc loc) ;

    std::unique_ptr<Expr> select_overload_candidate(
        std::string_view callee_name,
        const std::vector<OverloadCallCandidate>& candidates,
        const std::vector<std::unique_ptr<Expr>>& explicit_args,
        Expr* implicit_object_arg,
        SrcLoc loc,
        std::shared_ptr<Symbol>& selected_symbol_out,
        OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) ;
    std::unique_ptr<Expr> select_overload_candidate(
        std::string_view callee_name,
        const std::vector<OverloadCallCandidate>& candidates,
        const std::vector<Expr*>& explicit_args,
        Expr* implicit_object_arg,
        SrcLoc loc,
        std::shared_ptr<Symbol>& selected_symbol_out,
        OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) ;

    std::unique_ptr<Expr> report_inaccessible_member(
        std::string_view member_name,
        bool saw_private_member,
        bool saw_protected_member,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> make_hidden_overload_callee(
        std::shared_ptr<Symbol> selected_symbol,
        SrcLoc loc) const ;

    std::unique_ptr<Expr> complete_selected_function_template_specialization_symbol(
        std::shared_ptr<Symbol>& selected_symbol,
        SrcLoc loc,
        std::string_view failure_message) ;

    std::unique_ptr<Expr> try_cpp_binary_operator_overload(
        std::unique_ptr<Expr>& lhs,
        std::unique_ptr<Expr>& rhs,
        BinOpTypes bop,
        SrcLoc loc) ;

    std::unique_ptr<Expr> resolve_overloaded_call_candidates(
        std::string_view callee_name,
        const std::vector<OverloadCallCandidate>& candidates,
        const std::vector<std::unique_ptr<Expr>>& explicit_args,
        Expr* implicit_object_arg,
        SrcLoc loc,
        std::shared_ptr<Symbol>& selected_symbol_out,
        OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) ;
    std::unique_ptr<Expr> resolve_overloaded_call_candidates(
        std::string_view callee_name,
        const std::vector<OverloadCallCandidate>& candidates,
        const std::vector<Expr*>& explicit_args,
        Expr* implicit_object_arg,
        SrcLoc loc,
        std::shared_ptr<Symbol>& selected_symbol_out,
        OverloadImplicitObjectArgKind& selected_implicit_object_arg_kind_out) ;

    ImplicitConversionSequence evaluate_overload_implicit_object_conversion(
        Expr* object_arg,
        QualType param_type,
        OverloadImplicitObjectArgKind implicit_object_arg_kind,
        FunctionRefQualifierKind ref_qualifier,
        OverloadConversionMemoCache* conversion_cache = nullptr) ;

    ImplicitConversionSequence build_cpp_overload_conversion_sequence_cached(
        Expr* arg,
        QualType to,
        bool allow_user_defined,
        OverloadConversionMemoCache* conversion_cache) ;

    OverloadCandidateEval evaluate_overload_call_candidate(
        const OverloadCallCandidate& candidate_info,
        const std::vector<std::unique_ptr<Expr>>& explicit_args,
        Expr* implicit_object_arg,
        OverloadConversionMemoCache* conversion_cache = nullptr) ;
    OverloadCandidateEval evaluate_overload_call_candidate(
        const OverloadCallCandidate& candidate_info,
        const std::vector<Expr*>& explicit_args,
        Expr* implicit_object_arg,
        OverloadConversionMemoCache* conversion_cache = nullptr) ;

    OverloadCandidateEval evaluate_conversion_constructor_candidate(
        const RecordSemanticState::Constructor& ctor,
        Expr* arg,
        QualType target_type,
        bool allow_explicit_constructors,
        OverloadConversionMemoCache* conversion_cache = nullptr) ;

    OverloadCandidateEval evaluate_conversion_function_candidate(
        const RecordSemanticState::Method& method,
        const ObjectDecl* owner_record_decl,
        Expr* arg,
        QualType target_type,
        bool allow_explicit_conversion_functions,
        OverloadConversionMemoCache* conversion_cache = nullptr) ;

    void collect_viable_overload_candidates(
        OverloadCandidateSet& candidate_set) const ;

    std::string overload_failure_reason(
        const OverloadFailure& failure) const ;

    std::string overload_candidate_type_name(
        const OverloadCandidateEval& candidate) const ;

    int overload_failure_category(const OverloadFailure& failure) const ;

    bool overload_note_order_less(
        const OverloadCandidateSet& candidate_set,
        size_t lhs_idx,
        size_t rhs_idx) const ;

    void emit_overload_candidate_notes(
        std::string_view callee_name,
        const OverloadCandidateSet& candidate_set,
        bool include_non_viable,
        SrcLoc loc) const ;

    bool is_better_overload_candidate(const OverloadCandidateEval& lhs,
                                              const OverloadCandidateEval& rhs) ;

    std::optional<size_t> select_best_overload_candidate_index(
        const OverloadCandidateSet& candidate_set) ;

    QualType pick_common_type(QualType lhs, QualType rhs) const ;

    // Materialize rollback state lazily on first semantic mutation in a
    // tentative parse context.
    void materialize_tentative_snapshot(TentativeSnapshot& snapshot) ;
    void materialize_tentative_snapshot_if_needed() ;
    void record_decl_context_mutation(const std::shared_ptr<DeclContext>& context) ;
    void record_scope_mutation(const std::shared_ptr<Scope>& scope) ;
    void record_global_scope_mutation(
        const std::shared_ptr<GlobalIdentTracker>& global_scope) ;
    std::shared_ptr<DeclContext> find_decl_context(const DeclContext* target) const ;
    std::shared_ptr<DeclContext> resolve_scope_decl_context(const std::shared_ptr<Scope>& scope) const ;
    std::shared_ptr<Scope> find_enclosing_scope_with_flags(ScopeFlags flags) const ;
    void bind_symbol_in_scope(const std::shared_ptr<Scope>& scope,
                                      const std::string& name,
                                      const std::shared_ptr<Symbol>& sym) ;
    void bind_template_decl_in_scope(const std::shared_ptr<Scope>& scope,
                                     const std::string& name,
                                     const Decl* decl,
                                     LookupNamespace lookup_namespace) ;
    void bind_tag_decl_in_scope(const std::shared_ptr<Scope>& scope,
                                        const std::string& tag,
                                        TagDecl* decl) ;
    void bind_label_in_scope(const std::shared_ptr<Scope>& scope,
                                     const std::string& label,
                                     SrcLoc loc) ;
    void sync_decl_context_from_current_scope() ;
    FunctionDefinitionState capture_current_function_definition_state() const ;
    void restore_current_function_definition_state(FunctionDefinitionState state) ;
    void reset_current_function_definition_state() ;

    // --- Context (immutable) ---
    std::shared_ptr<ASTContext> ast_ctx_;
    CollectQueryContext query_context_;
    CollectQueryContext* previous_active_query_context_ = nullptr;
    ASTContextSideTableScope side_table_scope_;
    std::shared_ptr<SourceManager> sm_;
    std::shared_ptr<DiagnosticEngine> diag_engine_;
    LangOptions lang_opts_;

    struct CollectSessionState {
        std::shared_ptr<Scope> current_scope_ = nullptr;
        std::shared_ptr<DeclContext> translation_unit_decl_context_ = nullptr;
        std::shared_ptr<DeclContext> current_decl_context_ = nullptr;
        std::shared_ptr<GlobalIdentTracker> current_global_scope_ = nullptr;
        FunctionDefinitionState func_state_;
        QualType current_cpp_record_lookup_type_ = nullptr;
        std::vector<TentativeSnapshot> tentative_snapshots_;
        std::vector<FunctionDefinitionState> function_definition_stack_;
        std::vector<std::vector<TentativeSnapshot>>
            function_tentative_snapshot_stack_;
    };

    CollectSessionState session_;
};

#endif // ABURI_COLLECT_H
