#ifndef ABURI_AST2LLVM_H
#define ABURI_AST2LLVM_H

#include "../ast/ast.h"
#include "../ast/types.h"
#include "../abi/target_info.h"
#include "../ast/ast_context.h"
#include "../lang_options.h"
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/DIBuilder.h>
#include <llvm/Support/CodeGen.h>
#include <memory>
#include <map>
#include <set>
#include <unordered_map>

// Result of get_lvalue(): the address of a value and its semantic type.
// At address `address` we will find a value of type `type`.
struct LValueResult {
    llvm::Value* address = nullptr;
    std::shared_ptr<CType> type = nullptr;

    explicit operator bool() const { return address != nullptr; }
};

class ASTToLLVM {
public:
    enum class CppCtorDtorVariant {
        Complete,
        Base,
        Deleting,
    };

    ASTToLLVM();
    void dump();
    int run();
    std::string optimization_level = "0";
    void optimize();
    void emit(std::string filename, llvm::CodeGenFileType file_type);
    
    bool emit_debug_info = false;
    std::unique_ptr<llvm::DIBuilder> di_builder;
    llvm::DICompileUnit* di_cu = nullptr;

    void create_debug_info_for_function(FuncDecl* decl, llvm::Function* func);
    void emit_debug_location(Stmt* stmt);
    llvm::DIType* convert_debug_type(std::shared_ptr<CType> type);

    void convert_return_statement(Stmt *stmt);

    void convert_empty_stmt(EmptyStmt *stmt);

    void convert_statement(Stmt *stmt);
    void convert_statement_after_terminator(Stmt *stmt, bool allow_case_labels);

    void convert_compound_statement(Stmt *stmt,
                                    bool preserve_scope_cleanup_entries = false);

    void convert_function_declaration(Decl *decl);
    void emit_function_body(FuncDecl *node,
                            llvm::Function *mainFunc,
                            SrcLoc loc,
                            CppCtorDtorVariant special_member_variant =
                                CppCtorDtorVariant::Complete);
    void emit_cpp_lambda_invoker_body(FuncDecl* node,
                                      llvm::Function* mainFunc,
                                      SrcLoc loc,
                                      const CppLambdaInvokerInfo& invoker_info);
    void emit_deferred_inline_definitions();

    void convert_declaration(Decl *decl);

    void convert_translation_unit(Decl *decl);

    std::unique_ptr<llvm::LLVMContext> context;
    std::unique_ptr<llvm::Module> module;
    llvm::IRBuilder<> builder;
    std::map<std::string, llvm::Value*> named_values;
    std::set<std::string> is_global_defined;
    std::vector<FuncDecl*> deferred_inline_defs;
    std::set<const FuncDecl*> deferred_inline_set;
    llvm::AllocaInst* last_entry_alloca = nullptr;
    std::unordered_map<const Expr*, llvm::Value*> vla_size_cache;
    // Decl-identity keyed cache for lowered record LLVM types.
    // Key is RecordDecl* when available; falls back to ObjectType* for anonymous/unbound records.
    std::unordered_map<const void*, llvm::StructType*> struct_type_cache;
    std::unordered_map<const ObjectDecl*, llvm::GlobalVariable*> cpp_vtable_cache;
    std::unordered_map<std::string, llvm::GlobalVariable*> cpp_vtable_group_cache;
    std::unordered_map<std::string, llvm::GlobalVariable*> cpp_construction_vtable_cache;
    std::unordered_map<const ObjectDecl*, llvm::GlobalVariable*> cpp_vtt_cache;
    std::unordered_map<std::string, llvm::Function*> cpp_nonvirtual_thunk_cache;
    std::unordered_map<std::string, llvm::Function*> cpp_virtual_thunk_cache;
    // For structs with bitfields: C field index -> LLVM field index mapping
    std::unordered_map<const void*, std::vector<int>> bitfield_field_index_map;
    std::shared_ptr<Scope> current_scope;
    std::shared_ptr<ASTContext> ast_ctx;
    std::shared_ptr<TypeContext> type_ctx = nullptr;
    std::shared_ptr<TargetInfo> target = nullptr;
    std::shared_ptr<SourceManager> sm = nullptr;
    LangOptions lang_opts;

    // for loop

    llvm::BasicBlock * endloop = nullptr; // end of current loop
    llvm::BasicBlock * condloop = nullptr; // condition block of current loop

    // for switch
    llvm::SwitchInst * switch_inst = nullptr;
    llvm::BasicBlock * switch_end = nullptr;
    llvm::BasicBlock * switch_default = nullptr;

    // for goto
    std::map<std::string, llvm::BasicBlock*> label_blocks;
    std::unordered_map<std::string, size_t> label_cleanup_depths;
    std::unordered_map<std::string, uint32_t> label_offsets;
    std::unordered_map<std::string, std::vector<size_t>> label_cleanup_counts;
    std::vector<std::pair<std::string, llvm::Instruction*>> unresolved_gotos;
    bool materializing_dead_jump_targets = false;

    // cleanup attribute support
    struct CleanupEntry {
        enum class Kind {
            Call,
            CallNoArgs,
            CppDestructor,
            BlockByrefDispose,
            StackRestore,
        };
        llvm::Value* var_addr;
        std::string cleanup_func;
        std::shared_ptr<Symbol> cxx_destructor_sym;
        QualType cxx_destructor_object_type;
        SrcLoc location;
        Kind kind = Kind::Call;
    };
    std::vector<std::vector<CleanupEntry>> cleanup_stack;
    size_t break_cleanup_depth = 0;
    size_t continue_cleanup_depth = 0;
    struct EhRegionFrame {
        llvm::BasicBlock* landing_pad_block = nullptr;
        size_t cleanup_depth_snapshot = 0;
    };
    std::vector<EhRegionFrame> eh_region_stack;
    bool enforce_noexcept_terminate_on_escape = false;

    void emit_cleanup_entry(const CleanupEntry& entry);
    void emit_cleanups_for_scope();
    void emit_all_cleanups();
    void emit_cleanups_to_depth(size_t target_depth);
    void collect_label_cleanup_depths(Stmt* stmt, size_t depth);
    void emit_cleanup_cpp_destructor(const CleanupEntry& entry,
                                     const std::string& context);
    llvm::Function* get_or_create_eh_personality();
    llvm::Function* get_or_create_cxa_allocate_exception();
    llvm::Function* get_or_create_cxa_throw();
    llvm::Function* get_or_create_cxa_rethrow();
    llvm::Function* get_or_create_cxx_dynamic_cast();
    llvm::Function* get_or_create_cxa_bad_cast();
    llvm::Function* get_or_create_cxa_bad_typeid();
    llvm::Function* get_or_create_cxa_begin_catch();
    llvm::Function* get_or_create_cxa_end_catch();
    llvm::Function* get_or_create_cxx_terminate();
    llvm::Function* get_or_create_unwind_resume();
    llvm::Function* get_or_create_block_object_assign();
    llvm::Function* get_or_create_block_object_dispose();
    bool block_byref_requires_copy_dispose_helpers(QualType value_type) const;
    uint32_t block_object_field_flags_for_type(QualType value_type,
                                               bool byref_caller) const;
    llvm::Value* get_block_byref_cell_address(const Symbol* sym,
                                              SrcLoc loc,
                                              const char* context_name);
    llvm::Value* get_block_byref_forwarding_cell(llvm::Value* cell_addr,
                                                 SrcLoc loc,
                                                 const char* context_name);
    llvm::Value* get_block_byref_payload_address(llvm::Value* cell_addr,
                                                 QualType value_type,
                                                 SrcLoc loc,
                                                 const char* context_name);
    bool should_emit_invoke_for_callee(llvm::Value* callee,
                                       const FunctionType* callee_type = nullptr) const;
    std::string get_itanium_type_name_encoding(QualType type) const;
    std::string get_itanium_typeinfo_symbol(QualType type) const;
    llvm::GlobalVariable* get_or_create_itanium_typeinfo_global(QualType type);
    llvm::GlobalVariable* get_or_create_itanium_class_typeinfo_global(
        const ObjectDecl* record_decl);

    void error(std::string err, SrcLoc loc = SrcLoc()) const {
        SrcLoc curr_loc = loc;
        if (curr_loc.isInvalid() || sm == nullptr) {
            throw std::runtime_error("error in codegen/ast2llvm: " + err);
        }
        throw std::runtime_error(sm->formatDiagnostic(DiagnosticLevel::Error, err, curr_loc));
    }
    static void info(std::string info) {
      //  std::cout << info << std::endl;
    }
    static std::string mangleCIdentifier(const std::string& original);
    // Get the LLVM IR name for an asm label. Prepends \01 to prevent LLVM from
    // adding the Mach-O underscore prefix, since asm labels are exact symbol names.
    static std::string get_asm_label_name(const std::string& label);
    std::shared_ptr<Symbol> get_function_symbol_for_decl(const FuncDecl& decl) const;
    bool is_cxx_default_constructor_symbol(
        const std::shared_ptr<Symbol>& sym) const;
    std::string get_function_llvm_name(const FuncDecl& decl) const;
    std::string get_function_llvm_name(const std::shared_ptr<Symbol>& sym,
                                       const std::string& fallback_spelling = "") const;
    llvm::GlobalValue::LinkageTypes get_function_definition_linkage(
        const FuncDecl& decl,
        bool suppress_external_definition) const;
    llvm::GlobalValue::LinkageTypes get_function_declaration_linkage(
        const FuncDecl& decl,
        bool suppress_external_definition) const;
    llvm::GlobalValue::LinkageTypes get_function_symbol_linkage(
        const Symbol& sym) const;
    void apply_global_visibility(llvm::GlobalValue& global,
                                 const std::string& visibility) const;
    void configure_odr_function_linkage(llvm::Function* function) const;
    std::string get_variable_linkage_identity(const VariableDecl& decl) const;
    std::string get_variable_llvm_name(const VariableDecl& decl) const;
    std::string get_variable_llvm_name(const std::shared_ptr<Symbol>& sym,
                                       const std::string& fallback_spelling = "") const;
    llvm::Function* get_or_create_function_symbol(
        const std::shared_ptr<Symbol>& sym,
        const std::string& fallback_spelling = "");
    /**
     * Mangler for C identifiers to LLVM IR compatible names.
     * Prepends a 'C.' prefix and hex-escapes non-alphanumeric characters.
     */
    llvm::Value* convert_integer_literal(Expr * expr);
    llvm::Value* convert_floating_literal(Expr * expr);
    llvm::Value* convert_character_literal(Expr * expr);
    llvm::Constant* build_string_literal_array_constant(const StringLiteral* str_lit, size_t len);
    llvm::Value* convert_string_literal(Expr * expr);
    llvm::Value* convert_unary_expr(Expr * expr);

    llvm::Value *convert_logical_or_expr(BinaryOperation *expr);

    llvm::Value *convert_logical_and_expr(BinaryOperation *expr);

    LValueResult get_lvalue(Expr *expr);

    llvm::Value *convert_binary_expr(Expr *expr);
    llvm::Value* convert_cpp_builtin_three_way_compare_expr(
        CppBuiltinThreeWayCompareExpr* expr);

    llvm::Value* convert_expression(Expr * expr);
    llvm::Value* convert_init_list_rvalue_expression(InitListExpr* init_list,
                                                     SrcLoc expr_loc);
    llvm::Value* convert_cpp_construct_temporary_expression(
        CppConstructExpr* ctor_expr,
        SrcLoc expr_loc);

    void convert_variable_declaration(VariableDecl *varDecl);
    bool emit_cpp_construct_call(const CppConstructExpr* ctor_init,
                                 llvm::Value* object_addr,
                                 SrcLoc loc,
                                 const std::string& context,
                                 CppCtorDtorVariant variant =
                                     CppCtorDtorVariant::Complete);
    bool emit_cpp_construct_call(const std::shared_ptr<Symbol>& ctor_sym,
                                 const std::vector<std::unique_ptr<Expr>>& ctor_args,
                                 llvm::Value* object_addr,
                                 SrcLoc loc,
                                 const std::string& context,
                                 CppCtorDtorVariant variant =
                                     CppCtorDtorVariant::Complete);
    bool emit_cpp_destruct_call(const std::shared_ptr<Symbol>& dtor_sym,
                                llvm::Value* object_addr,
                                SrcLoc loc,
                                const std::string& context,
                                CppCtorDtorVariant variant =
                                    CppCtorDtorVariant::Complete);
    llvm::Value* emit_cpp_operator_call(
        const std::shared_ptr<Symbol>& callee_sym,
        const std::vector<std::pair<llvm::Value*, QualType>>& args,
        SrcLoc loc,
        const std::string& context);
    std::shared_ptr<Symbol> select_record_default_constructor_symbol(
        const RecordSemanticState* state,
        bool require_public_access) const;
    std::shared_ptr<Symbol> select_record_destructor_symbol(
        const RecordSemanticState* state,
        bool require_public_access) const;
    bool emit_cpp_object_default_construction_recursive(
        const QualType& object_type,
        llvm::Value* object_addr,
        SrcLoc loc,
        const std::string& construction_context,
        CppCtorDtorVariant ctor_variant =
            CppCtorDtorVariant::Complete,
        const ObjectDecl* construction_complete_decl = nullptr);
    void emit_cpp_object_teardown_recursive(const QualType& object_type,
                                            llvm::Value* object_addr,
                                            std::shared_ptr<Symbol> object_dtor_sym,
                                            SrcLoc loc,
                                            const std::string& teardown_context,
                                            CppCtorDtorVariant dtor_variant =
                                                CppCtorDtorVariant::Complete);
    void emit_cpp_global_object_ctor_thunk(const std::string& thunk_name,
                                           const CppConstructExpr* ctor_init,
                                           llvm::Value* object_addr,
                                           SrcLoc loc,
                                           const std::string& construction_context,
                                           llvm::GlobalValue::LinkageTypes thunk_linkage =
                                               llvm::GlobalValue::InternalLinkage,
                                           llvm::Constant* comdat_association = nullptr);
    void emit_cpp_global_object_dtor_thunk(const std::string& thunk_name,
                                           const QualType& object_type,
                                           llvm::Value* object_addr,
                                           std::shared_ptr<Symbol> selected_dtor_sym,
                                           SrcLoc loc,
                                           const std::string& teardown_context,
                                           llvm::GlobalValue::LinkageTypes thunk_linkage =
                                               llvm::GlobalValue::InternalLinkage,
                                           llvm::Constant* comdat_association = nullptr);
    const ObjectDecl* canonical_cpp_record_decl(const ObjectDecl* decl) const;
    const RecordSemanticState* lookup_cpp_record_state(const ObjectDecl* decl) const;
    std::string get_cpp_special_member_variant_llvm_name(
        const std::string& complete_name,
        bool is_destructor,
        CppCtorDtorVariant variant) const;
    std::string get_cpp_special_member_variant_llvm_name(
        const std::shared_ptr<Symbol>& sym,
        bool is_destructor,
        CppCtorDtorVariant variant) const;
    size_t cpp_vtable_emitted_slot_count(
        const RecordSemanticState* context_state) const;
    size_t cpp_vtable_physical_slot_index(
        const RecordSemanticState* context_state,
        size_t semantic_slot_index,
        bool use_deleting_destructor_entry = false) const;
    std::shared_ptr<Symbol> select_record_deallocation_symbol(
        const RecordSemanticState* state,
        bool is_array_form) const;
    llvm::Function* get_or_create_cpp_deleting_destructor_function(
        const std::shared_ptr<Symbol>& dtor_sym,
        SrcLoc loc,
        const std::string& context_name);
    bool cpp_record_uses_vptr(const RecordSemanticState* state) const;
    bool using_itanium_cxx_object_abi() const;
    bool ensure_supported_cpp_vtable_abi(SrcLoc loc,
                                         const std::string& context_name) const;
    size_t cpp_vtable_header_entries_for_context(
        const RecordSemanticState* context_state) const;
    size_t cpp_vtable_address_point_index(
        const RecordSemanticState* context_state) const;
    int64_t cpp_vtable_virtual_base_relative_index(
        const RecordSemanticState* context_state,
        size_t virtual_base_index) const;
    std::optional<size_t> find_cpp_base_subobject_offset(
        const ObjectDecl* derived_decl,
        const ObjectDecl* base_decl) const;
    llvm::Value* adjust_cpp_pointer_by_static_offset(
        llvm::Value* ptr_value,
        int64_t byte_offset,
        const std::string& name_prefix = "cpp.subobject.adjust");
    llvm::Value* recover_cpp_complete_object_address(
        llvm::Value* subobject_ptr,
        const ObjectDecl* subobject_record_decl,
        SrcLoc loc,
        const std::string& context_name,
        const ObjectDecl* active_vptr_context_decl = nullptr);
    llvm::Value* resolve_cpp_virtual_base_subobject_address(
        llvm::Value* context_ptr,
        const ObjectDecl* context_record_decl,
        const ObjectDecl* target_virtual_base_decl,
        SrcLoc loc,
        const std::string& context_name,
        const ObjectDecl* active_vptr_context_decl = nullptr);
    std::string make_cpp_vtable_group_key(const ObjectDecl* record_decl,
                                          const ObjectDecl* context_record_decl) const;
    std::optional<size_t> get_cpp_vtt_entry_index(
        const ObjectDecl* record_decl,
        const ObjectDecl* context_record_decl) const;
    llvm::GlobalVariable* get_or_create_cpp_vtable(
        const ObjectDecl* record_decl,
        const ObjectDecl* context_record_decl = nullptr);
    llvm::GlobalVariable* get_or_create_cpp_construction_vtable(
        const ObjectDecl* record_decl,
        const ObjectDecl* context_record_decl);
    llvm::GlobalVariable* get_or_create_cpp_vtt(const ObjectDecl* record_decl);
    bool emit_cpp_construction_vptr_store_from_vtt(
        const ObjectDecl* record_decl,
        const ObjectDecl* context_record_decl,
        llvm::Value* object_addr,
        SrcLoc loc,
        const std::string& context_name);
    llvm::GlobalVariable* get_or_create_cpp_vtable_for_object_type(
        const QualType& object_type);
    bool emit_cpp_vptr_store(const QualType& object_type,
                             llvm::Value* object_addr,
                             SrcLoc loc,
                             const std::string& context);

    llvm::Value* convert_var_ref(VarRef *expr);
    llvm::Value* convert_label_address_expr(LabelAddressExpr *expr);
    llvm::Value* materialize_reference_rvalue(Expr* expr,
                                              llvm::Value* lowered_value,
                                              const char* context_name);
    void reset_entry_alloca_insertion_state();
    llvm::AllocaInst* create_entry_alloca(llvm::Function* function,
                                          llvm::Type* alloc_type,
                                          llvm::Value* array_size,
                                          const std::string& name);

    void deal_global_variable_declaration(Decl *decl);

    void convert_if_statement(IfStmt *stmt);

    llvm::Value* convert_conditional_expr(CondExpr *expr);

    // Convert any value (int, float, pointer, complex) to i1 boolean
    llvm::Value* emit_bool_conversion(llvm::Value* val, const std::string& name = "tobool");

    llvm::Value* convert_assign_expr(BinaryOperation *expr);

    llvm::Value *convert_compound_assignment(Expr *expr);

    void convert_while_statement(WhileStmt *stmt);

    void convert_do_while_statement(DoWhileStmt *stmt);

    void convert_for_statement(ForStmt *stmt);

    void convert_cpp_range_for_statement(CppRangeForStmt *stmt);

    void convert_continue_statement(Stmt *stmt);

    void convert_break_statement(Stmt *stmt);

    void convert_switch_statement(SwitchStmt *stmt);
    void convert_case_statement(CaseStmt *stmt);
    void convert_default_statement(DefaultStmt *stmt);
    void convert_cpp_try_statement(CppTryStmt *stmt);

    void convert_labeled_statement(LabeledStmt *stmt);

    void convert_goto_statement(GoToStmt *stmt);
    void convert_computed_goto_statement(ComputedGotoStmt *stmt);

    llvm::Value* convert_function_call(FuncCall *expr);
    llvm::Value* convert_cpp_member_call(CppMemberCallExpr *expr);

    llvm::Type* convert_type(std::shared_ptr<CType> ctype);
    llvm::Type* convert_type(const QualType& qt) { return convert_type(qt.get_shared()); }
    bool pass_aggregate_by_reference(const QualType& param) const;
    llvm::Type* get_direct_aggregate_parameter_abi_type(
        const QualType& param) const;
    bool has_direct_aggregate_parameter_abi(const QualType& param) const;
    bool return_aggregate_indirectly(const QualType& ret) const;
    llvm::Type* convert_function_return_type(const QualType& ret);
    unsigned prepend_indirect_result_parameter(std::vector<llvm::Type*>& param_types,
                                               const QualType& ret);
    void apply_indirect_result_attributes(llvm::Function* fn,
                                          unsigned arg_index,
                                          const QualType& ret);
    void apply_indirect_result_attributes(llvm::CallBase* call,
                                          unsigned arg_index,
                                          const QualType& ret);
    llvm::AllocaInst* create_indirect_result_slot(llvm::Function* function,
                                                  const QualType& ret,
                                                  const char* name);
    llvm::Value* load_aggregate_memory_as_abi_value(llvm::Value* src_addr,
                                                    const QualType& aggregate_type,
                                                    llvm::Type* abi_type,
                                                    SrcLoc loc,
                                                    const char* context_name);
    void store_abi_value_into_aggregate_memory(llvm::Value* abi_value,
                                               llvm::Value* dest_addr,
                                               const QualType& aggregate_type,
                                               SrcLoc loc,
                                               const char* context_name);
    // Converts a function parameter type, decaying arrays to pointers (C standard)
    llvm::Type* convert_param_type(const QualType& param);
    llvm::Value* convert_implicit_cast(ImplicitCast *expr);
    llvm::Value* lower_lvalue_to_rvalue(ImplicitCast *expr);
    llvm::Value* lower_complex_cast(ImplicitCast *expr);
    llvm::Value* emit_member_pointer_dispatch(FuncCall *expr,
                                              MemberPointerAccessExpr *member_ptr_callee);

    llvm::Value* convert_cpp_value_init_expr(CppValueInitExpr* expr);
    llvm::Value *convert_explicit_cast(ExplicitCast *expr);

    llvm::Value* cast_llvm_type(llvm::Value* val, llvm::Type* destType, bool isUnsigned);

    llvm::Constant* convert_init_list(InitListExpr* initList, llvm::Type* type);
    void serialize_constant_to_bytes(llvm::Constant* c, std::vector<uint8_t>& bytes,
                                     size_t offset, size_t bufSize);
    void emit_init_list_store(InitListExpr* initList, llvm::Value* base_ptr, std::shared_ptr<CType> type,
                              bool is_volatile = false, bool is_atomic = false);

    llvm::Value* convert_member_expr(MemberExpr *expr);
    llvm::Value* convert_member_pointer_literal_expr(MemberPointerLiteralExpr* expr);
    llvm::Value* convert_member_pointer_access_expr(MemberPointerAccessExpr* expr);
    llvm::Value* convert_sizeof_expr(SizeOfExpr *expr);
    llvm::Value* convert_alignof_expr(AlignOfExpr *expr);
    llvm::Value* convert_offsetof_expr(OffsetOfExpr *expr);
    llvm::Value* convert_compound_literal(CompoundLiteralExpr *expr);
    llvm::Value* convert_stmt_expr(StmtExpr *expr);
    llvm::Value* emit_vla_size_value(const std::shared_ptr<Expr>& expr, bool cache);
    llvm::Value* emit_type_size_bytes(std::shared_ptr<CType> type, bool use_cache);
    void cache_vla_sizes_for_type(std::shared_ptr<CType> type);
    std::pair<llvm::Type*, llvm::Value*> get_vla_flat_element_and_count(std::shared_ptr<ArrayType> arr_type);

    // Builtin call support
    llvm::Value* convert_builtin_call_expr(BuiltinCallExpr *expr);
    llvm::Value* convert_cpp_typeid_expression(CppTypeIdExpr *expr);
    llvm::Value* convert_cpp_dynamic_cast_expression(CppDynamicCastExpr *expr);
    llvm::Value* convert_cpp_throw_expression(CppThrowExpr *expr);
    llvm::Value* convert_cpp_new_expression(CppNewExpr *expr);
    llvm::Value* convert_cpp_delete_expression(CppDeleteExpr *expr);
    llvm::Value* convert_block_expression(BlockExpr *expr);

    // Variadic function support
    llvm::Value* convert_va_arg_expr(VaArgExpr *expr);
    llvm::Value* convert_va_start_expr(VaStartExpr *expr);
    llvm::Value* convert_va_end_expr(VaEndExpr *expr);
    llvm::Value* convert_va_copy_expr(VaCopyExpr *expr);

    // Inline assembly support
    void convert_asm_statement(AsmStmt *stmt);
    void convert_file_scope_asm(FileScopeAsmDecl *decl);

    // Constant expression evaluation for global initializers
    llvm::Constant* emit_constant_initializer(Expr* expr);

    // Bitfield support
    llvm::Value* extract_bitfield(llvm::Value* storage_unit_ptr, uint32_t storage_size,
                                  uint32_t bit_offset, uint32_t bit_width, bool is_signed);
    llvm::Value* get_bitfield_storage_ptr(MemberExpr* member, llvm::Value* base_ptr, const BitfieldInfo* bf);
    void store_bitfield(llvm::Value* storage_ptr, uint32_t storage_size,
                        uint32_t bit_offset, uint32_t bit_width, llvm::Value* value);
};

#endif //ABURI_AST2LLVM_H
