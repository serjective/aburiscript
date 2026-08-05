#ifndef ABURI_CIR2LLVM_LOWERER_H
#define ABURI_CIR2LLVM_LOWERER_H

#include "cir2llvm.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include <llvm/ADT/StringRef.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

namespace aburi::abi {
struct AggregateClass;
} // namespace aburi::abi

namespace aburi::cir2llvm {

template <typename IdT>
uint64_t id_key(IdT id) {
    return (static_cast<uint64_t>(id.generation) << 32) | id.index;
}

class Lowerer {
public:
    Lowerer(const cir::File& file, LoweringOptions options);

    LoweringResult run();

    // Symbol name for an entity: Itanium-mangled in C++ mode (except
    // extern "C" and other raw-name cases), otherwise the source name.
    std::string linkage_name(cir::EntityId entity_id) const;
    void emit_structor_aliases();
    void merge_expression_blocks();
    void replace_aggregate_copies();

private:
    enum class AbiArgKind {
        Direct,
        Indirect
    };

    struct AbiArgInfo {
        AbiArgKind kind = AbiArgKind::Direct;
        cir::TypeRef source_type{};
        llvm::Type* abi_type = nullptr;
        bool is_aggregate = false;
        bool is_direct_aggregate = false;
        bool is_ignored = false;
        bool is_sret = false;
        bool is_byval = false;
    };

    struct FunctionAbiInfo {
        cir::TypeId source_function_type{};
        cir::TypeRef return_type{};
        AbiArgInfo result;
        std::vector<AbiArgInfo> params;
        llvm::FunctionType* llvm_type = nullptr;
        bool is_variadic = false;
        bool has_prototype = true;
    };

    llvm::LLVMContext& context();
    llvm::Module& module();
    llvm::IRBuilder<>& builder();

    void error(std::string message, SrcLoc loc = SrcLoc());
    bool has_errors() const;
    bool definition_required(const cir::Entity& entity) const;
    uint64_t pointer_bytes() const;
    uint64_t pointer_bits() const;

    void preflight();
    void check_entity(cir::EntityId entity_id);
    void check_function(cir::FunctionId function_id);
    bool check_type_ref(cir::TypeRef ref, SrcLoc loc, const std::string& context_text);
    bool check_type(cir::TypeId type_id, SrcLoc loc, const std::string& context_text);
    void check_inst(cir::InstId inst_id);

    void declare_entities();
    llvm::Function* get_or_declare_function(cir::EntityId entity_id);
    llvm::GlobalValue* function_symbol(cir::EntityId entity_id);
    llvm::GlobalValue* resolve_weakref_target(const std::string& target_name,
                                              cir::EntityId self,
                                              SrcLoc loc);
    llvm::GlobalValue* get_or_create_global(cir::EntityId entity_id);
    llvm::Constant* constant_from_static_bytes(cir::TypeId type_id,
                                               const std::vector<uint8_t>& bytes,
                                               SrcLoc loc,
                                               const std::vector<cir::StaticInitializerRelocation>& relocations = {});
    llvm::BlockAddress* block_address_constant(cir::EntityId entity_id,
                                               cir::BlockId block,
                                               SrcLoc loc);

    void lower_function(cir::FunctionId function_id);
    llvm::AllocaInst* create_entry_alloca(llvm::Type* type, std::string_view name);
    llvm::Value* value_for(cir::ValueRef value, SrcLoc loc);
    llvm::Value* value_for(cir::InstId inst_id, SrcLoc loc);
    llvm::Value* storage_for_place(cir::InstId place, SrcLoc loc);
    llvm::Value* storage_for_entity(cir::EntityId entity, SrcLoc loc);
    void remember(cir::InstId inst_id, llvm::Value* value);
    void lower_inst(cir::InstId inst_id);
    llvm::Value* lower_field_addr(const cir::Inst& inst,
                                  const std::vector<cir::Operand>& operands,
                                  const std::vector<cir::ValueRef>& values);
    llvm::Value* lower_data_member_pointer_place(
        const cir::Inst& inst,
        const std::vector<cir::ValueRef>& values);
    llvm::Value* lower_member_function_pointer_callee(
        const cir::Inst& inst,
        const std::vector<cir::ValueRef>& values);
    llvm::Value* lower_member_function_pointer_this(
        const cir::Inst& inst,
        const std::vector<cir::ValueRef>& values);
    llvm::Value* runtime_type_size(cir::TypeId type, SrcLoc loc);
    llvm::Value* lower_array_element_place(const cir::Inst& inst,
                                           const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_vector_extract(cir::ValueRef vector,
                                      cir::ValueRef index,
                                      SrcLoc loc);
    llvm::Value* lower_vector_element_load(cir::InstId place_inst, SrcLoc loc);
    void lower_vector_element_store(cir::InstId place_inst, llvm::Value* value, SrcLoc loc);
    const char* named_register_for_place(cir::ValueRef place);
    llvm::Value* lower_named_register_read(const char* reg, llvm::Type* type, SrcLoc loc);
    void lower_named_register_write(const char* reg, llvm::Value* value, SrcLoc loc);
    llvm::Value* lower_bitfield_load(cir::InstId place_inst, const cir::RecordFieldFact& field, SrcLoc loc);
    void lower_bitfield_store(cir::InstId place_inst,
                              llvm::Value* value,
                              const cir::RecordFieldFact& field,
                              SrcLoc loc);
    llvm::Value* lower_unary(const cir::Inst& inst,
                             const cir::UnaryOpDescriptor& descriptor,
                             const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_binary(const cir::Inst& inst,
                              const cir::BinaryOpDescriptor& descriptor,
                              const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_builtin_call(const cir::Inst& inst,
                                    const cir::BuiltinCallPayload& payload,
                                    const std::vector<cir::ValueRef>& operands);
    void lower_inline_asm(const cir::InlineAsmPayload& payload,
                          const std::vector<cir::ValueRef>& operands,
                          llvm::BasicBlock* fallthrough,
                          const std::vector<llvm::BasicBlock*>& indirect_dests,
                          SrcLoc loc);
    void lower_construct_in_place(const cir::Inst& inst,
                                  const std::vector<cir::Operand>& operands);
    void lower_destroy(const cir::Inst& inst,
                       const std::vector<cir::Operand>& operands);
    llvm::Value* lower_call(const cir::Inst& inst,
                            const std::vector<cir::Operand>& operands);
    void lower_terminator(const cir::Terminator& terminator);
    bool function_uses_eh(const cir::Function& function) const;
    void apply_eh_function_setup(llvm::Function* function,
                                 bool non_throwing_type);
    llvm::FunctionCallee eh_runtime_callee(std::string_view name,
                                           llvm::FunctionType* type,
                                           bool is_noreturn = false,
                                           bool is_nounwind = false);
    llvm::BasicBlock* llvm_block_for(cir::BlockId block, SrcLoc loc);
    llvm::CallBase* emit_call_or_invoke(llvm::FunctionType* fn_type,
                                        llvm::Value* callee,
                                        llvm::ArrayRef<llvm::Value*> args,
                                        bool can_throw,
                                        const llvm::Twine& name,
                                        SrcLoc loc);
    llvm::Value* lower_eh_alloc_exception(const cir::Inst& inst);
    llvm::Value* lower_eh_landing_pad(cir::InstId inst_id,
                                      const cir::Inst& inst);
    llvm::Value* lower_eh_selector(const cir::Inst& inst,
                                   const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_eh_typeid_for(const cir::Inst& inst,
                                     const std::vector<cir::Operand>& operands);
    llvm::Value* lower_catch_begin(const cir::Inst& inst,
                                   const std::vector<cir::ValueRef>& operands);
    void lower_catch_end(const cir::Inst& inst);
    void lower_throw_terminator(const cir::Terminator& terminator);
    void lower_resume_terminator(const cir::Terminator& terminator);

    FunctionAbiInfo classify_function_abi(cir::TypeId function_type);
    AbiArgInfo classify_result_abi(cir::TypeRef type);
    AbiArgInfo classify_param_abi(cir::TypeRef type);
    AbiArgInfo classify_vararg_abi(cir::TypeRef type);
    llvm::Type* direct_aggregate_llvm_type(const abi::AggregateClass& cls,
                                           cir::TypeRef source_type);
    llvm::Value* materialize_abi_value_to_source(llvm::Value* abi_value,
                                                 cir::TypeRef source_type,
                                                 SrcLoc loc,
                                                 llvm::StringRef name);
    llvm::Value* materialize_indirect_abi_value_to_source(llvm::Value* pointer,
                                                          cir::TypeRef source_type,
                                                          SrcLoc loc,
                                                          llvm::StringRef name);
    llvm::Value* materialize_source_value_to_abi(llvm::Value* source_value,
                                                 cir::TypeRef source_type,
                                                 llvm::Type* abi_type,
                                                 SrcLoc loc,
                                                 llvm::StringRef name);
    llvm::Value* materialize_source_value_to_indirect_abi(llvm::Value* source_value,
                                                          cir::TypeRef source_type,
                                                          SrcLoc loc,
                                                          llvm::StringRef name);
    void apply_function_abi_attributes(llvm::Function* function,
                                       const FunctionAbiInfo& abi);
    void apply_call_abi_attributes(llvm::CallBase* call,
                                   const FunctionAbiInfo& abi);
    llvm::Value* lower_va_start(const cir::Inst& inst,
                                const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_va_arg(const cir::Inst& inst,
                              const std::vector<cir::Operand>& operands);
    llvm::Value* lower_va_arg_aapcs64(cir::TypeId value_type,
                                      llvm::Value* va_list_ptr,
                                      llvm::Type* arg_type);
    llvm::Value* lower_va_end(const cir::Inst& inst,
                              const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_va_copy(const cir::Inst& inst,
                               const std::vector<cir::ValueRef>& operands);
    llvm::Value* lower_complex_binary(const cir::Inst& inst,
                                      const cir::BinaryOpDescriptor& descriptor,
                                      llvm::Value* lhs,
                                      llvm::Value* rhs);
    llvm::AtomicOrdering atomic_ordering(cir::MemoryOrder order,
                                         bool is_store,
                                         bool is_load);
    llvm::Align atomic_alignment(cir::TypeId type);
    llvm::Value* truth_value(llvm::Value* value, SrcLoc loc);
    llvm::Value* cast_value(llvm::Value* value,
                            llvm::Type* target_type,
                            SrcLoc loc,
                            llvm::StringRef name);
    llvm::Value* cast_value(llvm::Value* value,
                            cir::TypeId source_type,
                            cir::TypeId target_type,
                            SrcLoc loc,
                            llvm::StringRef name);

    llvm::ConstantInt* constant_usize(uint64_t value);
    llvm::Type* llvm_type(cir::TypeRef ref);
    llvm::Type* llvm_type(cir::TypeId type_id);
    llvm::Type* llvm_builtin_type(cir::BuiltinTypeKind kind);
    bool is_nullptr_type(cir::TypeId type_id) const;
    llvm::StructType* llvm_nullptr_carrier_type();
    llvm::Constant* llvm_nullptr_carrier_value();
    llvm::StructType* llvm_member_function_pointer_type();
    llvm::FunctionType* llvm_function_type(cir::TypeId type_id);
    std::optional<std::pair<uint64_t, uint64_t>> builtin_size_align(
        cir::BuiltinTypeKind kind) const;
    std::optional<uint64_t> size_of_type(cir::TypeId type_id, SrcLoc loc);
    std::optional<uint64_t> align_of_type(cir::TypeId type_id, SrcLoc loc);
    std::optional<std::pair<uint64_t, uint64_t>> size_align_of_type(cir::TypeId type_id,
                                                                    SrcLoc loc);
    const cir::RecordFieldFact* field_fact_for_place(cir::InstId place_inst) const;
    bool place_access_is_volatile(cir::InstId place_inst) const;

    const cir::File& file_;
    LoweringOptions options_;
    LoweringResult result_;
    std::unique_ptr<llvm::IRBuilder<>> builder_;
    llvm::Function* current_function_ = nullptr;
    std::unordered_map<uint64_t, llvm::Value*> entity_values_;
    std::unordered_map<uint64_t, llvm::Value*> inst_values_;
    std::unordered_map<uint64_t, llvm::Value*> local_places_;
    std::unordered_map<uint64_t, llvm::BasicBlock*> block_values_;
    std::unordered_map<uint64_t, llvm::BasicBlock*> label_address_blocks_;
    std::vector<llvm::BasicBlock*> address_taken_blocks_;
    std::unordered_map<uint64_t, llvm::Value*> landingpad_values_;
    cir::BlockId current_cir_block_{};
    FunctionAbiInfo current_abi_;
    bool has_current_abi_ = false;
    llvm::Value* current_sret_pointer_ = nullptr;
    llvm::Value* current_result_object_pointer_ = nullptr;
};

} // namespace aburi::cir2llvm

#endif // ABURI_CIR2LLVM_LOWERER_H
