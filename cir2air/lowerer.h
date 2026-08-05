#ifndef ABURI_CIR2AIR_LOWERER_H
#define ABURI_CIR2AIR_LOWERER_H

#include "cir2air.h"

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "../abi/aarch64_call_classify.h"
#include "../air/builder.h"

namespace aburi::cir2air {

template <typename IdT>
uint64_t id_key(IdT id) {
    return (static_cast<uint64_t>(id.generation) << 32) | id.index;
}

class Lowerer {
public:
    Lowerer(const cir::File& file, AirLoweringOptions options);

    AirLoweringResult run();

private:
    struct SignatureInfo {
        bool ok = false;
        air::SigId sig{};
        cir::TypeRef return_type{};
        abi::AggregateClass ret_class{};
        std::vector<cir::TypeRef> param_types;
        std::vector<abi::AggregateClass> param_classes;
        bool is_variadic = false;
        bool has_prototype = true;
        bool may_throw = true;
    };

    void error(std::string message, SrcLoc loc = SrcLoc());
    bool has_errors() const;
    size_t error_count() const;

    // Symbol name for an entity: Itanium-mangled in C++ mode (except
    // extern "C" and other raw-name cases), otherwise the source name.
    std::string linkage_name(cir::EntityId entity_id) const;
    std::optional<air::TypeId> air_type(cir::TypeId type_id);
    std::optional<air::TypeId> air_type(cir::TypeRef ref) { return air_type(ref.type); }
    bool is_nullptr_type(cir::TypeId type_id) const;
    air::TypeId air_nullptr_carrier_type() const;
    bool is_memory_only_type(cir::TypeId type_id) const;
    bool is_unsigned_domain(cir::TypeId type_id) const;
    uint64_t pointer_bytes() const;

    SignatureInfo signature_for_function_type(cir::TypeId function_type, SrcLoc loc);

    void declare_entities();
    air::FuncId get_or_declare_function(cir::EntityId entity_id);
    air::GlobalId get_or_create_global(cir::EntityId entity_id);
    air::GlobalId intern_string_literal(const std::vector<uint8_t>& bytes,
                                        uint64_t element_size,
                                        SrcLoc loc);
    void collect_static_ctors();
    void lower_function(cir::FunctionId function_id);
    void lower_inst(cir::InstId inst_id);
    void lower_terminator(const cir::Terminator& terminator);
    void lower_call(cir::InstId inst_id,
                    const cir::Inst& inst,
                    const std::vector<cir::Operand>& operands);
    void lower_construct_in_place(const cir::Inst& inst,
                                  const std::vector<cir::Operand>& operands);
    void lower_destroy(const cir::Inst& inst,
                       const std::vector<cir::Operand>& operands);
    void lower_builtin_call(cir::InstId inst_id,
                            const cir::Inst& inst,
                            const cir::BuiltinCallPayload& payload,
                            const std::vector<cir::ValueRef>& values);
    bool build_asm_payload(const cir::InlineAsmPayload& payload,
                           const std::vector<cir::ValueRef>& values,
                           SrcLoc loc,
                           air::AsmPayload& air_payload,
                           std::vector<air::ValueId>& operands);
    void lower_inline_asm(cir::InstId inst_id,
                          const cir::Inst& inst,
                          const cir::InlineAsmPayload& payload,
                          const std::vector<cir::ValueRef>& values);
    void lower_va_arg(cir::InstId inst_id,
                      const cir::Inst& inst,
                      const std::vector<cir::Operand>& operands);
    void lower_va_arg_aapcs64(cir::InstId inst_id,
                              const cir::Inst& inst,
                              cir::TypeRef target,
                              air::ValueId list);
    void lower_va_arg_sysv(cir::InstId inst_id,
                           const cir::Inst& inst,
                           cir::TypeRef target,
                           air::ValueId list);
    bool marshal_argument(const abi::AggregateClass& cls,
                          cir::TypeRef param_type,
                          cir::ValueRef arg_ref,
                          std::vector<air::ValueId>& args,
                          std::vector<air::SigParam>& site_params,
                          SrcLoc loc);
    std::optional<air::TypeId> hfa_element_type(cir::BuiltinTypeKind kind,
                                                SrcLoc loc);
    void lower_unary(cir::InstId inst_id,
                     const cir::Inst& inst,
                     const cir::UnaryOpDescriptor& descriptor,
                     const std::vector<cir::ValueRef>& values);
    void lower_binary(cir::InstId inst_id,
                      const cir::Inst& inst,
                      const cir::BinaryOpDescriptor& descriptor,
                      const std::vector<cir::ValueRef>& values);

    air::ValueId lower_bitfield_load(cir::InstId place_inst,
                                     const cir::RecordFieldFact& field,
                                     cir::TypeId result_type,
                                     SrcLoc loc);
    void lower_bitfield_store(cir::InstId place_inst,
                              air::ValueId value,
                              cir::TypeId value_type,
                              const cir::RecordFieldFact& field,
                              SrcLoc loc);
    struct ComplexInfo {
        bool valid = false;
        bool is_float = false;
        air::TypeId element{};
        uint64_t element_size = 0;
        uint32_t align = 1;
        cir::TypeId element_cir{};
    };
    ComplexInfo complex_info(cir::TypeId complex_type, SrcLoc loc);
    air::ValueId lower_complex_binary(const cir::Inst& inst,
                                      const cir::BinaryOpDescriptor& descriptor,
                                      air::ValueId lhs,
                                      cir::TypeId lhs_type,
                                      air::ValueId rhs,
                                      cir::TypeId rhs_type);

    air::MemOrder atomic_order(cir::MemoryOrder order) const;
    bool function_type_may_throw(cir::TypeId function_type) const;
    air::BlockId air_block_for(cir::BlockId target, SrcLoc loc);
    air::BlockId current_unwind_target(SrcLoc loc);
    air::ValueId emit_call_or_invoke(air::FuncId callee,
                                     std::span<const air::ValueId> args,
                                     bool can_throw,
                                     SrcLoc loc);
    air::ValueId emit_call_indirect_or_invoke(air::SigId sig,
                                              air::ValueId callee,
                                              std::span<const air::ValueId> args,
                                              bool can_throw,
                                              SrcLoc loc);

    bool invoke_eh_runtime(const std::string& name,
                           std::span<const air::ValueId> args,
                           air::SigId sig,
                           SrcLoc loc);
    air::FuncId declare_runtime_helper(const std::string& name, air::SigId sig);
    air::ValueId value_for(cir::ValueRef ref, SrcLoc loc);
    air::ValueId storage_for_place(cir::InstId place, SrcLoc loc);
    air::ValueId storage_for_entity(cir::EntityId entity, SrcLoc loc);
    void remember(cir::InstId inst_id, air::ValueId value);
    air::ValueId cast_value(air::ValueId value,
                            cir::TypeId source_type,
                            cir::TypeId target_type,
                            SrcLoc loc);
    air::ValueId truth_value(air::ValueId value, SrcLoc loc);
    air::ValueId int_resize(air::ValueId value, air::TypeId to, bool source_unsigned,
                            SrcLoc loc);
    air::ValueId create_entry_stack_alloc(uint64_t size_bytes, uint32_t align_bytes);
    const cir::RecordFieldFact* field_fact_for_place(cir::InstId place_inst) const;

    const cir::File& file_;
    AirLoweringOptions options_;
    AirLoweringResult result_;

    air::Module* mod_ = nullptr;
    air::Function* air_func_ = nullptr;
    std::unique_ptr<air::Builder> builder_;

    std::unordered_map<uint64_t, air::FuncId> function_ids_;
    std::unordered_map<uint64_t, air::GlobalId> global_ids_;
    std::unordered_map<uint64_t, SignatureInfo> signatures_;
    std::unordered_map<std::string, uint32_t> string_globals_;
    std::unordered_map<std::string, air::FuncId> runtime_helpers_;
    uint32_t string_counter_ = 0;
    SignatureInfo current_sig_;
    air::ValueId current_sret_{};
    air::ValueId current_result_object_{};
    cir::BlockId current_cir_block_{};
    std::vector<air::BlockId> label_target_blocks_;
    std::unordered_map<uint64_t, air::ValueId> inst_values_;
    std::unordered_map<uint64_t, air::ValueId> local_places_;
    std::unordered_map<uint64_t, air::BlockId> block_ids_;
};

} // namespace aburi::cir2air

#endif // ABURI_CIR2AIR_LOWERER_H
