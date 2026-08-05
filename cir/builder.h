#ifndef ABURI_CIR_BUILDER_H
#define ABURI_CIR_BUILDER_H

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "file.h"

namespace aburi::cir {

struct FunctionStart {
    FunctionId function{};
    EntityId entity{};
    BlockId entry{};
    std::vector<FunctionParameter> parameters;
};

class Builder {
public:
    struct Checkpoint {
        FunctionId current_function{};
        BlockId current_block{};
        BlockId current_unwind_target{};
        std::unordered_map<std::string, uint32_t> block_name_counts;
    };

    explicit Builder(File& file);

    File& file() { return file_; }
    TypeId void_type();
    TypeId bool_type();
    TypeId char_type();
    TypeId int_type();
    TypeId float_type();
    TypeId double_type();
    TypeId long_double_type();
    TypeId usize_type();
    TypeId unknown_type();
    TypeId dependent_type(std::string_view name);
    TypeId pointer_type(TypeId pointee);
    TypeId pointer_type(TypeRef pointee);
    TypeId array_type(TypeId element, std::optional<size_t> size = std::nullopt);
    TypeId place_type(TypeId object_type);
    TypeId place_type(TypeRef object_type);
    TypeId record_type(EntityId entity, std::string_view name);
    TypeId enum_type(EntityId entity,
                     std::string_view name,
                     TypeRef underlying_type,
                     bool is_scoped = false,
                     bool is_incomplete = true,
                     bool has_fixed_underlying_type = false);
    TypeId complex_type(TypeRef element_type);
    TypeId type_param_type(EntityId entity,
                           std::string_view name,
                           uint32_t index = 0,
                           uint32_t depth = 0,
                           bool is_parameter_pack = false);
    TypeId function_type(TypeId result, const std::vector<TypeId>& params);

    EntityId add_entity(EntityKind kind,
                        std::string_view name,
                        TypeId type = {},
                        EntityId parent = {},
                        SrcLoc loc = SrcLoc(),
                        StorageDuration storage_duration = StorageDuration::Unknown,
                        MemorySpace memory_space = MemorySpace::Default,
                        DeclSemanticFlags decl_flags = {});

    void set_mark_template_pattern(bool value) { mark_template_pattern_ = value; }
    FunctionStart begin_function(std::string_view name,
                                 TypeId result_type,
                                 const std::vector<std::pair<std::string, TypeId>>& params,
                                 SrcLoc loc = SrcLoc(),
                                 EntityKind kind = EntityKind::Function,
                                 EntityId parent = {});
    FunctionStart begin_function(EntityId entity,
                                 TypeId result_type,
                                 const std::vector<std::pair<EntityId, TypeId>>& params,
                                 SrcLoc loc = SrcLoc());

    FunctionId current_function() const { return current_function_; }
    BlockId current_block() const { return current_block_; }
    Checkpoint checkpoint() const;
    void rollback_to(const Checkpoint& checkpoint);
    void switch_to_block(BlockId block);
    void set_current_unwind_target(BlockId target) {
        current_unwind_target_ = target;
    }
    BlockId current_unwind_target() const { return current_unwind_target_; }
    void set_block_unwind_target(BlockId block, BlockId target);
    BlockId create_block(std::string_view name);
    InstId add_block_parameter(BlockId block,
                               TypeId type,
                               std::string_view name = {},
                               SrcLoc loc = SrcLoc());

    BlockId create_detached_block(std::string_view name);
    void rename_block(BlockId block, std::string_view name);
    Fragment block_fragment(BlockId block) const;
    Fragment concat(Fragment first, Fragment second, SrcLoc loc = SrcLoc());
    void attach_fragment_to_function(FunctionId function, const Fragment& fragment);
    bool current_block_terminated() const;
    bool block_terminated(BlockId block) const;

    InstId append_inst(InstKind kind,
                       TypeId result_type,
                       const std::vector<Operand>& operands = {},
                       InstPayload payload = {},
                       SrcLoc loc = SrcLoc(),
                       PlaceFactId place_fact = {});
    InstId param(EntityId entity, TypeId type, SrcLoc loc = SrcLoc());
    InstId integer_literal(int64_t value, std::string spelling = {}, SrcLoc loc = SrcLoc());
    InstId integer_literal(int64_t value,
                           TypeId type,
                           std::string spelling = {},
                           SrcLoc loc = SrcLoc());
    InstId integer_literal(IntegerValue value,
                           TypeId type,
                           std::string spelling = {},
                           SrcLoc loc = SrcLoc());
    InstId boolean_literal(bool value, std::string spelling = {}, SrcLoc loc = SrcLoc());
    InstId nullptr_literal(std::string spelling = "nullptr",
                           SrcLoc loc = SrcLoc());
    InstId floating_literal(FloatingValue value,
                            TypeId type,
                            std::string spelling = {},
                            SrcLoc loc = SrcLoc());
    InstId character_literal(TypeId type,
                             std::string decoded = {},
                             std::string spelling = {},
                             SrcLoc loc = SrcLoc());
    InstId string_literal(std::string value,
                          std::string spelling = {},
                          SrcLoc loc = SrcLoc(),
                          TypeRef element_type = {},
                          size_t char_width = 1);
    InstId name_ref(std::string_view name, TypeId result_type, SrcLoc loc = SrcLoc());
    InstId local_place(EntityId entity, TypeId object_type, SrcLoc loc = SrcLoc());
    InstId global_place(EntityId entity, SrcLoc loc = SrcLoc());
    InstId load(InstId place, SrcLoc loc = SrcLoc());
    InstId lvalue_to_rvalue(InstId place, SrcLoc loc = SrcLoc());
    InstId function_to_pointer(EntityId function, SrcLoc loc = SrcLoc());
    InstId member_pointer_value(EntityId member,
                                TypeId member_pointer_type,
                                SrcLoc loc = SrcLoc());
    InstId label_address(std::string_view name, BlockId target, SrcLoc loc = SrcLoc());
    InstId store(InstId place, InstId value, SrcLoc loc = SrcLoc());
    InstId zero_object(InstId place, SrcLoc loc = SrcLoc());
    InstId lifetime_start(InstId place, SrcLoc loc = SrcLoc());
    InstId lifetime_end(InstId place, SrcLoc loc = SrcLoc());
    InstId stack_alloc(TypeRef object_type,
                       InstId total_bytes,
                       EntityId entity = {},
                       SrcLoc loc = SrcLoc());
    InstId stack_save(SrcLoc loc = SrcLoc());
    InstId atomic_load(InstId place, MemoryOrder order, SrcLoc loc = SrcLoc());
    InstId atomic_store(InstId place, InstId value, MemoryOrder order, SrcLoc loc = SrcLoc());
    InstId atomic_rmw(InstId place, InstId value, AtomicRmwOp op, MemoryOrder order, SrcLoc loc = SrcLoc());
    InstId atomic_cmpxchg(InstId place,
                          InstId expected_place,
                          InstId desired,
                          MemoryOrder success_order,
                          MemoryOrder failure_order,
                          bool is_weak,
                          SrcLoc loc = SrcLoc());
    InstId atomic_fence(MemoryOrder order, SrcLoc loc = SrcLoc());
    InstId complex_make(TypeId complex_type, InstId real, InstId imag, SrcLoc loc = SrcLoc());
    InstId complex_real(InstId value, SrcLoc loc = SrcLoc());
    InstId complex_imag(InstId value, SrcLoc loc = SrcLoc());
    InstId complex_real_place(InstId place, SrcLoc loc = SrcLoc());
    InstId complex_imag_place(InstId place, SrcLoc loc = SrcLoc());
    InstId stack_restore(InstId saved, SrcLoc loc = SrcLoc());
    InstId addr_of(InstId place, SrcLoc loc = SrcLoc());
    InstId deref(InstId pointer, SrcLoc loc = SrcLoc());
    InstId field_addr(InstId base_place, EntityId field, TypeId field_type, SrcLoc loc = SrcLoc());
    InstId data_member_pointer_place(InstId base_place,
                                     InstId member_pointer,
                                     SrcLoc loc = SrcLoc());
    InstId member_function_pointer_callee(InstId adjusted_this,
                                          InstId member_pointer,
                                          TypeId function_pointer_type,
                                          SrcLoc loc = SrcLoc());
    InstId member_function_pointer_this(InstId object_pointer,
                                        InstId member_pointer,
                                        TypeId adjusted_pointer_type,
                                        SrcLoc loc = SrcLoc());
    InstId array_element_place(InstId base, InstId index, SrcLoc loc = SrcLoc());
    InstId vector_element_place(InstId base_place, InstId index, SrcLoc loc = SrcLoc());
    InstId vector_extract(InstId vector, InstId index, SrcLoc loc = SrcLoc());
    InstId sizeof_type(TypeId queried_type, SrcLoc loc = SrcLoc());
    InstId reflect_type(TypeRef operand, SrcLoc loc = SrcLoc());
    InstId reflect_entity(MetaInfoKind kind,
                          EntityId entity,
                          SrcLoc loc = SrcLoc());
    InstId alignof_type(TypeId queried_type, SrcLoc loc = SrcLoc());
    InstId unary(UnaryOpKind op, TypeId result_type, InstId operand, SrcLoc loc = SrcLoc());
    InstId binary(BinaryOpKind op, TypeId result_type, InstId lhs, InstId rhs, SrcLoc loc = SrcLoc());
    InstId cast(TypeId target_type, InstId value, std::string_view cast_kind = "value", SrcLoc loc = SrcLoc());
    InstId call(EntityId callee, TypeId result_type, const std::vector<InstId>& args, SrcLoc loc = SrcLoc());
    InstId call_indirect(InstId callee, TypeId result_type, const std::vector<InstId>& args, SrcLoc loc = SrcLoc());
    InstId call_virtual(InstId callee,
                        EntityId declaration,
                        TypeId result_type,
                        const std::vector<InstId>& args,
                        SrcLoc loc = SrcLoc());
    InstId emit_va_start(InstId va_list_place, SrcLoc loc = SrcLoc());
    InstId emit_va_arg(InstId va_list_place, TypeId result_type, SrcLoc loc = SrcLoc());
    InstId emit_va_end(InstId va_list_place, SrcLoc loc = SrcLoc());
    InstId emit_va_copy(InstId dest_place, InstId src_place, SrcLoc loc = SrcLoc());
    InstId builtin_call(BuiltinKind kind,
                        std::string_view name,
                        TypeId result_type,
                        const std::vector<InstId>& args,
                        SrcLoc loc = SrcLoc(),
                        TypeRef type_operand = {},
                        std::vector<int64_t> integer_operands = {});
    InstId inline_asm(std::string asm_string,
                      std::string constraints,
                      const std::vector<InstId>& args,
                      bool has_side_effects,
                      bool align_stack,
                      bool intel_dialect,
                      SrcLoc loc = SrcLoc());
    InstId inline_asm(InlineAsmPayload payload,
                      const std::vector<InstId>& operands,
                      SrcLoc loc = SrcLoc());
    InstId construct_in_place(InstId place, EntityId constructor, const std::vector<InstId>& args, SrcLoc loc = SrcLoc());
    InstId destroy(InstId place, EntityId destructor = {}, SrcLoc loc = SrcLoc());
    InstId dependent_call(std::string_view name, TypeId result_type, const std::vector<InstId>& args, SrcLoc loc = SrcLoc());
    InstId dependent_region(uint32_t hole, std::string display, InstId place = {}, SrcLoc loc = SrcLoc());
    InstId eh_alloc_exception(TypeRef object_type, SrcLoc loc = SrcLoc());
    InstId eh_landing_pad(EhLandingPadPayload payload, SrcLoc loc = SrcLoc());
    InstId eh_selector(InstId pad, SrcLoc loc = SrcLoc());
    InstId eh_typeid_for(EntityId typeinfo, SrcLoc loc = SrcLoc());
    InstId catch_begin(InstId exception_ptr, SrcLoc loc = SrcLoc());
    InstId catch_end(SrcLoc loc = SrcLoc());
    InstId coro_begin(InstId allocation, SrcLoc loc = SrcLoc());
    InstId coro_frame_size(SrcLoc loc = SrcLoc());
    InstId coro_frame_align(SrcLoc loc = SrcLoc());
    InstId coro_promise_place(InstId frame,
                              TypeId promise_type,
                              SrcLoc loc = SrcLoc());
    InstId coro_save(uint32_t index,
                     CoroSaveKind kind,
                     SrcLoc loc = SrcLoc());
    InstId coro_transfer(InstId frame, SrcLoc loc = SrcLoc());
    InstId objc_message_send(const ObjCMessageSendPayload& payload,
                             const std::vector<InstId>& receiver_and_args,
                             TypeId result_type,
                             SrcLoc loc = SrcLoc());
    InstId objc_ivar_addr(InstId object_pointer,
                          EntityId ivar,
                          TypeId place_type,
                          SrcLoc loc = SrcLoc());
    InstId objc_selector_literal(SelectorId selector,
                                 TypeId sel_type,
                                 SrcLoc loc = SrcLoc());
    InstId objc_arc_op(ObjCArcOpKind op,
                       const std::vector<InstId>& operands,
                       TypeId result_type = {},
                       SrcLoc loc = SrcLoc());
    InstId objc_string_literal(std::string bytes,
                               std::string spelling,
                               TypeId result_type,
                               SrcLoc loc = SrcLoc());
    InstId error(std::string message, SrcLoc loc = SrcLoc());

    void return_void(SrcLoc loc = SrcLoc());
    void return_value(InstId value, SrcLoc loc = SrcLoc());
    void branch(BlockId target, const std::vector<InstId>& args = {}, SrcLoc loc = SrcLoc());
    void branch_from(BlockId source,
                     BlockId target,
                     const std::vector<InstId>& args = {},
                     SrcLoc loc = SrcLoc());
    void cond_branch(InstId condition,
                     BlockId true_target,
                     BlockId false_target,
                     const std::vector<InstId>& args = {},
                     SrcLoc loc = SrcLoc());
    void cond_branch_from(BlockId source,
                          InstId condition,
                          BlockId true_target,
                          BlockId false_target,
                          const std::vector<InstId>& args = {},
                          SrcLoc loc = SrcLoc());
    void switch_branch(InstId condition,
                       TypeRef condition_type,
                       BlockId default_target,
                       std::vector<SwitchCaseRange> cases,
                       SrcLoc loc = SrcLoc());
    void switch_branch_from(BlockId source,
                            InstId condition,
                            TypeRef condition_type,
                            BlockId default_target,
                            std::vector<SwitchCaseRange> cases,
                            SrcLoc loc = SrcLoc());
    void indirect_branch(InstId target, SrcLoc loc = SrcLoc());
    void indirect_branch_from(BlockId source, InstId target, SrcLoc loc = SrcLoc());
    void asm_goto_from(BlockId source,
                       InlineAsmPayload payload,
                       const std::vector<InstId>& operands,
                       BlockId fallthrough,
                       SrcLoc loc = SrcLoc());
    void unreachable(SrcLoc loc = SrcLoc());
    void unreachable_from(BlockId source, SrcLoc loc = SrcLoc());
    void throw_from(BlockId source,
                    InstId exception_place,
                    EntityId typeinfo,
                    EntityId destructor = {},
                    SrcLoc loc = SrcLoc());
    void rethrow_from(BlockId source, SrcLoc loc = SrcLoc());
    void resume_from(BlockId source,
                     InstId exception_ptr,
                     InstId selector,
                     SrcLoc loc = SrcLoc());
    void return_void_from(BlockId source, SrcLoc loc = SrcLoc());
    void return_value_from(BlockId source, InstId value, SrcLoc loc = SrcLoc());
    void coro_suspend_from(BlockId source,
                           uint32_t index,
                           CoroSaveKind kind,
                           BlockId resume_target,
                           BlockId destroy_target,
                           SrcLoc loc = SrcLoc());
    void coro_end_from(BlockId source, SrcLoc loc = SrcLoc());

private:
    InstPayload payload_none() const;
    NameId unique_block_name(std::string_view name);
    TypeRef entity_object_ref(EntityId entity, TypeId fallback_type);
    TypeRef object_ref_from_place(InstId place);
    TypeId object_type_from_place(InstId place);
    TypeRef element_ref_from_array_base(InstId base);
    TypeRef element_ref_from_vector_base(InstId base);
    TypeRef inherit_memory_if_default(TypeRef ref, MemorySpace memory_space) const;
    PlaceFactId add_place_fact(TypeRef object_type,
                               StorageDuration storage_duration,
                               EntityId entity = {},
                               InstId base = {},
                               SrcLoc loc = SrcLoc());

    File& file_;
    FunctionId current_function_{};
    BlockId current_block_{};
    BlockId current_unwind_target_{};
    bool mark_template_pattern_ = false;
    std::unordered_map<std::string, uint32_t> block_name_counts_;
};

} // namespace aburi::cir

#endif // ABURI_CIR_BUILDER_H
