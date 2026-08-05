#include "consteval_engine.h"

#include "constant_state.h"
#include "metafn_eval.h"

#include "../abi/endian.h"
#include "../cir/layout.h"
#include "../perf_stats.h"
#include "eval_state.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <limits>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

#include "../numeric/floating_cir.h"

namespace {

using aburi::cir::BinaryOpKind;
using aburi::cir::BlockId;
using aburi::cir::InstId;
using aburi::cir::InstKind;
using aburi::cir::TerminatorKind;
using aburi::cir::TypeId;
using aburi::cir::TypeKind;
using aburi::cir::UnaryOpKind;
using aburi::cir::ValueRef;

uint64_t inst_key(InstId id) {
    return (uint64_t(id.generation) << 32) | id.index;
}

bool has_constexpr_unknown_representation(
    const aburi::cir::File& file,
    aburi::cir::TypeRef ref,
    std::vector<TypeId>& record_stack) {
    while (file.valid(ref.type) &&
           file.type(ref.type).kind == TypeKind::Typedef) {
        const auto* alias = std::get_if<aburi::cir::TypedefTypePayload>(
            &file.type_payload(ref.type));
        if (!alias) {
            return true;
        }
        ref.qualifiers = static_cast<uint8_t>(
            ref.qualifiers | alias->underlying_type.qualifiers);
        ref.type = alias->underlying_type.type;
    }
    ref.type = file.resolved_type(ref.type);
    if (!file.valid(ref.type) ||
        (ref.qualifiers & aburi::cir::QualVolatile) != 0) {
        return true;
    }
    switch (file.type(ref.type).kind) {
        case TypeKind::Pointer:
        case TypeKind::BlockPointer:
        case TypeKind::MemberPointer:
            return true;
        case TypeKind::Array: {
            const auto* array = std::get_if<aburi::cir::ArrayTypePayload>(
                &file.type_payload(ref.type));
            return !array || has_constexpr_unknown_representation(
                file, array->element_type, record_stack);
        }
        case TypeKind::Record: {
            const aburi::cir::RecordFacts* facts =
                file.record_facts_for_type(ref.type);
            if (!facts || facts->is_incomplete ||
                facts->kind == aburi::cir::RecordKind::Union) {
                return true;
            }
            if (std::find(record_stack.begin(), record_stack.end(), ref.type) !=
                record_stack.end()) {
                return false;
            }
            record_stack.push_back(ref.type);
            for (const aburi::cir::RecordBaseFact& base : facts->bases) {
                if (has_constexpr_unknown_representation(
                        file, base.type, record_stack)) {
                    record_stack.pop_back();
                    return true;
                }
            }
            for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                TypeId field_type = file.resolved_type(field.type.type);
                if ((file.valid(field_type) &&
                     (file.type(field_type).kind == TypeKind::LValueReference ||
                      file.type(field_type).kind == TypeKind::RValueReference)) ||
                    has_constexpr_unknown_representation(
                        file, field.type, record_stack)) {
                    record_stack.pop_back();
                    return true;
                }
            }
            record_stack.pop_back();
            return false;
        }
        default:
            return false;
    }
}

bool has_constexpr_unknown_representation(const aburi::cir::File& file,
                                          aburi::cir::TypeRef ref) {
    std::vector<TypeId> record_stack;
    return has_constexpr_unknown_representation(file, ref, record_stack);
}

ConstEvalDiagnostic make_diag(ConstEvalDiagCode code,
                              std::string message,
                              SrcLoc loc) {
    return ConstEvalDiagnostic::make(code, std::move(message), loc);
}

ConstEvalResult make_not_evaluated(std::string message,
                                   ConstEvalDiagCode code,
                                   SrcLoc loc) {
    ConstEvalResult result = ConstEvalResult::not_evaluated(std::move(message));
    result.diagnostics.push_back(make_diag(code, result.message, loc));
    return result;
}

ConstEvalResult make_unsupported(std::string message, SrcLoc loc) {
    return ConstEvalResult::unsupported(
        std::move(message), ConstEvalDiagCode::UnsupportedExpression, loc);
}

ConstEvalResult make_error(ConstEvalDiagCode code,
                           std::string message,
                           SrcLoc loc) {
    return ConstEvalResult::error(std::move(message), code, loc);
}

enum class AllocationCallKind {
    None,
    Allocation,
    NonallocatingPlacement,
    Deallocation
};

// Itanium spellings of the replaceable global allocation functions:
// `operator new`/`new[]` mangle as _Znw/_Zna plus the target's size_t code
// (j on ILP32, m when long is 64-bit, y otherwise); `operator delete`/
// `delete[]` as _ZdlPv/_ZdaPv, carrying that same code only in the sized
// forms. Either family may append the align_val_t parameter. Classifying by
// grammar rather than by a fixed list keeps every target's spelling covered:
// matching only the LP64 names silently skipped ILP32 and the sized/aligned
// forms, which reach the evaluator through the same call path.
AllocationCallKind allocation_call_kind(std::string_view name) {
    auto drop_align_suffix = [](std::string_view rest) {
        constexpr std::string_view align_parameter = "St11align_val_t";
        if (rest.size() >= align_parameter.size() &&
            rest.substr(rest.size() - align_parameter.size()) ==
                align_parameter) {
            rest.remove_suffix(align_parameter.size());
        }
        return rest;
    };
    auto is_size_code = [](std::string_view rest) {
        return rest.size() == 1 &&
               (rest.front() == 'j' || rest.front() == 'm' ||
                rest.front() == 'y');
    };
    if (name.rfind("_Znw", 0) == 0 || name.rfind("_Zna", 0) == 0) {

        return is_size_code(drop_align_suffix(name.substr(4)))
            ? AllocationCallKind::Allocation
            : AllocationCallKind::None;
    }
    if (name.rfind("_ZdlPv", 0) == 0 || name.rfind("_ZdaPv", 0) == 0) {
        std::string_view rest = drop_align_suffix(name.substr(6));
        return rest.empty() || is_size_code(rest)
            ? AllocationCallKind::Deallocation
            : AllocationCallKind::None;
    }
    return AllocationCallKind::None;
}

bool is_truthy(const ConstValue& value, bool& out) {
    switch (value.kind) {
        case ConstValueKind::Integer:
            out = value.int_value.to_unsigned_u128() != 0;
            return true;
        case ConstValueKind::Boolean:
            out = value.bool_value;
            return true;
        case ConstValueKind::Floating:
            out = !aburi::floating::is_zero(value.float_value.value);
            return true;
        case ConstValueKind::Null:
            out = false;
            return true;
        case ConstValueKind::Address:
        case ConstValueKind::MemberPointer:
            out = true;
            return true;
        default:
            return false;
    }
}

std::optional<ConstIntValue> value_to_int(const ConstValue& value,
                                          aburi::cir::IntegerTypeShape shape) {
    switch (value.kind) {
        case ConstValueKind::Integer:
            return value.int_value.cast(shape.bit_width, shape.is_unsigned);
        case ConstValueKind::Boolean:
            return shape.is_unsigned
                ? ConstIntValue::from_unsigned(value.bool_value ? 1 : 0,
                                               shape.bit_width)
                : ConstIntValue::from_signed(value.bool_value ? 1 : 0,
                                             shape.bit_width);
        case ConstValueKind::Null:
            if (value.null_kind == ConstNullKind::Pointer) {
                return shape.is_unsigned
                    ? ConstIntValue::from_unsigned(0, shape.bit_width)
                    : ConstIntValue::from_signed(0, shape.bit_width);
            }
            return std::nullopt;
        default:
            return std::nullopt;
    }
}

aburi::floating::FloatResult value_to_float(
    const ConstValue& value,
    aburi::cir::FloatingSemantics semantics) {
    switch (value.kind) {
        case ConstValueKind::Floating:
            return aburi::floating::convert(value.float_value.value, semantics);
        case ConstValueKind::Integer:
            return aburi::floating::from_integer(
                value.int_value.to_unsigned_u128(),
                value.int_value.bit_width,
                !value.int_value.is_unsigned,
                semantics);
        case ConstValueKind::Boolean:
            return aburi::floating::from_integer(
                value.bool_value ? 1 : 0, 1, false, semantics);
        default:
            return {{}, {}, aburi::floating::FloatError::InvalidEncoding};
    }
}

bool floating_status_disqualifies(aburi::floating::FloatStatus status) {
    return status.has(aburi::floating::FloatStatusFlag::Invalid) ||
           status.has(aburi::floating::FloatStatusFlag::DivideByZero);
}

aburi::cir::FloatingValue floating_from_raw_bits(
    aburi::cir::FloatingSemantics semantics,
    uint64_t low,
    uint64_t high) {
    aburi::cir::FloatingValue value{semantics, low, high};
    if (semantics == aburi::cir::FloatingSemantics::IEEEBinary16) {
        value.low_bits &= 0xffffu;
        value.high_bits = 0;
    } else if (semantics == aburi::cir::FloatingSemantics::IEEEBinary32) {
        value.low_bits &= 0xffffffffu;
        value.high_bits = 0;
    } else if (semantics == aburi::cir::FloatingSemantics::IEEEBinary64) {
        value.high_bits = 0;
    } else if (semantics == aburi::cir::FloatingSemantics::X87Extended80) {
        value.high_bits &= 0xffffu;
    }
    return value;
}

bool is_bool_type(const aburi::cir::File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != TypeKind::Builtin) {
        return false;
    }
    const auto* builtin = std::get_if<aburi::cir::BuiltinTypePayload>(&file.type_payload(type));
    return builtin && builtin->kind == aburi::cir::BuiltinTypeKind::Bool;
}

bool is_void_type(const aburi::cir::File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != TypeKind::Builtin) {
        return false;
    }
    const auto* builtin =
        std::get_if<aburi::cir::BuiltinTypePayload>(&file.type_payload(type));
    return builtin && builtin->kind == aburi::cir::BuiltinTypeKind::Void;
}

ConstValue bool_result_for_type(const aburi::cir::File& file, TypeId type, bool value) {
    if (is_bool_type(file, type)) {
        return ConstValue::boolean(value);
    }
    if (aburi::cir::is_integer_like_type(file, type)) {
        auto shape = aburi::cir::integer_shape_for_type(file, type);
        return ConstValue::integer(value
            ? ConstIntValue::from_unsigned(1, shape.bit_width).cast(shape.bit_width,
                                                                    shape.is_unsigned)
            : ConstIntValue::from_unsigned(0, shape.bit_width).cast(shape.bit_width,
                                                                    shape.is_unsigned));
    }
    return ConstValue::boolean(value);
}

std::optional<aburi::cir::TypeRef> first_type_operand(const aburi::cir::File& file,
                                                      const aburi::cir::Inst& inst) {
    std::vector<aburi::cir::Operand> operands = file.operands(inst.operands);
    for (const aburi::cir::Operand& operand : operands) {
        if (const auto* type_ref =
                std::get_if<aburi::cir::TypeRef>(&operand.data)) {
            return *type_ref;
        }
    }
    return std::nullopt;
}

std::vector<ValueRef> value_operands(const aburi::cir::File& file,
                                     const aburi::cir::Inst& inst) {
    return file.value_operands(inst.operands);
}

uint64_t bytes_to_u64(const aburi::cir::LiteralByteArray& bytes) {
    uint64_t value = 0;
    size_t count = std::min<size_t>(bytes.size(), sizeof(uint64_t));
    for (size_t index = 0; index < count; ++index) {
        value = (value << 8) | static_cast<uint64_t>(bytes[index]);
    }
    return value;
}

uint64_t entity_key(aburi::cir::EntityId id) {
    return (uint64_t(id.generation) << 32) | id.index;
}

aburi::cir::EntityId entity_operand_at(const aburi::cir::File& file,
                                       const aburi::cir::Inst& inst,
                                       size_t index) {
    std::vector<aburi::cir::Operand> operands = file.operands(inst.operands);
    if (index >= operands.size()) {
        return {};
    }
    if (const auto* entity =
            std::get_if<aburi::cir::EntityId>(&operands[index].data)) {
        return *entity;
    }
    return {};
}

std::optional<size_t> pointee_size(const aburi::cir::File& file, TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != TypeKind::Pointer) {
        return std::nullopt;
    }
    const auto* pointer =
        std::get_if<aburi::cir::PointerTypePayload>(&file.type_payload(type));
    if (!pointer) {
        return std::nullopt;
    }
    return aburi::cir::size_of_type(file, pointer->pointee.type);
}

std::optional<ConstAddressValue> as_address(const ConstValue& value) {
    if (value.kind == ConstValueKind::Address) {
        return value.address_value;
    }
    if (value.is_null(ConstNullKind::Nullptr) ||
        value.is_null(ConstNullKind::Pointer)) {
        return ConstAddressValue{};
    }
    return std::nullopt;
}

bool address_is_null_base(const ConstAddressValue& address) {
    return !address.entity.valid() && address.allocation_id == 0 &&
           !address.string_literal.valid();
}

bool is_pointer_or_reference_type(const aburi::cir::File& file,
                                  TypeId type,
                                  bool* is_reference = nullptr) {
    TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return false;
    }
    TypeKind kind = file.type(resolved).kind;
    bool reference = kind == TypeKind::LValueReference ||
                     kind == TypeKind::RValueReference;
    if (is_reference) {
        *is_reference = reference;
    }
    return kind == TypeKind::Pointer ||
           kind == TypeKind::BlockPointer ||
           reference;
}

class Evaluator {
public:
    Evaluator(const ConstEvalContext& context, ConstEvalRequest request)
        : context_(context),
          request_(request),
          state_(context.lang_options.consteval_step_limit,
                 context.lang_options.consteval_recursion_limit) {}

    ConstEvalResult evaluate_inst(InstId inst) {
        std::unordered_map<uint64_t, ConstValue> empty_env;
        return evaluate_inst(inst, empty_env);
    }

    AllocationCallKind callee_allocation_kind(
        aburi::cir::EntityId callee) const {
        if (!callee.valid() || !file().valid(callee)) {
            return AllocationCallKind::None;
        }
        const aburi::cir::Entity& entity = file().entity(callee);
        if (!entity.name.valid()) {
            return AllocationCallKind::None;
        }
        AllocationCallKind kind = allocation_call_kind(
            file().name(entity.name));
        if (kind != AllocationCallKind::None) {
            return kind;
        }

        // Header-defined non-allocating placement new has a source-level
        // entity name rather than the ABI name used by an implicitly declared
        // replaceable allocation function. Recognize its structural operator
        // identity and canonical (size, void*) signature.
        if (entity.kind != aburi::cir::EntityKind::Function ||
            (entity.operator_function.kind !=
                 aburi::cir::OperatorFunctionKind::Allocation &&
             entity.operator_function.kind !=
                 aburi::cir::OperatorFunctionKind::Deallocation)) {
            return AllocationCallKind::None;
        }
        TypeId function_type = file().resolved_type(entity.type);
        if (!file().valid(function_type) ||
            file().type(function_type).kind != TypeKind::Function) {
            return AllocationCallKind::None;
        }
        const auto* function =
            std::get_if<aburi::cir::FunctionTypePayload>(
                &file().type_payload(function_type));
        if (!function || function->parameters.empty() ||
            function->parameters.size() > 2) {
            return AllocationCallKind::None;
        }
        if (function->parameters.size() == 1) {
            return entity.operator_function.kind ==
                    aburi::cir::OperatorFunctionKind::Allocation
                ? AllocationCallKind::Allocation
                : AllocationCallKind::Deallocation;
        }
        TypeId placement_type =
            file().resolved_type(function->parameters[1].type);
        bool has_void_pointer_placement =
            file().valid(placement_type) &&
            file().type(placement_type).kind == TypeKind::Pointer &&
            is_void_type(file(),
                         file().pointer_pointee_type(placement_type));
        if (entity.operator_function.kind ==
            aburi::cir::OperatorFunctionKind::Deallocation) {
            return has_void_pointer_placement
                ? AllocationCallKind::None
                : AllocationCallKind::Deallocation;
        }
        return has_void_pointer_placement
            ? AllocationCallKind::NonallocatingPlacement
            : AllocationCallKind::Allocation;
    }

    bool is_std_construct_at(aburi::cir::EntityId callee) const {
        if (!callee.valid() || !file().valid(callee)) {
            return false;
        }
        aburi::cir::EntityId declaration = callee;
        if (const aburi::cir::TemplateSpecializationFact* specialization =
                file().template_specialization(callee)) {
            declaration = specialization->selected_template_entity.valid()
                ? specialization->selected_template_entity
                : specialization->template_entity;
        }
        if (!declaration.valid() || !file().valid(declaration)) {
            return false;
        }
        const aburi::cir::Entity& function = file().entity(declaration);
        if (!function.name.valid() ||
            file().name(function.name) != "construct_at") {
            return false;
        }

        aburi::cir::DeclContextId context = function.semantic_context;
        while (context.valid() && file().valid(context)) {
            const aburi::cir::DeclContext& declaration_context =
                file().decl_context(context);
            aburi::cir::EntityId owner = declaration_context.owner;
            if (owner.valid() && file().valid(owner) &&
                file().entity(owner).kind ==
                    aburi::cir::EntityKind::Namespace) {
                const aburi::cir::Entity& namespace_entity =
                    file().entity(owner);
                if (namespace_entity.name.valid() &&
                    file().name(namespace_entity.name) == "std") {
                    return true;
                }
                if (!declaration_context.is_inline_namespace) {
                    return false;
                }
            }
            context = declaration_context.parent;
        }
        return false;
    }

    bool demand_block_function_definitions(BlockId block_id) const {
        if (!context_.demand_function_definition) {
            return true;
        }
        if (!file().valid(block_id)) {
            return true;
        }

        std::vector<InstId> instructions =
            file().block(block_id).instructions;
        for (InstId inst_id : instructions) {
            if (!file().valid(inst_id)) {
                continue;
            }
            const aburi::cir::Inst& inst = file().inst(inst_id);
            size_t entity_index = 0;
            switch (inst.kind) {
                case InstKind::Call:
                    entity_index = 0;
                    break;
                case InstKind::ConstructInPlace:
                case InstKind::Destroy:
                    entity_index = 1;
                    break;
                default:
                    continue;
            }
            aburi::cir::EntityId callee =
                entity_operand_at(file(), inst, entity_index);

            if (callee_allocation_kind(callee) != AllocationCallKind::None) {
                continue;
            }
            if (callee.valid() &&
                !context_.demand_function_definition(callee, inst.loc) &&
                request_.required) {
                return false;
            }
        }
        return true;
    }
    ConstEvalResult evaluate_direct_entity_call(
        aburi::cir::EntityId callee,
        std::vector<ConstValue> arg_values,
        SrcLoc loc,
        bool allow_void_return) {
        if (!context_.lang_options
                 .consteval_function_interpreter_enabled()) {
            return make_unsupported(
                "function call is not a constant expression in this mode",
                loc);
        }
        if (!callee.valid() || !file().valid(callee)) {
            return make_unsupported("indirect call is not a constant expression",
                                    loc);
        }

        AllocationCallKind allocation_kind = callee_allocation_kind(callee);
        if (context_.lang_options.is_cxx20_or_later() &&
            allocation_kind != AllocationCallKind::None) {
            if (allocation_kind == AllocationCallKind::Allocation) {
                if (arg_values.empty() || arg_values.size() > 2) {
                    return make_unsupported(
                        "allocation call arguments are not supported in "
                        "constant evaluation",
                        loc);
                }
                std::optional<int64_t> size = arg_values[0].try_as_int64();
                if (!size.has_value() || *size < 0) {
                    return make_unsupported(
                        "allocation size is not a constant expression", loc);
                }
                uint64_t allocation = state_.memory().allocate_dynamic(
                    static_cast<size_t>(*size));
                ConstAddressValue address;
                address.allocation_id = allocation;
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(address));
            }
            if (allocation_kind ==
                AllocationCallKind::NonallocatingPlacement) {
                if (construct_at_call_depth_ == 0 ||
                    arg_values.size() != 2) {
                    return make_unsupported(
                        "placement allocation is only permitted through "
                        "std::construct_at in constant evaluation",
                        loc);
                }
                std::optional<ConstAddressValue> address =
                    as_address(arg_values[1]);
                if (!address.has_value() || address->allocation_id == 0) {
                    return make_unsupported(
                        "std::construct_at destination is not "
                        "evaluator-owned memory",
                        loc);
                }
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(*address));
            }
            if (allocation_kind == AllocationCallKind::Deallocation) {
                if (arg_values.empty()) {
                    return make_unsupported(
                        "deallocation call has no pointer operand", loc);
                }
                const ConstValue& pointer = arg_values[0];
                if (pointer.is_null(ConstNullKind::Pointer) ||
                    pointer.is_null(ConstNullKind::Nullptr)) {

                    return ConstEvalResult::constant(ConstValue::void_value());
                }
                std::optional<ConstAddressValue> address = as_address(pointer);
                if (!address.has_value() || address->allocation_id == 0 ||
                    address->byte_offset != 0) {
                    return make_error(
                        ConstEvalDiagCode::InvalidDeallocation,
                        "deallocation of a pointer that is not the result of "
                        "a constexpr allocation",
                        loc);
                }
                switch (state_.memory().deallocate_dynamic(
                    address->allocation_id)) {
                    case EvalDeallocStatus::Ok:
                        return ConstEvalResult::constant(
                            ConstValue::void_value());
                    case EvalDeallocStatus::AlreadyDeallocated:
                        return make_error(
                            ConstEvalDiagCode::InvalidDeallocation,
                            "constexpr memory was deallocated twice", loc);
                    case EvalDeallocStatus::NotDynamic:
                    case EvalDeallocStatus::NotAnAllocation:
                        return make_error(
                            ConstEvalDiagCode::InvalidDeallocation,
                            "deallocation of a pointer that is not the result "
                            "of a constexpr allocation",
                            loc);
                }
            }
        }

        if (context_.lang_options.is_cxx_mode()) {
            const aburi::cir::Entity& callee_entity = file().entity(callee);
            if (!callee_entity.decl_flags.is_constexpr &&
                !callee_entity.decl_flags.is_consteval) {
                std::string name = callee_entity.name.valid()
                    ? std::string(file().name(callee_entity.name))
                    : std::string("<function>");
                return make_unsupported(
                    "call to non-constexpr function '" + name +
                        "' is not a constant expression",
                    loc);
            }
        }
        if (context_.demand_function_definition) {
            bool definition_available =
                context_.demand_function_definition(callee, loc);
            if (request_.required && !definition_available) {
                return make_unsupported(
                    "required function definition could not be instantiated "
                    "for constant evaluation",
                    loc);
            }
        }
        const aburi::cir::Function* body = nullptr;
        for (aburi::cir::FunctionId id : file().function_ids()) {
            const aburi::cir::Function& candidate = file().function(id);
            if (candidate.entity == callee &&
                !file().entity(candidate.entity).is_template_pattern) {
                body = &candidate;
                break;
            }
        }
        if (!body || !file().valid(body->entry_block)) {
            return make_unsupported(
                "call to a function with no available body is not a "
                "constant expression",
                loc);
        }
        if (arg_values.size() != body->parameters.size()) {
            return make_unsupported(
                "call argument count does not match for constant evaluation",
                loc);
        }

        aburi::cir::Fragment callee_fragment;
        callee_fragment.blocks = body->blocks;
        callee_fragment.entry = body->entry_block;
        callee_fragment.exit =
            body->blocks.empty() ? body->entry_block : body->blocks.back();

        std::string frame_name = "<function>";
        if (file().entity(callee).name.valid()) {
            frame_name = std::string(file().name(file().entity(callee).name));
        }
        if (!state_.push_frame(std::move(frame_name))) {
            return make_error(ConstEvalDiagCode::RecursionLimitExceeded,
                              "constant evaluation recursion limit exceeded",
                              loc);
        }

        std::unordered_map<uint64_t, uint64_t> saved_locals =
            std::move(local_allocations_);
        local_allocations_.clear();
        bool construct_at_call = is_std_construct_at(callee);
        if (construct_at_call) {
            ++construct_at_call_depth_;
        }
        ConstEvalResult result = evaluate_frame(callee_fragment,
                                                std::move(arg_values),
                                                allow_void_return);
        if (construct_at_call) {
            --construct_at_call_depth_;
        }
        local_allocations_ = std::move(saved_locals);
        state_.pop_frame();
        return result;
    }

    ConstEvalResult evaluate_call(const aburi::cir::Inst& inst,
                                  std::unordered_map<uint64_t, ConstValue>& env) {
        std::vector<aburi::cir::Operand> operands = file().operands(inst.operands);
        if (operands.empty()) {
            return make_unsupported("call has no callee", inst.loc);
        }
        std::vector<ConstValue> arg_values;
        arg_values.reserve(operands.size() - 1);
        for (size_t index = 1; index < operands.size(); ++index) {
            const auto* value = std::get_if<ValueRef>(&operands[index].data);
            if (!value) {
                continue;
            }
            ConstEvalResult evaluated = value_for_ref(*value, env);
            if (evaluated.status != ConstEvalStatus::Constant ||
                !evaluated.value.has_value()) {
                return evaluated;
            }
            arg_values.push_back(*evaluated.value);
        }

        aburi::cir::EntityId resolved_callee{};
        const aburi::cir::RecordFacts* virtual_facts = nullptr;
        const aburi::cir::VirtualOverrideEdgeFact* covariant_edge = nullptr;
        const auto* virtual_call = std::get_if<aburi::cir::CallPayload>(
            &file().payload(inst.payload_index));
        if (virtual_call && virtual_call->virtual_declaration.valid()) {
            if (arg_values.empty()) {
                return make_unsupported("virtual call has no object argument",
                                        inst.loc);
            }
            std::optional<ConstAddressValue> object =
                as_address(arg_values.front());
            if (!object.has_value() || !object->entity.valid() ||
                !file().valid(object->entity)) {
                return make_unsupported(
                    "virtual call object has no constant dynamic type",
                    inst.loc);
            }
            TypeId dynamic_type =
                file().resolved_type(file().entity(object->entity).type);
            virtual_facts = file().record_facts_for_type(dynamic_type);
            if (!virtual_facts) {
                return make_unsupported(
                    "virtual call dynamic type has no record facts",
                    inst.loc);
            }

            std::vector<aburi::cir::EntityId> object_path;
            for (const ConstSubobjectPathEntry& step : object->subobjects) {
                if (!step.is_array_element && step.entity.valid()) {
                    object_path.push_back(step.entity);
                }
            }
            uint32_t declaration_subobject = 0;
            bool found_subobject = false;
            for (const aburi::cir::VirtualSubobjectFact& subobject :
                 virtual_facts->virtual_subobjects) {
                if (subobject.storage_path == object_path) {
                    declaration_subobject = subobject.id;
                    found_subobject = true;
                    break;
                }
            }
            const aburi::cir::VirtualFinalOverriderFact* selected = nullptr;
            for (const aburi::cir::VirtualFinalOverriderFact& final :
                 virtual_facts->virtual_final_overriders) {
                if (final.virtual_declaration !=
                        virtual_call->virtual_declaration ||
                    !final.final_overrider.valid() || final.has_conflict()) {
                    continue;
                }
                if (found_subobject &&
                    final.declaration_subobject == declaration_subobject) {
                    selected = &final;
                    break;
                }
                if (!selected) {
                    selected = &final;
                } else if (!found_subobject) {
                    selected = nullptr;
                    break;
                }
            }
            if (!selected) {
                return make_unsupported(
                    "virtual call has no constant final overrider", inst.loc);
            }
            resolved_callee = selected->final_overrider;
            const aburi::cir::VirtualSubobjectFact& declaration_object =
                virtual_facts->virtual_subobjects[
                    selected->declaration_subobject];
            const aburi::cir::VirtualSubobjectFact& final_object =
                virtual_facts->virtual_subobjects[selected->final_subobject];
            object->byte_offset +=
                static_cast<int64_t>(final_object.static_offset_bytes) -
                static_cast<int64_t>(
                    declaration_object.static_offset_bytes);
            object->subobjects.clear();
            for (aburi::cir::EntityId step : final_object.storage_path) {
                object->subobjects.push_back(
                    ConstSubobjectPathEntry{step, 0, false});
            }
            arg_values.front() = ConstValue::address_value_of(*object);
            for (const aburi::cir::VirtualOverrideEdgeFact& edge :
                 virtual_facts->virtual_override_edges) {
                if (edge.overriding == resolved_callee &&
                    edge.overridden == virtual_call->virtual_declaration &&
                    edge.return_relation ==
                        aburi::cir::VirtualReturnRelation::Covariant) {
                    covariant_edge = &edge;
                    break;
                }
            }
        } else if (const auto* direct =
                std::get_if<aburi::cir::EntityId>(&operands[0].data)) {
            resolved_callee = *direct;
        } else if (const auto* indirect =
                       std::get_if<ValueRef>(&operands[0].data)) {
            ConstEvalResult pointer = value_for_ref(*indirect, env);
            if (pointer.status != ConstEvalStatus::Constant ||
                !pointer.value.has_value()) {
                return pointer;
            }
            std::optional<ConstAddressValue> address =
                as_address(*pointer.value);
            if (!address.has_value() || !address->entity.valid() ||
                address->allocation_id != 0 || address->byte_offset != 0) {
                return make_unsupported(
                    "indirect call target is not a constant function address",
                    inst.loc);
            }
            resolved_callee = address->entity;
        }
        if (!resolved_callee.valid() || !file().valid(resolved_callee)) {
            return make_unsupported("indirect call is not a constant expression",
                                    inst.loc);
        }
        ConstEvalResult result = evaluate_direct_entity_call(
            resolved_callee,
            std::move(arg_values),
            inst.loc,
            is_void_type(file(), inst.result_type));
        if (!covariant_edge || result.status != ConstEvalStatus::Constant ||
            !result.value.has_value() ||
            result.value->kind != ConstValueKind::Address) {
            return result;
        }
        ConstAddressValue adjusted = result.value->address_value;
        for (aburi::cir::EntityId step : covariant_edge->covariance_path) {
            const aburi::cir::RecordFieldFact* field =
                file().field_fact(step);
            if (!field) {
                return make_unsupported(
                    "covariant virtual result has an invalid base path",
                    inst.loc);
            }
            adjusted.byte_offset += static_cast<int64_t>(field->offset);
            adjusted.subobjects.push_back(
                ConstSubobjectPathEntry{step, 0, false});
        }
        result.value = ConstValue::address_value_of(std::move(adjusted));
        return result;
    }

    ConstEvalResult activate_union_member_for_address(
        const ConstAddressValue& address,
        SrcLoc loc) {
        if (address.subobjects.empty()) {
            return ConstEvalResult::constant(ConstValue::void_value());
        }
        for (const ConstSubobjectPathEntry& step : address.subobjects) {
            if (step.is_array_element || !step.entity.valid() ||
                !file().valid(step.entity)) {
                continue;
            }
            aburi::cir::EntityId parent = file().entity(step.entity).parent;
            const aburi::cir::RecordFacts* parent_facts =
                parent.valid() ? file().record_facts(parent) : nullptr;
            if (!parent_facts ||
                parent_facts->kind != aburi::cir::RecordKind::Union) {
                continue;
            }
            if (step.containing_object_offset < 0 ||
                !state_.memory().set_active_union(
                    address.allocation_id,
                    static_cast<size_t>(step.containing_object_offset),
                    step.entity)) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constant evaluation could not activate union member",
                    loc);
            }
        }
        return ConstEvalResult::constant(ConstValue::void_value());
    }

    ConstEvalResult evaluate_construct_in_place(
        const aburi::cir::Inst& inst,
        std::unordered_map<uint64_t, ConstValue>& env) {
        std::vector<aburi::cir::Operand> operands = file().operands(inst.operands);
        if (operands.size() < 2) {
            return make_unsupported("construct_in_place is malformed",
                                    inst.loc);
        }
        const auto* place_ref = std::get_if<ValueRef>(&operands[0].data);
        const auto* constructor =
            std::get_if<aburi::cir::EntityId>(&operands[1].data);
        if (!place_ref || !constructor) {
            return make_unsupported("construct_in_place has invalid operands",
                                    inst.loc);
        }
        ConstEvalResult place = value_for_ref(*place_ref, env);
        if (place.status != ConstEvalStatus::Constant ||
            !place.value.has_value()) {
            return place;
        }
        std::optional<ConstAddressValue> this_address =
            as_address(*place.value);
        if (!this_address.has_value()) {
            return make_unsupported(
                "construct_in_place destination is not an address constant",
                inst.loc);
        }

        ConstEvalResult activated =
            activate_union_member_for_address(*this_address, inst.loc);
        if (activated.status != ConstEvalStatus::Constant) {
            return activated;
        }

        std::vector<ConstValue> arg_values;
        arg_values.reserve(operands.size() - 1);
        arg_values.push_back(ConstValue::address_value_of(*this_address));
        for (size_t index = 2; index < operands.size(); ++index) {
            const auto* value = std::get_if<ValueRef>(&operands[index].data);
            if (!value) {
                continue;
            }
            ConstEvalResult evaluated = value_for_ref(*value, env);
            if (evaluated.status != ConstEvalStatus::Constant ||
                !evaluated.value.has_value()) {
                return evaluated;
            }
            arg_values.push_back(*evaluated.value);
        }

        ConstEvalResult result = evaluate_direct_entity_call(
            *constructor,
            std::move(arg_values),
            inst.loc,
            /*allow_void_return=*/true);
        if (result.status != ConstEvalStatus::Constant) {
            return result;
        }
        return ConstEvalResult::constant(ConstValue::void_value());
    }

    bool is_constant_p_result(ValueRef result) const {
        if (!result.valid() || !file().valid(result.inst)) {
            return false;
        }
        const aburi::cir::Inst& inst = file().inst(result.inst);
        if (inst.kind != InstKind::BuiltinCall) {
            return false;
        }
        const aburi::cir::InstPayload& payload =
            file().payload(inst.payload_index);
        const auto* builtin =
            std::get_if<aburi::cir::BuiltinCallPayload>(&payload);
        return builtin && builtin->kind == BuiltinKind::CONSTANT_P;
    }

    ConstEvalResult evaluate_fragment(const aburi::cir::Fragment& fragment,
                                      ValueRef result) {
        if (!result.valid()) {
            return make_error(ConstEvalDiagCode::NullExpression,
                              "constant evaluation has no result value",
                              request_.loc);
        }
        if (fragment.empty()) {
            return apply_request_target(evaluate_inst(result.inst));
        }
        ConstEvalResult walked =
            apply_request_target(walk_blocks(fragment, result, {}));

        if (walked.status != ConstEvalStatus::Constant &&
            walked.status != ConstEvalStatus::Dependent &&
            is_constant_p_result(result)) {
            return apply_request_target(evaluate_inst(result.inst));
        }
        return walked;
    }

    ConstEvalResult evaluate_fragment_with_object_seeds(
        const aburi::cir::Fragment& fragment,
        ValueRef result,
        const std::vector<ConstEvalObjectSeed>& object_seeds) {
        for (const ConstEvalObjectSeed& seed : object_seeds) {
            ConstEvalResult seeded = seed_local_object(seed);
            if (seeded.status != ConstEvalStatus::Constant) {
                return seeded;
            }
        }
        return evaluate_fragment(fragment, result);
    }

    ConstEvalResult evaluate_frame(const aburi::cir::Fragment& fragment,
                                   std::vector<ConstValue> arg_values,
                                   bool allow_void_return = false) {

        return walk_blocks(fragment,
                           ValueRef{},
                           std::move(arg_values),
                           allow_void_return);
    }

    ConstEvalResult walk_blocks(const aburi::cir::Fragment& fragment,
                                ValueRef result,
                                std::vector<ConstValue> initial_args,
                                bool allow_void_return = false) {
        std::unordered_map<uint64_t, ConstValue> env;
        if (!file().valid(fragment.entry)) {
            return make_error(ConstEvalDiagCode::NullExpression,
                              "constant evaluation fragment has no entry block",
                              request_.loc);
        }

        BlockId current = fragment.entry;
        std::vector<ConstValue> incoming_args = std::move(initial_args);

        for (;;) {
            if (!state_.consume_step()) {
                return make_error(ConstEvalDiagCode::StepLimitExceeded,
                                  "constant evaluation step limit exceeded",
                                  request_.loc);
            }
            if (!file().valid(current)) {
                return make_error(ConstEvalDiagCode::NullExpression,
                                  "constant evaluation reached an invalid block",
                                  request_.loc);
            }

            demand_block_function_definitions(current);

            const aburi::cir::Block& block = file().block(current);

            for (InstId inst : block.instructions) {
                env.erase(inst_key(inst));
            }
            for (size_t index = 0; index < block.parameters.size(); ++index) {
                if (index >= incoming_args.size()) {
                    return make_unsupported(
                        "constant evaluation cannot bind block parameter",
                        request_.loc);
                }
                env[inst_key(block.parameters[index])] = incoming_args[index];
            }
            incoming_args.clear();

            for (InstId inst : block.instructions) {
                ConstEvalResult inst_result = evaluate_inst(inst, env);
                if (inst_result.status == ConstEvalStatus::Constant &&
                    inst_result.value.has_value()) {
                    env[inst_key(inst)] = *inst_result.value;
                    continue;
                }

                if (inst_result.status == ConstEvalStatus::Dependent) {
                    return inst_result;
                }

                if (inst_result.status == ConstEvalStatus::Error &&
                    !inst_result.diagnostics.empty() &&
                    inst_result.diagnostics.front().code ==
                        ConstEvalDiagCode::InvalidDeallocation) {
                    return inst_result;
                }

                if (inst_result.status == ConstEvalStatus::Unsupported ||
                    inst_result.status == ConstEvalStatus::NotConstant) {
                    continue;
                }
            }

            auto result_it = env.find(inst_key(result.inst));
            if (current == fragment.exit && result_it != env.end() &&
                block.terminator.kind == TerminatorKind::Invalid) {
                return ConstEvalResult::constant(result_it->second);
            }

            const aburi::cir::Terminator& term = block.terminator;
            switch (term.kind) {
                case TerminatorKind::Invalid:
                    if (result_it != env.end()) {
                        return ConstEvalResult::constant(result_it->second);
                    }

                    return value_for_ref(result, env);
                case TerminatorKind::Branch: {
                    auto args = evaluate_value_operands(term.operands, env);
                    if (!args.has_value()) {
                        return args.error();
                    }
                    incoming_args = std::move(args.value());
                    current = term.target;
                    break;
                }
                case TerminatorKind::CondBranch: {
                    std::vector<ValueRef> operands = file().value_operands(term.operands);
                    if (operands.empty()) {
                        return make_unsupported(
                            "constant evaluation conditional branch has no condition",
                            term.loc);
                    }
                    ConstEvalResult cond = value_for_ref(operands[0], env);
                    if (cond.status != ConstEvalStatus::Constant ||
                        !cond.value.has_value()) {
                        return cond;
                    }
                    bool condition = false;
                    if (!is_truthy(*cond.value, condition)) {
                        return make_unsupported(
                            "constant evaluation condition is not scalar",
                            term.loc);
                    }
                    incoming_args.clear();
                    for (size_t index = 1; index < operands.size(); ++index) {
                        ConstEvalResult arg = value_for_ref(operands[index], env);
                        if (arg.status != ConstEvalStatus::Constant ||
                            !arg.value.has_value()) {
                            return arg;
                        }
                        incoming_args.push_back(*arg.value);
                    }
                    current = condition ? term.target : term.false_target;
                    break;
                }
                case TerminatorKind::Return: {
                    auto args = evaluate_value_operands(term.operands, env);
                    if (!args.has_value()) {
                        return args.error();
                    }
                    if (!args->empty()) {
                        return ConstEvalResult::constant(args->front());
                    }
                    if (allow_void_return) {
                        return ConstEvalResult::constant(
                            ConstValue::void_value());
                    }
                    return make_unsupported(
                        "void return is not a constant expression value",
                        term.loc);
                }
                case TerminatorKind::Switch:
                    return make_unsupported(
                        "switch is not a constant expression",
                        term.loc);
                case TerminatorKind::IndirectBranch:
                    return make_unsupported(
                        "computed goto is not a constant expression",
                        term.loc);
                case TerminatorKind::AsmGoto:
                    return make_unsupported(
                        "asm goto is not a constant expression",
                        term.loc);
                case TerminatorKind::Unreachable:
                    return make_unsupported(
                        "constant evaluation reached unreachable code",
                        term.loc);
                case TerminatorKind::Throw:
                case TerminatorKind::Rethrow:

                    return make_unsupported(
                        "throwing an exception is not a constant expression",
                        term.loc);
                case TerminatorKind::Resume:
                    return make_unsupported(
                        "stack unwinding is not a constant expression",
                        term.loc);
                case TerminatorKind::CoroSuspend:
                case TerminatorKind::CoroEnd:

                    return make_unsupported(
                        "a coroutine suspension is not a constant expression",
                        term.loc);
            }
        }
    }

private:
    template <typename T>
    class Expected {
    public:
        Expected(T value) : value_(std::move(value)) {}
        Expected(ConstEvalResult error) : error_(std::move(error)) {}

        bool has_value() const { return value_.has_value(); }
        T& value() { return *value_; }
        const T& value() const { return *value_; }
        T* operator->() { return &*value_; }
        ConstEvalResult error() const { return *error_; }

    private:
        std::optional<T> value_;
        std::optional<ConstEvalResult> error_;
    };

    const aburi::cir::File& file() const {
        return *context_.file;
    }

    bool request_is_non_type_template_argument() const {
        return request_.mode.kind ==
            ConstEvalModeKind::CppNonTypeTemplateArgument;
    }

    ConstEvalResult apply_request_target(ConstEvalResult result) {
        if (!request_is_non_type_template_argument() ||
            !request_.target_type.valid() ||
            result.status != ConstEvalStatus::Constant ||
            !result.value.has_value()) {
            return result;
        }
        return convert_non_type_template_argument_to_target(*result.value);
    }

    ConstEvalResult convert_non_type_template_argument_to_target(
        const ConstValue& value) const {
        TypeId target = file().resolved_type(request_.target_type);
        if (!file().valid(target)) {
            return make_error(ConstEvalDiagCode::UnsupportedExpression,
                              "non-type template argument target type is invalid",
                              request_.loc);
        }

        TypeKind target_kind = file().type(target).kind;
        if (target_kind == TypeKind::Builtin) {
            const auto* builtin =
                std::get_if<aburi::cir::BuiltinTypePayload>(
                    &file().type_payload(target));
            if (builtin &&
                builtin->kind == aburi::cir::BuiltinTypeKind::NullPtr) {
                if (value.is_null(ConstNullKind::Nullptr)) {
                    return ConstEvalResult::constant(value);
                }
                if (value.kind == ConstValueKind::Integer &&
                    value.int_value.to_unsigned_u128() == 0) {
                    return ConstEvalResult::constant(
                        ConstValue::nullptr_value());
                }
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "non-type template argument is not a converted constant expression",
                    request_.loc);
            }
        }
        if (target_kind == TypeKind::Pointer ||
            target_kind == TypeKind::BlockPointer) {
            if (value.is_null(ConstNullKind::Nullptr)) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            if (value.is_null(ConstNullKind::Pointer) ||
                value.kind == ConstValueKind::Address) {
                return ConstEvalResult::constant(value);
            }
            return make_error(
                ConstEvalDiagCode::UnsupportedExpression,
                "non-type template argument is not a converted constant expression",
                request_.loc);
        }
        if (target_kind == TypeKind::MemberPointer) {
            if (value.is_null(ConstNullKind::Nullptr)) {
                return ConstEvalResult::constant(
                    ConstValue::null_member_pointer());
            }
            if (value.is_null(ConstNullKind::MemberPointer) ||
                value.kind == ConstValueKind::MemberPointer) {
                return ConstEvalResult::constant(value);
            }
            return make_error(
                ConstEvalDiagCode::UnsupportedExpression,
                "non-type template argument is not a converted constant expression",
                request_.loc);
        }

        if (is_bool_type(file(), target)) {
            if (value.kind == ConstValueKind::Boolean) {
                return ConstEvalResult::constant(value);
            }
            if (value.kind == ConstValueKind::Integer) {
                if (!const_int_value_representable(value.int_value,
                                                   1,
                                                   true)) {
                    return make_error(
                        ConstEvalDiagCode::UnsupportedExpression,
                        "non-type template argument conversion is narrowing",
                        request_.loc);
                }
                return ConstEvalResult::constant(
                    ConstValue::boolean(value.int_value.to_unsigned_u128() != 0));
            }
            return make_error(
                ConstEvalDiagCode::UnsupportedExpression,
                "non-type template argument is not a converted constant expression",
                request_.loc);
        }

        if (aburi::cir::is_integer_like_type(file(), target)) {
            aburi::cir::IntegerTypeShape shape =
                aburi::cir::integer_shape_for_type(file(), target);
            if (value.kind == ConstValueKind::Boolean) {
                ConstIntValue converted =
                    ConstIntValue::from_unsigned(value.bool_value ? 1 : 0,
                                                 shape.bit_width)
                        .cast(shape.bit_width, shape.is_unsigned);
                return ConstEvalResult::constant(ConstValue::integer(converted));
            }
            if (value.kind != ConstValueKind::Integer) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    value.kind == ConstValueKind::Floating
                        ? "non-type template argument conversion is narrowing"
                        : "non-type template argument is not a converted constant expression",
                    request_.loc);
            }
            if (!const_int_value_representable(value.int_value,
                                               shape.bit_width,
                                               shape.is_unsigned)) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "non-type template argument conversion is narrowing",
                    request_.loc);
            }
            return ConstEvalResult::constant(ConstValue::integer(
                value.int_value.cast(shape.bit_width, shape.is_unsigned)));
        }

        return ConstEvalResult::constant(value);
    }
    ConstEvalResult bytes_to_value(const std::vector<uint8_t>& bytes,
                                   TypeId type,
                                   SrcLoc loc) {
        TypeId resolved = file().resolved_type(type);
        if (!file().valid(resolved)) {
            return make_unsupported("loaded value has invalid type", loc);
        }
        if (file().type(resolved).kind == TypeKind::Array) {
            const auto* array =
                std::get_if<aburi::cir::ArrayTypePayload>(
                    &file().type_payload(resolved));
            if (!array || !array->size.has_value()) {
                return make_unsupported(
                    "array load has incomplete type in constant evaluation",
                    loc);
            }
            std::optional<size_t> element_size =
                aburi::cir::size_of_type(file(), array->element_type.type);
            if (!element_size.has_value()) {
                return make_unsupported(
                    "array element size is not supported in constant evaluation",
                    loc);
            }
            std::vector<ConstValue> elements;
            elements.reserve(*array->size);
            for (size_t index = 0; index < *array->size; ++index) {
                size_t element_offset = index * *element_size;
                if (element_offset + *element_size > bytes.size()) {
                    return make_unsupported(
                        "array load is outside object bounds in constant evaluation",
                        loc);
                }
                std::vector<uint8_t> element_bytes(
                    bytes.begin() + static_cast<int64_t>(element_offset),
                    bytes.begin() + static_cast<int64_t>(
                                        element_offset + *element_size));
                ConstEvalResult element =
                    bytes_to_value(element_bytes, array->element_type.type, loc);
                if (element.status != ConstEvalStatus::Constant ||
                    !element.value.has_value()) {
                    return element;
                }
                elements.push_back(*element.value);
            }
            return ConstEvalResult::constant(
                ConstValue::object(ConstObjectValueKind::Array,
                                   std::move(elements)));
        }
        if (file().type(resolved).kind == TypeKind::Record) {
            const aburi::cir::RecordFacts* facts =
                file().record_facts_for_type(resolved);
            if (!facts || facts->is_incomplete) {
                return make_unsupported(
                    "record load has incomplete type in constant evaluation",
                    loc);
            }
            std::vector<ConstValue> elements;
            for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (field.is_bitfield) {
                    return make_unsupported(
                        "bit-field object loads are not supported in constant evaluation",
                        loc);
                }
                std::optional<size_t> field_size =
                    aburi::cir::size_of_type(file(), field.type.type);
                if (!field_size.has_value() ||
                    field.offset + *field_size > bytes.size()) {
                    return make_unsupported(
                        "record field load is outside object bounds in constant evaluation",
                        loc);
                }
                std::vector<uint8_t> field_bytes(
                    bytes.begin() + static_cast<int64_t>(field.offset),
                    bytes.begin() + static_cast<int64_t>(
                                        field.offset + *field_size));
                ConstEvalResult field_value =
                    bytes_to_value(field_bytes, field.type.type, loc);
                if (field_value.status != ConstEvalStatus::Constant ||
                    !field_value.value.has_value()) {
                    return field_value;
                }
                elements.push_back(*field_value.value);
            }
            return ConstEvalResult::constant(
                ConstValue::object(ConstObjectValueKind::Record,
                                   std::move(elements)));
        }
        if (file().type(resolved).kind == TypeKind::Pointer ||
            file().type(resolved).kind == TypeKind::BlockPointer) {
            bool all_zero = std::all_of(bytes.begin(), bytes.end(),
                                        [](uint8_t byte) {
                                            return byte == 0;
                                        });
            if (all_zero) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            return make_unsupported(
                "non-null pointer bytes require a relocation in constant "
                "evaluation",
                loc);
        }
        if (aburi::cir::is_integer_like_type(file(), resolved)) {
            if (bytes.size() > 16) {
                return make_unsupported(
                    "loads wider than 128 bits are not supported in constant evaluation",
                    loc);
            }
            aburi::abi::ScalarBits raw_bits = aburi::abi::read_scalar_bits(
                bytes.data(), bytes.size(), file().target_info().endianness);
            unsigned __int128 raw =
                (static_cast<unsigned __int128>(raw_bits.high) << 64) |
                raw_bits.low;
            auto shape = aburi::cir::integer_shape_for_type(file(), resolved);
            if (is_bool_type(file(), resolved)) {
                return ConstEvalResult::constant(ConstValue::boolean(raw != 0));
            }
            return ConstEvalResult::constant(ConstValue::integer(
                ConstIntValue::from_bits128(raw, shape.bit_width,
                                            shape.is_unsigned)));
        }
        if (file().type(resolved).kind == TypeKind::Builtin) {
            const auto* builtin =
                std::get_if<aburi::cir::BuiltinTypePayload>(
                    &file().type_payload(resolved));
            if (builtin &&
                builtin->kind == aburi::cir::BuiltinTypeKind::NullPtr) {
                bool all_zero = true;
                for (uint8_t byte : bytes) {
                    all_zero = all_zero && byte == 0;
                }
                if (all_zero) {
                    return ConstEvalResult::constant(
                        ConstValue::nullptr_value());
                }
                return make_unsupported(
                    "nullptr_t loads from non-zero bytes are not supported",
                    loc);
            }
        }
        if (aburi::cir::is_floating_type(file(), resolved)) {
            aburi::cir::FloatingSemantics semantics =
                aburi::floating::semantics_for_type(file(), resolved);
            if (semantics != aburi::cir::FloatingSemantics::Invalid &&
                bytes.size() <= 16) {
                aburi::abi::ScalarBits bits = aburi::abi::read_scalar_bits(
                    bytes.data(), bytes.size(),
                    file().target_info().endianness);
                return ConstEvalResult::constant(ConstValue::floating(
                    floating_from_raw_bits(semantics, bits.low, bits.high)));
            }
            return make_unsupported(
                "floating load width is not supported in constant evaluation",
                loc);
        }
        if (file().type(resolved).kind == TypeKind::Pointer) {
            bool all_zero = true;
            for (uint8_t byte : bytes) {
                all_zero = all_zero && byte == 0;
            }
            if (all_zero) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            return make_unsupported(
                "pointer loads from evaluator memory are not supported", loc);
        }
        return make_unsupported(
            "loaded type is not supported in constant evaluation", loc);
    }

    std::optional<std::vector<uint8_t>> value_to_bytes(const ConstValue& value,
                                                       TypeId type) {
        std::optional<size_t> size;
        if (file().valid(type)) {
            size = aburi::cir::size_of_type(file(), type);
        }
        TypeId resolved = file().resolved_type(type);
        if (value.kind == ConstValueKind::Object) {
            if (!file().valid(resolved) || !size.has_value() ||
                !value.object_value) {
                return std::nullopt;
            }
            if (file().type(resolved).kind == TypeKind::Array) {
                const auto* array =
                    std::get_if<aburi::cir::ArrayTypePayload>(
                        &file().type_payload(resolved));
                if (!array || !array->size.has_value() ||
                    value.object_value->kind != ConstObjectValueKind::Array ||
                    value.object_value->elements.size() != *array->size) {
                    return std::nullopt;
                }
                std::optional<size_t> element_size =
                    aburi::cir::size_of_type(file(), array->element_type.type);
                if (!element_size.has_value()) {
                    return std::nullopt;
                }
                std::vector<uint8_t> out(*size, 0);
                for (size_t index = 0; index < *array->size; ++index) {
                    size_t element_offset = index * *element_size;
                    if (element_offset + *element_size > out.size()) {
                        return std::nullopt;
                    }
                    std::optional<std::vector<uint8_t>> element_bytes =
                        value_to_bytes(value.object_value->elements[index],
                                       array->element_type.type);
                    if (!element_bytes.has_value() ||
                        element_bytes->size() != *element_size) {
                        return std::nullopt;
                    }
                    std::copy(element_bytes->begin(),
                              element_bytes->end(),
                              out.begin() + static_cast<int64_t>(element_offset));
                }
                return out;
            }
            if (file().type(resolved).kind == TypeKind::Record) {
                const aburi::cir::RecordFacts* facts =
                    file().record_facts_for_type(resolved);
                if (!facts || facts->is_incomplete ||
                    value.object_value->kind != ConstObjectValueKind::Record) {
                    return std::nullopt;
                }
                bool sparse_union =
                    facts->kind == aburi::cir::RecordKind::Union &&
                    value.object_value->active_union_member.valid() &&
                    value.object_value->elements.size() == 1;
                std::vector<uint8_t> out(*size, 0);
                size_t element_index = 0;
                for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                    if (field.is_virtual_base_storage ||
                        field.is_flexible_array_member) {
                        continue;
                    }
                    if (sparse_union &&
                        field.entity !=
                            value.object_value->active_union_member) {
                        continue;
                    }
                    if (field.is_bitfield ||
                        element_index >= value.object_value->elements.size()) {
                        return std::nullopt;
                    }
                    std::optional<size_t> field_size =
                        aburi::cir::size_of_type(file(), field.type.type);
                    if (!field_size.has_value() ||
                        field.offset + *field_size > out.size()) {
                        return std::nullopt;
                    }
                    std::optional<std::vector<uint8_t>> field_bytes =
                        value_to_bytes(value.object_value->elements[element_index],
                                       field.type.type);
                    if (!field_bytes.has_value() ||
                        field_bytes->size() != *field_size) {
                        return std::nullopt;
                    }
                    std::copy(field_bytes->begin(),
                              field_bytes->end(),
                              out.begin() + static_cast<int64_t>(field.offset));
                    ++element_index;
                }
                if (element_index != value.object_value->elements.size()) {
                    return std::nullopt;
                }
                return out;
            }
            return std::nullopt;
        }
        switch (value.kind) {
            case ConstValueKind::Integer: {
                size_t width = size.value_or((value.int_value.bit_width + 7) / 8);
                if (width > 16) {
                    return std::nullopt;
                }
                unsigned __int128 raw = static_cast<unsigned __int128>(
                    value.int_value.to_signed_i128());
                std::vector<uint8_t> out(width, 0);
                aburi::abi::write_scalar_bits(
                    out.data(), width, static_cast<uint64_t>(raw),
                    static_cast<uint64_t>(raw >> 64),
                    file().target_info().endianness);
                return out;
            }
            case ConstValueKind::Boolean: {
                std::vector<uint8_t> out(size.value_or(1), 0);
                if (!out.empty()) {
                    out[0] = value.bool_value ? 1 : 0;
                }
                return out;
            }
            case ConstValueKind::Floating: {
                size_t width = size.value_or(8);
                if (width <= 16 && value.float_value.value.canonical()) {
                    std::vector<uint8_t> out(width, 0);
                    aburi::abi::write_scalar_bits(
                        out.data(), width,
                        value.float_value.value.low_bits,
                        value.float_value.value.high_bits,
                        file().target_info().endianness);
                    return out;
                }
                return std::nullopt;
            }
            case ConstValueKind::Null:
                return std::vector<uint8_t>(size.value_or(8), 0);
            default:
                return std::nullopt;
        }
    }

    const aburi::cir::ConstantStateFact* constant_state_at_offset(
        const aburi::cir::ConstantStateFact& root,
        int64_t byte_offset,
        TypeId want) {
        TypeId target = file().resolved_type(want);
        if (byte_offset < 0 || !file().valid(target)) {
            return nullptr;
        }
        const aburi::cir::ConstantStateFact* state = &root;
        int64_t remaining = byte_offset;
        while (state != nullptr) {
            TypeId current = file().resolved_type(state->type.type);
            if (!file().valid(current)) {
                return nullptr;
            }
            if (remaining == 0 && current == target) {
                return state;
            }
            if (file().type(current).kind == TypeKind::Array) {
                const auto* array = std::get_if<aburi::cir::ArrayTypePayload>(
                    &file().type_payload(current));
                if (!array) {
                    return nullptr;
                }
                std::optional<size_t> element_size =
                    aburi::cir::size_of_type(file(), array->element_type.type);
                if (!element_size.has_value() || *element_size == 0) {
                    return nullptr;
                }
                size_t index =
                    static_cast<size_t>(remaining) / *element_size;
                if (index >= state->elements.size()) {
                    return nullptr;
                }
                remaining -=
                    static_cast<int64_t>(index * *element_size);
                state = &state->elements[index];
                continue;
            }
            if (file().type(current).kind != TypeKind::Record) {
                return nullptr;
            }
            const aburi::cir::RecordFacts* facts =
                file().record_facts_for_type(current);
            if (!facts) {
                return nullptr;
            }
            bool is_union = facts->kind == aburi::cir::RecordKind::Union;
            bool sparse_union = is_union &&
                state->active_union_member.valid() &&
                state->elements.size() == 1;
            const aburi::cir::ConstantStateFact* next = nullptr;
            size_t element_index = 0;
            for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (sparse_union &&
                    field.entity != state->active_union_member) {
                    continue;
                }
                if (element_index >= state->elements.size()) {
                    break;
                }
                size_t selected_index = element_index++;

                std::optional<size_t> field_size =
                    aburi::cir::size_of_type(file(), field.type.type);
                if (field.is_bitfield || !field_size.has_value()) {
                    continue;
                }

                if (is_union && state->active_union_member != field.entity) {
                    continue;
                }
                int64_t start = static_cast<int64_t>(field.offset);
                if (remaining < start ||
                    remaining >= start + static_cast<int64_t>(*field_size)) {
                    continue;
                }
                next = &state->elements[selected_index];
                remaining -= start;
                break;
            }
            state = next;
        }
        return nullptr;
    }

    std::optional<uint64_t> materialize_string_literal(
        aburi::cir::InstId literal_id) {
        if (!literal_id.valid() || !file().valid(literal_id)) {
            return std::nullopt;
        }
        uint64_t key = inst_key(literal_id);
        auto found = string_literal_allocations_.find(key);
        if (found != string_literal_allocations_.end()) {
            return found->second;
        }
        const aburi::cir::Inst& literal_inst = file().inst(literal_id);
        if (literal_inst.kind != InstKind::StringLiteral) {
            return std::nullopt;
        }
        const auto* literal =
            std::get_if<aburi::cir::LiteralPayload>(
                &file().payload(literal_inst.payload_index));
        const auto* bytes = literal
            ? std::get_if<aburi::cir::LiteralByteArray>(&literal->value)
            : nullptr;
        if (!bytes) {
            return std::nullopt;
        }
        TypeId object_type =
            file().place_object_type(literal_inst.result_type);
        std::optional<size_t> object_size =
            aburi::cir::size_of_type(file(), object_type);
        if (!object_size.has_value() || *object_size < bytes->size()) {
            return std::nullopt;
        }

        uint64_t allocation = state_.memory().allocate(*object_size, false);
        std::vector<uint8_t> data(*object_size, 0);
        std::copy(bytes->begin(), bytes->end(), data.begin());
        if (!state_.memory().store_bytes(allocation, 0, data)) {
            return std::nullopt;
        }
        string_literal_allocations_.emplace(key, allocation);
        return allocation;
    }

    ConstEvalResult load_value_from_memory(ConstAddressValue address,
                                           TypeId type,
                                           SrcLoc loc) {
        if (address.allocation_id == 0 &&
            address.string_literal.valid()) {
            std::optional<uint64_t> allocation =
                materialize_string_literal(address.string_literal);
            if (!allocation.has_value()) {
                return make_unsupported(
                    "string literal object could not be materialized in "
                    "constant evaluation",
                    loc);
            }
            address.allocation_id = *allocation;
        }
        TypeId resolved = file().resolved_type(type);
        std::optional<size_t> size = aburi::cir::size_of_type(file(), type);
        if (!file().valid(resolved) || !size.has_value() ||
            address.byte_offset < 0 || address.allocation_id == 0) {
            return make_unsupported(
                "load target is not evaluator-owned memory", loc);
        }

        if (!address.subobjects.empty()) {
            aburi::cir::EntityId member =
                address.subobjects.back().entity;
            if (member.valid() && file().valid(member)) {
                aburi::cir::EntityId parent = file().entity(member).parent;
                const aburi::cir::RecordFacts* parent_facts =
                    parent.valid() ? file().record_facts(parent) : nullptr;
                if (parent_facts &&
                    parent_facts->kind == aburi::cir::RecordKind::Union) {
                    aburi::cir::EntityId active =
                        state_.memory().active_union_member(
                            address.allocation_id,
                            static_cast<size_t>(
                                address.containing_object_offset));
                    if (active.valid() && active != member) {
                        return make_error(
                            ConstEvalDiagCode::UnsupportedExpression,
                            "read of an inactive union member is not a constant expression",
                            loc);
                    }
                }
            }
        }

        if (address.bitfield_entity.valid()) {
            size_t storage_bytes =
                (static_cast<size_t>(address.bit_storage_bits) + 7) / 8;
            std::optional<std::vector<uint8_t>> stored =
                state_.memory().load_bytes(
                    address.allocation_id,
                    static_cast<size_t>(address.byte_offset),
                    storage_bytes);
            if (!stored.has_value() || address.bit_width == 0 ||
                address.bit_width > 64) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constant evaluation read an uninitialized bit-field",
                    loc);
            }
            uint64_t raw = aburi::abi::read_scalar_bits(
                stored->data(), stored->size(),
                file().target_info().endianness).low;
            uint64_t mask = address.bit_width == 64
                ? ~uint64_t{0}
                : ((uint64_t{1} << address.bit_width) - 1);
            raw = (raw >> address.bit_offset) & mask;
            aburi::cir::IntegerTypeShape shape =
                aburi::cir::integer_shape_for_type(file(), resolved);
            if (!shape.is_unsigned && address.bit_width < 64 &&
                (raw & (uint64_t{1} << (address.bit_width - 1))) != 0) {
                raw |= ~mask;
            }
            return ConstEvalResult::constant(ConstValue::integer(
                ConstIntValue::from_bits128(raw, shape.bit_width,
                                            shape.is_unsigned)));
        }

        if (file().type(resolved).kind == TypeKind::Array) {
            const auto* array =
                std::get_if<aburi::cir::ArrayTypePayload>(
                    &file().type_payload(resolved));
            if (!array || !array->size.has_value()) {
                return make_unsupported(
                    "array load has incomplete type in constant evaluation",
                    loc);
            }
            std::optional<size_t> element_size =
                aburi::cir::size_of_type(file(), array->element_type.type);
            if (!element_size.has_value()) {
                return make_unsupported(
                    "array element size is not supported in constant evaluation",
                    loc);
            }
            std::vector<ConstValue> elements;
            elements.reserve(*array->size);
            for (size_t index = 0; index < *array->size; ++index) {
                ConstAddressValue element_address = address;
                element_address.byte_offset +=
                    static_cast<int64_t>(index * *element_size);
                ConstEvalResult element =
                    load_value_from_memory(element_address,
                                           array->element_type.type,
                                           loc);
                if (element.status != ConstEvalStatus::Constant ||
                    !element.value.has_value()) {
                    return element;
                }
                elements.push_back(*element.value);
            }
            return ConstEvalResult::constant(
                ConstValue::object(ConstObjectValueKind::Array,
                                   std::move(elements)));
        }

        if (file().type(resolved).kind == TypeKind::Record) {
            const aburi::cir::RecordFacts* facts =
                file().record_facts_for_type(resolved);
            if (!facts || facts->is_incomplete) {
                return make_unsupported(
                    "record load has incomplete type in constant evaluation",
                    loc);
            }
            bool is_union =
                facts->kind == aburi::cir::RecordKind::Union;
            aburi::cir::EntityId active_union_member = is_union
                ? state_.memory().active_union_member(
                      address.allocation_id,
                      static_cast<size_t>(address.byte_offset))
                : aburi::cir::EntityId{};
            if (is_union && !active_union_member.valid()) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constant evaluation read a union with no active member",
                    loc);
            }
            std::vector<ConstValue> elements;
            for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (is_union && field.entity != active_union_member) {
                    continue;
                }
                ConstAddressValue field_address = address;
                field_address.containing_object_offset = address.byte_offset;
                field_address.byte_offset +=
                    static_cast<int64_t>(field.offset);
                field_address.subobjects.push_back(
                    ConstSubobjectPathEntry{
                        field.entity, 0, false, address.byte_offset});
                if (field.is_bitfield) {
                    field_address.bitfield_entity = field.entity;
                    field_address.bit_offset = field.bit_offset;
                    field_address.bit_width =
                        aburi::cir::bitfield_value_width(file(), field);
                    field_address.bit_storage_bits =
                        field.storage_size == 0 ? 32 : field.storage_size;
                }
                ConstEvalResult field_value =
                    load_value_from_memory(field_address,
                                           field.type.type,
                                           loc);
                if (field_value.status != ConstEvalStatus::Constant ||
                    !field_value.value.has_value()) {
                    return field_value;
                }
                elements.push_back(*field_value.value);
            }
            ConstValue object = ConstValue::object(
                ConstObjectValueKind::Record, std::move(elements));
            if (is_union) {
                object.object_value->active_union_member = active_union_member;
            }
            return ConstEvalResult::constant(std::move(object));
        }

        {

            const auto* builtin = std::get_if<aburi::cir::BuiltinTypePayload>(
                &file().type_payload(resolved));
            if (builtin &&
                builtin->kind == aburi::cir::BuiltinTypeKind::MetaInfo) {
                size_t byte_offset = static_cast<size_t>(address.byte_offset);
                if (std::optional<ConstValue> stored =
                        state_.memory().load_meta(address.allocation_id,
                                                  byte_offset,
                                                  *size)) {
                    return ConstEvalResult::constant(*stored);
                }
                std::optional<std::vector<uint8_t>> bytes =
                    state_.memory().load_bytes(address.allocation_id,
                                               byte_offset,
                                               *size);
                if (bytes.has_value()) {
                    bool all_zero = true;
                    for (uint8_t byte : *bytes) {
                        all_zero = all_zero && byte == 0;
                    }
                    if (all_zero) {
                        return ConstEvalResult::constant(
                            ConstValue::meta_info_null());
                    }
                }
                return make_unsupported(
                    "reflection load has no handle identity in constant "
                    "evaluation",
                    loc);
            }
        }

        bool is_reference = false;
        if (is_pointer_or_reference_type(file(), resolved, &is_reference)) {
            size_t byte_offset = static_cast<size_t>(address.byte_offset);
            if (std::optional<ConstAddressValue> stored =
                    state_.memory().load_address(address.allocation_id,
                                                 byte_offset,
                                                 *size)) {
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(*stored));
            }
            std::optional<std::vector<uint8_t>> bytes =
                state_.memory().load_bytes(address.allocation_id,
                                           byte_offset,
                                           *size);
            if (!bytes.has_value()) {
                return make_error(ConstEvalDiagCode::UnsupportedExpression,
                                  "constant evaluation read outside object bounds",
                                  loc);
            }
            bool all_zero = true;
            for (uint8_t byte : *bytes) {
                all_zero = all_zero && byte == 0;
            }
            if (!is_reference && all_zero) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            return make_unsupported(
                is_reference
                    ? "reference load has no address identity in constant evaluation"
                    : "pointer load has no address identity in constant evaluation",
                loc);
        }

        std::optional<std::vector<uint8_t>> bytes =
            state_.memory().load_bytes(
                address.allocation_id,
                static_cast<size_t>(address.byte_offset),
                *size);
        if (!bytes.has_value()) {
            return make_error(ConstEvalDiagCode::UnsupportedExpression,
                              "constant evaluation read outside object bounds",
                              loc);
        }
        return bytes_to_value(*bytes, type, loc);
    }

    ConstEvalResult store_value_to_memory(const ConstAddressValue& address,
                                          const ConstValue& value,
                                          TypeId type,
                                          SrcLoc loc) {
        TypeId resolved = file().resolved_type(type);
        std::optional<size_t> size = aburi::cir::size_of_type(file(), type);
        if (!file().valid(resolved) || !size.has_value() ||
            address.byte_offset < 0 || address.allocation_id == 0) {
            return make_unsupported(
                "store target is not evaluator-owned memory", loc);
        }

        ConstEvalResult activated =
            activate_union_member_for_address(address, loc);
        if (activated.status != ConstEvalStatus::Constant) {
            return activated;
        }

        if (value.kind == ConstValueKind::Object) {
            if (!value.object_value) {
                return make_unsupported(
                    "object store value is invalid in constant evaluation",
                    loc);
            }
            if (file().type(resolved).kind == TypeKind::Array) {
                const auto* array =
                    std::get_if<aburi::cir::ArrayTypePayload>(
                        &file().type_payload(resolved));
                if (!array || !array->size.has_value() ||
                    value.object_value->kind != ConstObjectValueKind::Array ||
                    value.object_value->elements.size() != *array->size) {
                    return make_unsupported(
                        "array object store shape is invalid in constant evaluation",
                        loc);
                }
                std::optional<size_t> element_size =
                    aburi::cir::size_of_type(file(), array->element_type.type);
                if (!element_size.has_value()) {
                    return make_unsupported(
                        "array element size is not supported in constant evaluation",
                        loc);
                }
                for (size_t index = 0; index < *array->size; ++index) {
                    ConstAddressValue element_address = address;
                    element_address.byte_offset +=
                        static_cast<int64_t>(index * *element_size);
                    ConstEvalResult stored =
                        store_value_to_memory(element_address,
                                              value.object_value->elements[index],
                                              array->element_type.type,
                                              loc);
                    if (stored.status != ConstEvalStatus::Constant) {
                        return stored;
                    }
                }
                return ConstEvalResult::constant(ConstValue::void_value());
            }
            if (file().type(resolved).kind == TypeKind::Record) {
                const aburi::cir::RecordFacts* facts =
                    file().record_facts_for_type(resolved);
                if (!facts || facts->is_incomplete ||
                    value.object_value->kind != ConstObjectValueKind::Record) {
                    return make_unsupported(
                        "record object store shape is invalid in constant evaluation",
                        loc);
                }
                bool sparse_union =
                    facts->kind == aburi::cir::RecordKind::Union &&
                    value.object_value->active_union_member.valid() &&
                    value.object_value->elements.size() == 1;
                if (facts->kind == aburi::cir::RecordKind::Union &&
                    value.object_value->active_union_member.valid() &&
                    !state_.memory().set_active_union(
                        address.allocation_id,
                        static_cast<size_t>(address.byte_offset),
                        value.object_value->active_union_member)) {
                    return make_error(
                        ConstEvalDiagCode::UnsupportedExpression,
                        "constant evaluation could not copy union member state",
                        loc);
                }
                size_t element_index = 0;
                for (const aburi::cir::RecordFieldFact& field : facts->fields) {
                    if (field.is_virtual_base_storage ||
                        field.is_flexible_array_member) {
                        continue;
                    }
                    if (sparse_union &&
                        field.entity !=
                            value.object_value->active_union_member) {
                        continue;
                    }
                    if (element_index >= value.object_value->elements.size()) {
                        return make_unsupported(
                            "record object store field is invalid in constant evaluation",
                            loc);
                    }
                    if (facts->kind == aburi::cir::RecordKind::Union &&
                        value.object_value->active_union_member.valid() &&
                        field.entity !=
                            value.object_value->active_union_member) {
                        ++element_index;
                        continue;
                    }
                    ConstAddressValue field_address = address;
                    field_address.containing_object_offset =
                        address.byte_offset;
                    field_address.byte_offset +=
                        static_cast<int64_t>(field.offset);
                    field_address.subobjects.push_back(
                        ConstSubobjectPathEntry{
                            field.entity, 0, false, address.byte_offset});
                    if (field.is_bitfield) {
                        field_address.bitfield_entity = field.entity;
                        field_address.bit_offset = field.bit_offset;
                        field_address.bit_width =
                            aburi::cir::bitfield_value_width(file(), field);
                        field_address.bit_storage_bits =
                            field.storage_size == 0 ? 32 : field.storage_size;
                    }
                    ConstEvalResult stored =
                        store_value_to_memory(field_address,
                                              value.object_value
                                                  ->elements[element_index],
                                              field.type.type,
                                              loc);
                    if (stored.status != ConstEvalStatus::Constant) {
                        return stored;
                    }
                    ++element_index;
                }
                if (element_index != value.object_value->elements.size()) {
                    return make_unsupported(
                        "record object store has extra elements in constant evaluation",
                        loc);
                }
                return ConstEvalResult::constant(ConstValue::void_value());
            }
        }

        if (value.kind == ConstValueKind::MetaInfo) {
            if (!state_.memory().store_meta(
                    address.allocation_id,
                    static_cast<size_t>(address.byte_offset),
                    *size,
                    value)) {
                return make_error(ConstEvalDiagCode::UnsupportedExpression,
                                  "constant evaluation wrote outside object bounds",
                                  loc);
            }
            return ConstEvalResult::constant(ConstValue::void_value());
        }

        if (address.bitfield_entity.valid()) {
            std::optional<int64_t> field_value = value.try_as_int64();
            size_t storage_bytes =
                (static_cast<size_t>(address.bit_storage_bits) + 7) / 8;
            if (!field_value.has_value() || address.bit_width == 0 ||
                address.bit_width > 64 || storage_bytes > 8) {
                return make_unsupported(
                    "bit-field value is not supported in constant evaluation",
                    loc);
            }
            std::optional<std::vector<uint8_t>> existing =
                state_.memory().load_bytes(
                    address.allocation_id,
                    static_cast<size_t>(address.byte_offset),
                    storage_bytes);
            std::vector<uint8_t> bytes =
                existing.value_or(std::vector<uint8_t>(storage_bytes, 0));
            uint64_t storage = aburi::abi::read_scalar_bits(
                bytes.data(), bytes.size(),
                file().target_info().endianness).low;
            uint64_t value_mask = address.bit_width == 64
                ? ~uint64_t{0}
                : ((uint64_t{1} << address.bit_width) - 1);
            uint64_t shifted_mask = value_mask << address.bit_offset;
            storage = (storage & ~shifted_mask) |
                ((static_cast<uint64_t>(*field_value) & value_mask)
                 << address.bit_offset);
            aburi::abi::write_scalar_bits(
                bytes.data(), bytes.size(), storage, 0,
                file().target_info().endianness);
            if (!state_.memory().store_bytes(
                    address.allocation_id,
                    static_cast<size_t>(address.byte_offset), bytes)) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constant evaluation wrote outside bit-field storage",
                    loc);
            }
            return ConstEvalResult::constant(ConstValue::void_value());
        }

        bool is_reference = false;
        if (is_pointer_or_reference_type(file(), resolved, &is_reference)) {
            if (value.kind == ConstValueKind::Address) {
                if (!state_.memory().store_address(
                        address.allocation_id,
                        static_cast<size_t>(address.byte_offset),
                        *size,
                        value.address_value)) {
                    return make_error(ConstEvalDiagCode::UnsupportedExpression,
                                      "constant evaluation wrote outside object bounds",
                                      loc);
                }
                return ConstEvalResult::constant(ConstValue::void_value());
            }
            if (!is_reference &&
                (value.is_null(ConstNullKind::Pointer) ||
                 value.is_null(ConstNullKind::Nullptr))) {
                std::vector<uint8_t> zeros(*size, 0);
                if (!state_.memory().store_bytes(
                        address.allocation_id,
                        static_cast<size_t>(address.byte_offset),
                        zeros)) {
                    return make_error(ConstEvalDiagCode::UnsupportedExpression,
                                      "constant evaluation wrote outside object bounds",
                                      loc);
                }
                return ConstEvalResult::constant(ConstValue::void_value());
            }
            return make_unsupported(
                is_reference
                    ? "reference store value has no address identity in constant evaluation"
                    : "pointer store value has no address identity in constant evaluation",
                loc);
        }

        std::optional<std::vector<uint8_t>> bytes =
            value_to_bytes(value, type);
        if (!bytes.has_value()) {
            return make_unsupported(
                "store value cannot be serialized in constant evaluation",
                loc);
        }
        if (!state_.memory().store_bytes(
                address.allocation_id,
                static_cast<size_t>(address.byte_offset),
                *bytes)) {
            return make_error(ConstEvalDiagCode::UnsupportedExpression,
                              "constant evaluation wrote outside object bounds",
                              loc);
        }
        return ConstEvalResult::constant(ConstValue::void_value());
    }

    ConstEvalResult seed_local_object(const ConstEvalObjectSeed& seed) {
        if (!seed.entity.valid() || !file().valid(seed.entity)) {
            return make_unsupported(
                "constant evaluation object seed has no entity",
                seed.loc);
        }
        TypeId type = seed.type.valid() ? seed.type : file().entity(seed.entity).type;
        std::optional<size_t> size = aburi::cir::size_of_type(file(), type);
        if (!size.has_value()) {
            return make_unsupported(
                "constant evaluation object seed has no constant size",
                seed.loc);
        }
        uint64_t key = entity_key(seed.entity);
        if (local_allocations_.find(key) != local_allocations_.end()) {
            return make_unsupported(
                "constant evaluation object seed aliases an existing local object",
                seed.loc);
        }
        uint64_t allocation = state_.memory().allocate(*size);
        local_allocations_[key] = allocation;
        ConstAddressValue address;
        address.entity = seed.entity;
        address.allocation_id = allocation;
        return store_value_to_memory(address, seed.value, type, seed.loc);
    }

    ConstEvalResult evaluate_inst(InstId inst_id,
                                  std::unordered_map<uint64_t, ConstValue>& env) {
        if (!state_.consume_step()) {
            return make_error(ConstEvalDiagCode::StepLimitExceeded,
                              "constant evaluation step limit exceeded",
                              request_.loc);
        }
        if (auto found = env.find(inst_key(inst_id)); found != env.end()) {
            return ConstEvalResult::constant(found->second);
        }
        if (!file().valid(inst_id)) {
            return make_error(ConstEvalDiagCode::NullExpression,
                              "cannot evaluate an invalid CIR instruction",
                              request_.loc);
        }

        const aburi::cir::Inst& inst = file().inst(inst_id);
        const aburi::cir::InstPayload& payload = file().payload(inst.payload_index);
        switch (inst.kind) {
            case InstKind::IntegerLiteral: {
                const auto* literal = std::get_if<aburi::cir::LiteralPayload>(&payload);
                const auto* value = literal
                    ? std::get_if<aburi::cir::IntegerValue>(&literal->value)
                    : nullptr;
                if (!value) {
                    return make_unsupported("integer literal payload is missing",
                                            inst.loc);
                }
                auto shape =
                    aburi::cir::integer_shape_for_type(file(), inst.result_type);
                return ConstEvalResult::constant(ConstValue::integer(
                    value->cast(shape.bit_width, shape.is_unsigned)));
            }
            case InstKind::BooleanLiteral: {
                const auto* literal = std::get_if<aburi::cir::LiteralPayload>(&payload);
                const auto* value =
                    literal ? std::get_if<bool>(&literal->value) : nullptr;
                if (!value) {
                    return make_unsupported("boolean literal payload is missing",
                                            inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::boolean(*value));
            }
            case InstKind::NullptrLiteral:
                return ConstEvalResult::constant(ConstValue::nullptr_value());
            case InstKind::FloatingLiteral: {
                const auto* literal = std::get_if<aburi::cir::LiteralPayload>(&payload);
                const auto* value =
                    literal
                        ? std::get_if<aburi::cir::FloatingValue>(&literal->value)
                        : nullptr;
                if (!value) {
                    return make_unsupported("floating literal payload is missing",
                                            inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::floating(*value));
            }
            case InstKind::CharacterLiteral: {
                const auto* literal = std::get_if<aburi::cir::LiteralPayload>(&payload);
                const auto* bytes =
                    literal ? std::get_if<aburi::cir::LiteralByteArray>(&literal->value)
                            : nullptr;
                if (!bytes) {
                    return make_unsupported("character literal payload is missing",
                                            inst.loc);
                }
                auto shape =
                    aburi::cir::integer_shape_for_type(file(), inst.result_type);
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_unsigned(bytes_to_u64(*bytes), shape.bit_width)
                        .cast(shape.bit_width, shape.is_unsigned)));
            }
            case InstKind::SizeofType: {
                auto type_ref = first_type_operand(file(), inst);
                if (!type_ref.has_value()) {
                    return make_unsupported("sizeof has no type operand", inst.loc);
                }
                auto size = aburi::cir::size_of_type(file(), type_ref->type);
                if (!size.has_value()) {
                    return make_unsupported(
                        "sizeof operand type is not complete for constant evaluation",
                        inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_unsigned(*size, 64)));
            }
            case InstKind::AlignofType: {
                auto type_ref = first_type_operand(file(), inst);
                if (!type_ref.has_value()) {
                    return make_unsupported("alignof has no type operand", inst.loc);
                }
                auto align = aburi::cir::align_of_type(file(), type_ref->type);
                if (!align.has_value()) {
                    return make_unsupported(
                        "alignof operand type is not complete for constant evaluation",
                        inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_unsigned(*align, 64)));
            }
            case InstKind::UnaryOp:
                return evaluate_unary(inst, payload, env);
            case InstKind::BinaryOp:
                return evaluate_binary(inst, payload, env);
            case InstKind::Cast:
                return evaluate_cast(inst, env);
            case InstKind::Param:
                return make_unsupported(
                    "function or block parameter is not bound in constant evaluation",
                    inst.loc);
            case InstKind::LocalPlace: {
                aburi::cir::EntityId entity = entity_operand_at(file(), inst, 0);
                if (!entity.valid()) {
                    return make_unsupported("local place has no entity", inst.loc);
                }
                uint64_t key = entity_key(entity);
                auto found = local_allocations_.find(key);
                uint64_t allocation = 0;
                if (found != local_allocations_.end()) {
                    allocation = found->second;
                } else {
                    std::optional<size_t> size =
                        aburi::cir::size_of_type(file(), file().entity(entity).type);
                    if (!size.has_value()) {
                        return make_unsupported(
                            "local object has no constant size", inst.loc);
                    }
                    allocation = state_.memory().allocate(*size);
                    local_allocations_[key] = allocation;
                }
                ConstAddressValue address;
                address.entity = entity;
                address.allocation_id = allocation;
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(address));
            }
            case InstKind::GlobalPlace: {
                aburi::cir::EntityId entity = entity_operand_at(file(), inst, 0);
                if (!entity.valid()) {
                    return make_unsupported("global place has no entity", inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::address(entity));
            }
            case InstKind::ComplexMake: {
                std::vector<aburi::cir::ValueRef> operands =
                    file().value_operands(inst.operands);
                if (operands.size() != 2) {
                    return make_unsupported("complex_make operand mismatch", inst.loc);
                }
                ConstEvalResult real = value_for_ref(operands[0], env);
                if (real.status != ConstEvalStatus::Constant) {
                    return real;
                }
                ConstEvalResult imag = value_for_ref(operands[1], env);
                if (imag.status != ConstEvalStatus::Constant) {
                    return imag;
                }
                aburi::cir::TypeId resolved =
                    file().resolved_type(inst.result_type);
                const auto* complex = file().valid(resolved)
                    ? std::get_if<aburi::cir::ComplexTypePayload>(
                          &file().type_payload(resolved))
                    : nullptr;
                if (complex && aburi::cir::is_integer_like_type(
                                   file(), complex->element_type.type)) {
                    aburi::cir::IntegerTypeShape shape =
                        aburi::cir::integer_shape_for_type(
                            file(), complex->element_type.type);
                    auto re = value_to_int(*real.value, shape);
                    auto im = value_to_int(*imag.value, shape);
                    if (!re || !im) {
                        return make_unsupported(
                            "complex_make operands are not integer constants",
                            inst.loc);
                    }
                    return ConstEvalResult::constant(
                        ConstValue::complex_integer(*re, *im));
                }
                aburi::cir::FloatingSemantics semantics = complex
                    ? aburi::floating::semantics_for_type(
                          file(), complex->element_type.type)
                    : aburi::cir::FloatingSemantics::Invalid;
                auto re = value_to_float(*real.value, semantics);
                auto im = value_to_float(*imag.value, semantics);
                if (!re || !im || floating_status_disqualifies(re.status) ||
                    floating_status_disqualifies(im.status)) {
                    return make_unsupported("complex_make operands are not constant",
                                            inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::complex(*re, *im));
            }
            case InstKind::ComplexReal:
            case InstKind::ComplexImag: {
                std::vector<aburi::cir::ValueRef> operands =
                    file().value_operands(inst.operands);
                if (operands.size() != 1) {
                    return make_unsupported("complex extraction operand mismatch",
                                            inst.loc);
                }
                ConstEvalResult operand = value_for_ref(operands[0], env);
                if (operand.status != ConstEvalStatus::Constant) {
                    return operand;
                }
                if (operand.value->kind != ConstValueKind::Complex) {
                    return make_unsupported("complex extraction operand is not complex",
                                            inst.loc);
                }
                if (operand.value->complex_value.has_integer_components) {
                    aburi::cir::IntegerTypeShape shape =
                        aburi::cir::integer_shape_for_type(
                            file(), inst.result_type);
                    ConstIntValue part = inst.kind == InstKind::ComplexImag
                        ? operand.value->complex_value.integer_imag
                        : operand.value->complex_value.integer_real;
                    return ConstEvalResult::constant(
                        ConstValue::integer(
                            part.cast(shape.bit_width, shape.is_unsigned)));
                }
                aburi::cir::FloatingValue part = inst.kind == InstKind::ComplexImag
                    ? operand.value->complex_value.imag
                    : operand.value->complex_value.real;
                aburi::cir::FloatingSemantics semantics =
                    aburi::floating::semantics_for_type(file(), inst.result_type);
                auto converted = aburi::floating::convert(part, semantics);
                if (!converted || floating_status_disqualifies(converted.status)) {
                    return make_unsupported(
                        "complex extraction cannot represent its real component",
                        inst.loc);
                }
                return ConstEvalResult::constant(
                    ConstValue::floating(*converted));
            }
            case InstKind::StringLiteral: {
                std::optional<uint64_t> allocation =
                    materialize_string_literal(inst_id);
                if (!allocation.has_value()) {
                    return make_unsupported(
                        "string literal object could not be materialized in "
                        "constant evaluation",
                        inst.loc);
                }
                ConstAddressValue address;
                address.allocation_id = *allocation;
                address.string_literal = inst_id;
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(address));
            }
            case InstKind::AddrOf: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.empty()) {
                    return make_unsupported("address-of has no operand", inst.loc);
                }
                return value_for_ref(operands[0], env);
            }
            case InstKind::Deref: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.empty()) {
                    return make_unsupported("dereference has no operand", inst.loc);
                }
                ConstEvalResult pointer = value_for_ref(operands[0], env);
                if (pointer.status != ConstEvalStatus::Constant ||
                    !pointer.value.has_value()) {
                    return pointer;
                }
                std::optional<ConstAddressValue> address = as_address(*pointer.value);
                if (!address.has_value()) {
                    return make_unsupported(
                        "dereference operand is not an address constant", inst.loc);
                }
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(*address));
            }
            case InstKind::FieldAddr: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.empty()) {
                    return make_unsupported("field address has no base", inst.loc);
                }
                ConstEvalResult base = value_for_ref(operands[0], env);
                if (base.status != ConstEvalStatus::Constant ||
                    !base.value.has_value()) {
                    return base;
                }
                std::optional<ConstAddressValue> address = as_address(*base.value);
                if (!address.has_value()) {
                    return make_unsupported(
                        "field base is not an address constant", inst.loc);
                }
                aburi::cir::EntityId field = entity_operand_at(file(), inst, 1);
                const aburi::cir::RecordFieldFact* fact = file().field_fact(field);
                if (!fact) {
                    return make_unsupported(
                        "field offset is unavailable in constant evaluation",
                        inst.loc);
                }
                int64_t containing_offset = address->byte_offset;
                address->byte_offset += static_cast<int64_t>(fact->offset);
                address->containing_object_offset = containing_offset;
                address->subobjects.push_back(
                    ConstSubobjectPathEntry{
                        field, 0, false, containing_offset});
                if (fact->is_bitfield) {
                    address->bitfield_entity = field;
                    address->bit_offset = fact->bit_offset;
                    address->bit_width = aburi::cir::bitfield_value_width(
                        file(), *fact);
                    address->bit_storage_bits =
                        fact->storage_size == 0 ? 32 : fact->storage_size;
                }
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(*address));
            }
            case InstKind::ArrayElementPlace: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.size() < 2) {
                    return make_unsupported("array element place is malformed",
                                            inst.loc);
                }
                ConstEvalResult base = value_for_ref(operands[0], env);
                if (base.status != ConstEvalStatus::Constant ||
                    !base.value.has_value()) {
                    return base;
                }
                ConstEvalResult index = value_for_ref(operands[1], env);
                if (index.status != ConstEvalStatus::Constant ||
                    !index.value.has_value()) {
                    return index;
                }
                std::optional<ConstAddressValue> address = as_address(*base.value);
                std::optional<int64_t> index_value = index.value->try_as_int64();
                if (!address.has_value() || !index_value.has_value()) {
                    return make_unsupported(
                        "array element base is not an address constant", inst.loc);
                }
                TypeId element =
                    file().place_object_type(inst.result_type);
                std::optional<size_t> element_size =
                    aburi::cir::size_of_type(file(), element);
                if (!element_size.has_value()) {
                    return make_unsupported(
                        "array element size is unavailable in constant evaluation",
                        inst.loc);
                }
                address->byte_offset +=
                    *index_value * static_cast<int64_t>(*element_size);
                address->subobjects.push_back(ConstSubobjectPathEntry{
                    {}, static_cast<uint64_t>(*index_value), true});
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(*address));
            }
            case InstKind::Load:
            case InstKind::LValueToRValue: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.empty()) {
                    return make_unsupported("load has no place operand", inst.loc);
                }
                ConstEvalResult place = value_for_ref(operands[0], env);
                if (place.status != ConstEvalStatus::Constant ||
                    !place.value.has_value()) {
                    return place;
                }
                std::optional<ConstAddressValue> address = as_address(*place.value);
                if (!address.has_value()) {
                    return make_unsupported(
                        "load target is not an address constant", inst.loc);
                }
                std::optional<size_t> size =
                    aburi::cir::size_of_type(file(), inst.result_type);
                if (!size.has_value() || address->byte_offset < 0) {
                    return make_unsupported(
                        "load size is unavailable in constant evaluation",
                        inst.loc);
                }

                if (address->entity.valid()) {
                    const aburi::cir::Entity& entity =
                        file().entity(address->entity);
                    if (entity.has_constant_value &&
                        address->byte_offset == 0 &&
                        address->subobjects.empty() &&
                        aburi::cir::is_integer_like_type(
                            file(), inst.result_type)) {
                        aburi::cir::IntegerTypeShape shape =
                            aburi::cir::integer_shape_for_type(
                                file(), inst.result_type);
                        return ConstEvalResult::constant(
                            ConstValue::integer(
                                entity.constant_integer_value.cast(
                                    shape.bit_width,
                                    shape.is_unsigned)));
                    }
                    if (entity.constant_state.valid() &&
                        file().valid(entity.constant_state)) {
                        const aburi::cir::ConstantStateFact* state =
                            &file().constant_state(entity.constant_state);
                        bool path_ok = true;
                        for (const ConstSubobjectPathEntry& step :
                             address->subobjects) {
                            const aburi::cir::ConstantStateFact* next = nullptr;
                            if (step.is_array_element) {
                                if (step.array_index < state->elements.size()) {
                                    next = &state->elements[step.array_index];
                                }
                            } else {
                                if (state->active_union_member.valid() &&
                                    state->active_union_member != step.entity) {
                                    return make_error(
                                        ConstEvalDiagCode::UnsupportedExpression,
                                        "read of an inactive union member is not a constant expression",
                                        inst.loc);
                                }
                                for (const aburi::cir::ConstantStateFact& child :
                                     state->elements) {
                                    if (child.subobject_entity == step.entity) {
                                        next = &child;
                                        break;
                                    }
                                }
                            }
                            if (!next) {
                                path_ok = false;
                                break;
                            }
                            state = next;
                        }
                        bool selected_subobject =
                            !address->subobjects.empty();
                        bool loads_complete_entity =
                            address->byte_offset == 0 &&
                            file().resolved_type(inst.result_type) ==
                                file().resolved_type(entity.type);
                        const aburi::cir::ConstantStateFact* selected =
                            path_ok &&
                                    (selected_subobject ||
                                     loads_complete_entity)
                                ? state
                                : nullptr;
                        if ((!selected ||
                             file().resolved_type(selected->type.type) !=
                                 file().resolved_type(inst.result_type)) &&
                            !address->bitfield_entity.valid()) {
                            if (const aburi::cir::ConstantStateFact* by_layout =
                                    constant_state_at_offset(
                                        file().constant_state(
                                            entity.constant_state),
                                        address->byte_offset,
                                        inst.result_type)) {
                                selected = by_layout;
                            }
                        }
                        if (selected) {
                            std::optional<ConstValue> durable =
                                const_value_from_constant_state(*selected);
                            if (durable.has_value()) {
                                return ConstEvalResult::constant(
                                    std::move(*durable));
                            }
                        }
                    }
                    bool evaluator_visible_abi_table =
                        entity.generated_symbol_role ==
                            aburi::cir::GeneratedSymbolRole::VTable ||
                        entity.generated_symbol_role ==
                            aburi::cir::GeneratedSymbolRole::ConstructionVTable;
                    bool evaluator_visible_initializer =
                        entity.decl_flags.is_constexpr ||
                        entity.has_constant_value ||
                        entity.object_origin ==
                            aburi::cir::EntityObjectOrigin::StringLiteral ||
                        evaluator_visible_abi_table;
                    if (evaluator_visible_initializer &&
                        entity.has_static_initializer &&
                        address->byte_offset >= 0) {
                        size_t byte_offset =
                            static_cast<size_t>(address->byte_offset);
                        for (const aburi::cir::StaticInitializerRelocation&
                                 relocation :
                             entity.static_initializer_relocations) {
                            if (relocation.offset == byte_offset &&
                                !relocation.block.valid() &&
                                !relocation.subtract_block.valid() &&
                                relocation.entity.valid()) {
                                return ConstEvalResult::constant(
                                    ConstValue::address(
                                        relocation.entity,
                                        relocation.addend));
                            }
                        }
                    }
                    if (evaluator_visible_initializer &&
                        entity.has_static_initializer &&
                        address->byte_offset >= 0) {
                        if (address->bitfield_entity.valid()) {
                            size_t storage_bytes =
                                (static_cast<size_t>(
                                     address->bit_storage_bits) + 7) / 8;
                            size_t storage_offset = static_cast<size_t>(
                                address->byte_offset);
                            if (storage_offset >
                                    entity.static_initializer_bytes.size() ||
                                storage_bytes >
                                    entity.static_initializer_bytes.size() -
                                        storage_offset ||
                                address->bit_width == 0 ||
                                address->bit_width > 64) {
                                return make_unsupported(
                                    "bit-field load is outside static initializer bytes",
                                    inst.loc);
                            }
                            uint64_t raw = aburi::abi::read_scalar_bits(
                                entity.static_initializer_bytes.data() +
                                    storage_offset,
                                storage_bytes,
                                file().target_info().endianness).low;
                            uint64_t mask = address->bit_width == 64
                                ? ~uint64_t{0}
                                : ((uint64_t{1} << address->bit_width) - 1);
                            raw = (raw >> address->bit_offset) & mask;
                            aburi::cir::IntegerTypeShape shape =
                                aburi::cir::integer_shape_for_type(
                                    file(), inst.result_type);
                            if (!shape.is_unsigned &&
                                address->bit_width < 64 &&
                                (raw & (uint64_t{1}
                                        << (address->bit_width - 1))) != 0) {
                                raw |= ~mask;
                            }
                            return ConstEvalResult::constant(
                                ConstValue::integer(
                                    ConstIntValue::from_bits128(
                                        raw, shape.bit_width,
                                        shape.is_unsigned)));
                        }
                        size_t byte_offset =
                            static_cast<size_t>(address->byte_offset);
                        size_t initializer_size =
                            entity.static_initializer_bytes.size();
                        if (byte_offset > initializer_size ||
                            *size > initializer_size - byte_offset) {
                            return make_unsupported(
                                "load target is outside static initializer bytes",
                                inst.loc);
                        }
                        size_t byte_end = byte_offset + *size;
                        for (const aburi::cir::StaticInitializerRelocation&
                                 relocation :
                             entity.static_initializer_relocations) {
                            if (relocation.offset >= byte_offset &&
                                relocation.offset < byte_end) {
                                return make_unsupported(
                                    "relocation-bearing static object loads are not supported in constant evaluation",
                                    inst.loc);
                            }
                        }
                        std::vector<uint8_t> bytes(
                            entity.static_initializer_bytes.begin() +
                                static_cast<int64_t>(byte_offset),
                            entity.static_initializer_bytes.begin() +
                                static_cast<int64_t>(byte_end));
                        return bytes_to_value(bytes, inst.result_type, inst.loc);
                    }

                    if (entity.decl_flags.is_constexpr &&
                        !address->subobjects.empty()) {
                        const ConstSubobjectPathEntry& last =
                            address->subobjects.back();
                        bool is_vptr = !last.is_array_element &&
                            last.entity.valid() && file().valid(last.entity) &&
                            file().entity(last.entity).name.valid() &&
                            file().name(file().entity(last.entity).name) ==
                                ".vptr";
                        const aburi::cir::RecordFacts* dynamic = is_vptr
                            ? file().record_facts_for_type(
                                  file().entity(address->entity).type)
                            : nullptr;
                        if (dynamic && dynamic->vtable_entity.valid()) {
                            size_t address_point =
                                dynamic->vtable_address_point;
                            size_t best_secondary_path = 0;
                            std::vector<aburi::cir::EntityId> object_path;
                            object_path.reserve(address->subobjects.size());
                            for (const ConstSubobjectPathEntry& step :
                                 address->subobjects) {
                                if (!step.is_array_element &&
                                    step.entity.valid() &&
                                    step.entity != last.entity) {
                                    object_path.push_back(step.entity);
                                }
                            }
                            for (const aburi::cir::RecordFacts::SecondaryVtable&
                                     secondary :
                                 dynamic->secondary_vtables) {
                                bool names_secondary =
                                    secondary.storage_path.size() <=
                                        object_path.size() &&
                                    std::equal(
                                        secondary.storage_path.begin(),
                                        secondary.storage_path.end(),
                                        object_path.begin());
                                if (names_secondary &&
                                    secondary.storage_path.size() >=
                                        best_secondary_path) {
                                    address_point =
                                        secondary.address_point_bytes;
                                    best_secondary_path =
                                        secondary.storage_path.size();
                                }
                            }
                            return ConstEvalResult::constant(
                                ConstValue::address(dynamic->vtable_entity,
                                                    static_cast<int64_t>(
                                                        address_point)));
                        }
                    }
                }
                if (address->allocation_id == 0 &&
                    !address->string_literal.valid()) {
                    bool deferred_static_member = false;
                    if (address->entity.valid() &&
                        file().valid(address->entity)) {
                        const aburi::cir::Entity& object =
                            file().entity(address->entity);
                        const aburi::cir::RecordFacts* owner_facts =
                            object.parent.valid() &&
                                    file().valid(object.parent)
                                ? file().record_facts(object.parent)
                                : nullptr;
                        deferred_static_member =
                            owner_facts &&
                            std::any_of(
                                owner_facts->static_data_members.begin(),
                                owner_facts->static_data_members.end(),
                                [&](const auto& member) {
                                    return member.entity ==
                                               address->entity &&
                                        member.has_in_class_initializer &&
                                        member.initializer_begin <
                                            member.initializer_end;
                                });
                    }
                    if (deferred_static_member) {
                        ConstEvalResult dependency =
                            ConstEvalResult::dependent(
                                "static object constant initializer is not "
                                "materialized");
                        dependency.dependency_entity = address->entity;
                        return dependency;
                    }
                    return make_unsupported(
                        "load target is not evaluator-owned memory", inst.loc);
                }
                return load_value_from_memory(*address,
                                              inst.result_type,
                                              inst.loc);
            }
            case InstKind::Store: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.size() < 2) {
                    return make_unsupported("store is malformed", inst.loc);
                }
                ConstEvalResult place = value_for_ref(operands[0], env);
                if (place.status != ConstEvalStatus::Constant ||
                    !place.value.has_value()) {
                    return place;
                }
                ConstEvalResult value = value_for_ref(operands[1], env);
                if (value.status != ConstEvalStatus::Constant ||
                    !value.value.has_value()) {
                    return value;
                }
                std::optional<ConstAddressValue> address = as_address(*place.value);
                if (!address.has_value() || address->allocation_id == 0) {
                    return make_unsupported(
                        "store target is not evaluator-owned memory", inst.loc);
                }
                TypeId value_type = file().valid(operands[1].inst)
                    ? file().inst(operands[1].inst).result_type
                    : TypeId{};
                return store_value_to_memory(*address,
                                             *value.value,
                                             value_type,
                                             inst.loc);
            }
            case InstKind::ZeroObject: {
                std::vector<ValueRef> operands = value_operands(file(), inst);
                if (operands.empty()) {
                    return make_unsupported("zero_object has no place", inst.loc);
                }
                ConstEvalResult place = value_for_ref(operands[0], env);
                if (place.status != ConstEvalStatus::Constant ||
                    !place.value.has_value()) {
                    return place;
                }
                std::optional<ConstAddressValue> address = as_address(*place.value);
                if (!address.has_value() || address->allocation_id == 0) {
                    return make_unsupported(
                        "zero_object target is not evaluator-owned memory",
                        inst.loc);
                }
                TypeId object = file().place_object_type(
                    file().valid(operands[0].inst)
                        ? file().inst(operands[0].inst).result_type
                        : TypeId{});
                std::optional<size_t> size = aburi::cir::size_of_type(file(), object);
                if (!size.has_value() || address->byte_offset < 0) {
                    return make_unsupported(
                        "zero_object size is unavailable in constant evaluation",
                        inst.loc);
                }
                std::vector<uint8_t> zeros(*size, 0);
                if (!state_.memory().store_bytes(
                        address->allocation_id,
                        static_cast<size_t>(address->byte_offset),
                        zeros)) {
                    return make_error(ConstEvalDiagCode::UnsupportedExpression,
                                      "constant evaluation zeroed outside object bounds",
                                      inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::void_value());
            }
            case InstKind::FunctionToPointer: {
                aburi::cir::EntityId entity = entity_operand_at(file(), inst, 0);
                if (!entity.valid()) {
                    return make_unsupported("function pointer has no entity",
                                            inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::address(entity));
            }
            case InstKind::NameRef:
            case InstKind::MemberPointerValue:
            case InstKind::DataMemberPointerPlace:
            case InstKind::MemberFunctionPointerCallee:
            case InstKind::MemberFunctionPointerThis:
            case InstKind::StackAlloc:
            case InstKind::AtomicLoad:
            case InstKind::AtomicStore:
            case InstKind::AtomicRmw:
            case InstKind::AtomicCmpXchg:
            case InstKind::AtomicFence:
            case InstKind::ComplexRealPlace:
            case InstKind::ComplexImagPlace:
            case InstKind::StackSave:
            case InstKind::StackRestore:
            case InstKind::VectorElementPlace:
            case InstKind::VectorExtract:
            case InstKind::Call:
                return evaluate_call(inst, env);
            case InstKind::ConstructInPlace:
                return evaluate_construct_in_place(inst, env);
            case InstKind::BuiltinCall:
                return evaluate_builtin_call(inst_id, inst, payload, env);
            case InstKind::ReflectValue: {
                const auto* reflect =
                    std::get_if<aburi::cir::ReflectPayload>(&payload);
                if (!reflect) {
                    return make_unsupported("reflect payload is missing",
                                            inst.loc);
                }
                std::vector<aburi::cir::Operand> operands =
                    file().operands(inst.operands);
                if (operands.size() != 1) {
                    return make_unsupported("reflect operand is malformed",
                                            inst.loc);
                }
                if (reflect->kind == aburi::cir::MetaInfoKind::Type) {
                    const auto* type =
                        std::get_if<aburi::cir::TypeRef>(&operands[0].data);
                    if (!type || !type->type.valid()) {
                        return make_unsupported(
                            "reflected type operand is invalid", inst.loc);
                    }
                    return ConstEvalResult::constant(
                        ConstValue::meta_info_type(*type));
                }
                const auto* entity =
                    std::get_if<aburi::cir::EntityId>(&operands[0].data);
                if (!entity || !entity->valid()) {
                    return make_unsupported(
                        "reflected entity operand is invalid", inst.loc);
                }
                return ConstEvalResult::constant(
                    ConstValue::meta_info_entity(reflect->kind, *entity));
            }
            case InstKind::Destroy:
                return evaluate_destroy(inst, env);
            case InstKind::LifetimeStart:
            case InstKind::LifetimeEnd:

                return ConstEvalResult::constant(ConstValue::void_value());
            case InstKind::LabelAddress:
            case InstKind::InlineAsm:
            case InstKind::VaStart:
            case InstKind::VaArg:
            case InstKind::VaEnd:
            case InstKind::VaCopy:
            case InstKind::DependentCall:
            case InstKind::DependentRegion:
                return make_unsupported(
                    std::string(file().format_inst(inst_id)) +
                        " is not supported by the CIR constant evaluator yet",
                    inst.loc);
            case InstKind::Error:
            case InstKind::Invalid:
                return make_error(ConstEvalDiagCode::UnsupportedExpression,
                                  "cannot evaluate invalid CIR instruction",
                                  inst.loc);
        }
        return make_unsupported("CIR instruction is not a constant expression",
                                inst.loc);
    }

    ConstEvalResult evaluate_builtin_call(InstId inst_id,
                                          const aburi::cir::Inst& inst,
                                          const aburi::cir::InstPayload& payload,
                                          std::unordered_map<uint64_t, ConstValue>& env) {
        const auto* builtin =
            std::get_if<aburi::cir::BuiltinCallPayload>(&payload);
        if (!builtin) {
            return make_unsupported("builtin call payload is missing", inst.loc);
        }
        if (builtin->kind == BuiltinKind::CONSTANT_P) {

            bool is_const = false;
            if (inst.operands.count != 0) {
                is_const = evaluate_value_operands(inst.operands, env).has_value();
            }
            auto shape =
                aburi::cir::integer_shape_for_type(file(), inst.result_type);
            return ConstEvalResult::constant(ConstValue::integer(
                ConstIntValue::from_signed(is_const ? 1 : 0, shape.bit_width)
                    .cast(shape.bit_width, shape.is_unsigned)));
        }

        if (builtin->kind == BuiltinKind::EXPECT ||
            builtin->kind == BuiltinKind::EXPECT_WITH_PROBABILITY) {

            auto args = evaluate_value_operands(inst.operands, env);
            if (!args.has_value()) {
                return args.error();
            }
            if (args->empty()) {
                return make_unsupported(
                    "__builtin_expect requires an operand", inst.loc);
            }
            return ConstEvalResult::constant(args.value()[0]);
        }

        if (builtin->kind == BuiltinKind::FABS ||
            builtin->kind == BuiltinKind::FABSF ||
            builtin->kind == BuiltinKind::FABSL) {
            auto args = evaluate_value_operands(inst.operands, env);
            if (!args.has_value()) {
                return args.error();
            }
            aburi::cir::FloatingSemantics semantics =
                aburi::floating::semantics_for_type(file(), inst.result_type);
            if (args->size() != 1 ||
                semantics == aburi::cir::FloatingSemantics::Invalid) {
                return make_unsupported(
                    builtin->name + " has invalid constant operands",
                    inst.loc);
            }
            aburi::floating::FloatResult value =
                value_to_float(args.value()[0], semantics);
            if (!value || floating_status_disqualifies(value.status)) {
                return make_unsupported(
                    builtin->name + " operand is not a floating constant",
                    inst.loc);
            }
            if (aburi::floating::is_negative(*value)) {
                value.value = aburi::floating::negate(*value);
            }
            return ConstEvalResult::constant(
                ConstValue::floating(value.value));
        }

        if (builtin->kind == BuiltinKind::ASSUME_ALIGNED ||
            builtin->kind == BuiltinKind::LAUNDER) {

            auto args = evaluate_value_operands(inst.operands, env);
            if (!args.has_value()) {
                return args.error();
            }
            size_t maximum_operands =
                builtin->kind == BuiltinKind::LAUNDER ? 1 : 2;
            if (args->empty() || args->size() > maximum_operands) {
                return make_unsupported(
                    builtin->name + " has invalid constant operands",
                    inst.loc);
            }
            return ConstEvalResult::constant(args.value()[0]);
        }

        if (builtin->kind == BuiltinKind::STRLEN) {
            auto args = evaluate_value_operands(inst.operands, env);
            if (!args.has_value()) {
                return args.error();
            }
            if (args->size() != 1) {
                return make_unsupported(
                    "__builtin_strlen requires one pointer operand", inst.loc);
            }
            std::optional<ConstAddressValue> cursor =
                as_address(args.value()[0]);
            if (!cursor.has_value() || address_is_null_base(*cursor)) {
                return make_error(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "__builtin_strlen cannot read through a null pointer",
                    inst.loc);
            }

            uint64_t length = 0;
            TypeId char_type =
                file().builtin_type(aburi::cir::BuiltinTypeKind::Char);
            for (;;) {

                if (!state_.consume_step()) {
                    return make_error(
                        ConstEvalDiagCode::StepLimitExceeded,
                        "constant evaluation step limit exceeded",
                        inst.loc);
                }
                ConstEvalResult character =
                    load_value_from_memory(*cursor, char_type, inst.loc);
                if (character.status != ConstEvalStatus::Constant ||
                    !character.value.has_value()) {
                    return character;
                }
                std::optional<int64_t> code_unit =
                    character.value->try_as_int64();
                if (!code_unit.has_value()) {
                    return make_unsupported(
                        "__builtin_strlen character is not an integer constant",
                        inst.loc);
                }
                if (*code_unit == 0) {
                    break;
                }
                if (cursor->byte_offset ==
                    std::numeric_limits<int64_t>::max()) {
                    return make_error(
                        ConstEvalDiagCode::UnsupportedExpression,
                        "__builtin_strlen exceeded evaluator address range",
                        inst.loc);
                }
                ++cursor->byte_offset;
                ++length;
                if (!cursor->subobjects.empty() &&
                    cursor->subobjects.back().is_array_element) {
                    ++cursor->subobjects.back().array_index;
                }
            }

            auto shape =
                aburi::cir::integer_shape_for_type(file(), inst.result_type);
            return ConstEvalResult::constant(ConstValue::integer(
                ConstIntValue::from_bits128(
                    static_cast<unsigned __int128>(length),
                    shape.bit_width,
                    shape.is_unsigned)));
        }

        if (builtin->kind == BuiltinKind::BIT_CAST) {
            std::vector<aburi::cir::Operand> operands =
                file().operands(inst.operands);
            if (operands.size() != 1) {
                return make_unsupported(
                    "__builtin_bit_cast requires one value operand", inst.loc);
            }
            const auto* source_ref =
                std::get_if<ValueRef>(&operands.front().data);
            if (!source_ref || !file().valid(source_ref->inst)) {
                return make_unsupported(
                    "__builtin_bit_cast source operand is malformed", inst.loc);
            }
            TypeId source_type = file().inst(source_ref->inst).result_type;
            aburi::cir::TypeRef target_ref = builtin->type_operand.type.valid()
                ? builtin->type_operand
                : file().type_ref(inst.result_type);
            if (has_constexpr_unknown_representation(
                    file(), file().type_ref(source_type)) ||
                has_constexpr_unknown_representation(file(), target_ref)) {
                return make_unsupported(
                    "__builtin_bit_cast involving a type with constexpr-unknown "
                    "representation is not a constant expression",
                    inst.loc);
            }
            auto args = evaluate_value_operands(inst.operands, env);
            if (!args.has_value()) {
                return args.error();
            }
            if (args->size() != 1) {
                return make_unsupported(
                    "__builtin_bit_cast requires one constant operand", inst.loc);
            }
            std::optional<std::vector<uint8_t>> bytes =
                value_to_bytes(args.value()[0], source_type);
            if (!bytes.has_value()) {
                return make_unsupported(
                    "__builtin_bit_cast source object representation is not "
                    "available in constant evaluation",
                    inst.loc);
            }
            return bytes_to_value(*bytes, inst.result_type, inst.loc);
        }

        switch (builtin->kind) {
            case BuiltinKind::METAFN_QUERY_INT:
            case BuiltinKind::METAFN_QUERY_INFO:
            case BuiltinKind::METAFN_NAME_DATA:
            case BuiltinKind::METAFN_NAME_SIZE:
            case BuiltinKind::METAFN_RANGE_COUNT:
            case BuiltinKind::METAFN_RANGE_AT: {
                auto operands = evaluate_value_operands(inst.operands, env);
                if (!operands.has_value()) {
                    return operands.error();
                }
                return evaluate_metafunction(builtin->kind,
                                             file(),
                                             context_.mutable_file,
                                             state_.memory(),
                                             operands.value(),
                                             inst.result_type,
                                             inst.loc);
            }
            case BuiltinKind::IS_CONSTANT_EVALUATED:

                return ConstEvalResult::constant(
                    bool_result_for_type(file(), inst.result_type, true));
            default:
                break;
        }

        enum class BitOp {
            Clz,
            Ctz,
            Popcount,
            Parity,
            Ffs,
            Bswap,
        };
        std::optional<BitOp> bit_op;
        uint16_t width = 0;
        const uint16_t target_long_width = static_cast<uint16_t>(
            file().target_info_ptr() ? file().target_info_ptr()->long_width : 64);
        switch (builtin->kind) {
            case BuiltinKind::CLZ:
                bit_op = BitOp::Clz;
                width = 32;
                break;
            case BuiltinKind::CLZL:
                bit_op = BitOp::Clz;
                width = target_long_width;
                break;
            case BuiltinKind::CLZLL:
                bit_op = BitOp::Clz;
                width = 64;
                break;
            case BuiltinKind::CLZG:
                bit_op = BitOp::Clz;
                break;
            case BuiltinKind::CTZ:
                bit_op = BitOp::Ctz;
                width = 32;
                break;
            case BuiltinKind::CTZL:
                bit_op = BitOp::Ctz;
                width = target_long_width;
                break;
            case BuiltinKind::CTZLL:
                bit_op = BitOp::Ctz;
                width = 64;
                break;
            case BuiltinKind::CTZG:
                bit_op = BitOp::Ctz;
                break;
            case BuiltinKind::POPCOUNT:
                bit_op = BitOp::Popcount;
                width = 32;
                break;
            case BuiltinKind::POPCOUNTL:
                bit_op = BitOp::Popcount;
                width = target_long_width;
                break;
            case BuiltinKind::POPCOUNTLL:
                bit_op = BitOp::Popcount;
                width = 64;
                break;
            case BuiltinKind::POPCOUNTG:
                bit_op = BitOp::Popcount;
                break;
            case BuiltinKind::PARITY:
                bit_op = BitOp::Parity;
                width = 32;
                break;
            case BuiltinKind::PARITYL:
                bit_op = BitOp::Parity;
                width = target_long_width;
                break;
            case BuiltinKind::PARITYLL:
                bit_op = BitOp::Parity;
                width = 64;
                break;
            case BuiltinKind::FFS:
                bit_op = BitOp::Ffs;
                width = 32;
                break;
            case BuiltinKind::FFSL:
                bit_op = BitOp::Ffs;
                width = target_long_width;
                break;
            case BuiltinKind::FFSLL:
                bit_op = BitOp::Ffs;
                width = 64;
                break;
            case BuiltinKind::BSWAP16:
                bit_op = BitOp::Bswap;
                width = 16;
                break;
            case BuiltinKind::BSWAP32:
                bit_op = BitOp::Bswap;
                width = 32;
                break;
            case BuiltinKind::BSWAP64:
                bit_op = BitOp::Bswap;
                width = 64;
                break;
            default:
                break;
        }
        if (!bit_op.has_value()) {
            return make_unsupported(
                std::string(file().format_inst(inst_id)) +
                    " is not supported by the CIR constant evaluator yet",
                inst.loc);
        }

        auto args = evaluate_value_operands(inst.operands, env);
        if (!args.has_value()) {
            return args.error();
        }
        bool generic_count_zero =
            builtin->kind == BuiltinKind::CLZG ||
            builtin->kind == BuiltinKind::CTZG;
        bool generic_width =
            generic_count_zero ||
            builtin->kind == BuiltinKind::POPCOUNTG;
        bool valid_count =
            generic_count_zero
            ? (args->size() == 1 || args->size() == 2)
            : args->size() == 1;
        bool integer_operand =
            !args->empty() &&
            (args.value()[0].kind == ConstValueKind::Integer ||
             (generic_width &&
              args.value()[0].kind == ConstValueKind::Boolean));
        if (!valid_count || !integer_operand ||
            (args->size() == 2 &&
             args.value()[1].kind != ConstValueKind::Integer)) {
            return make_unsupported(
                "bit builtin has invalid constant operands", inst.loc);
        }
        if (generic_width && width == 0) {
            width = args.value()[0].kind == ConstValueKind::Boolean
                ? 1
                : args.value()[0].int_value.bit_width;
        }

        const unsigned __int128 mask = width >= 128
            ? ~static_cast<unsigned __int128>(0)
            : ((static_cast<unsigned __int128>(1) << width) - 1);
        const unsigned __int128 bits = args.value()[0].kind ==
                ConstValueKind::Boolean
            ? static_cast<unsigned __int128>(
                  args.value()[0].bool_value ? 1 : 0)
            : args.value()[0].int_value.to_unsigned_u128() & mask;
        auto count_set = [](unsigned __int128 value) {
            int64_t count = 0;
            while (value != 0) {
                count += static_cast<int64_t>(value & 1);
                value >>= 1;
            }
            return count;
        };

        int64_t result = 0;
        switch (*bit_op) {
            case BitOp::Clz: {
                if (bits == 0) {
                    if (generic_count_zero && args->size() == 2) {
                        result =
                            args.value()[1].int_value.to_signed_i64();
                        break;
                    }
                    return make_unsupported(
                        "__builtin_clz family is undefined for zero", inst.loc);
                }
                int64_t highest = -1;
                for (uint16_t bit = 0; bit < width; ++bit) {
                    if ((bits >> bit) & 1) {
                        highest = bit;
                    }
                }
                result = width - 1 - highest;
                break;
            }
            case BitOp::Ctz: {
                if (bits == 0) {
                    if (generic_count_zero && args->size() == 2) {
                        result =
                            args.value()[1].int_value.to_signed_i64();
                        break;
                    }
                    return make_unsupported(
                        "__builtin_ctz family is undefined for zero", inst.loc);
                }
                uint16_t lowest = 0;
                while (((bits >> lowest) & 1) == 0) {
                    ++lowest;
                }
                result = lowest;
                break;
            }
            case BitOp::Popcount:
                result = count_set(bits);
                break;
            case BitOp::Parity:
                result = count_set(bits) & 1;
                break;
            case BitOp::Ffs:
                if (bits == 0) {
                    result = 0;
                } else {
                    uint16_t lowest = 0;
                    while (((bits >> lowest) & 1) == 0) {
                        ++lowest;
                    }
                    result = lowest + 1;
                }
                break;
            case BitOp::Bswap: {
                unsigned __int128 swapped = 0;
                for (uint16_t byte = 0; byte < width / 8; ++byte) {
                    swapped =
                        (swapped << 8) | ((bits >> (byte * 8)) & 0xff);
                }
                auto shape =
                    aburi::cir::integer_shape_for_type(file(), inst.result_type);
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_bits128(swapped, width, true)
                        .cast(shape.bit_width, shape.is_unsigned)));
            }
        }

        auto shape =
            aburi::cir::integer_shape_for_type(file(), inst.result_type);
        return ConstEvalResult::constant(ConstValue::integer(
            ConstIntValue::from_signed(result, shape.bit_width)
                .cast(shape.bit_width, shape.is_unsigned)));
    }

    ConstEvalResult evaluate_destroy(
        const aburi::cir::Inst& inst,
        std::unordered_map<uint64_t, ConstValue>& env) {
        std::vector<aburi::cir::Operand> operands = file().operands(inst.operands);
        if (operands.empty()) {
            return make_unsupported("destroy has no place operand", inst.loc);
        }
        const aburi::cir::EntityId* destructor = operands.size() > 1
            ? std::get_if<aburi::cir::EntityId>(&operands[1].data)
            : nullptr;
        if (!destructor || !destructor->valid()) {

            return ConstEvalResult::constant(ConstValue::void_value());
        }
        const auto* place_ref = std::get_if<ValueRef>(&operands[0].data);
        if (!place_ref) {
            return make_unsupported("destroy has an invalid place operand",
                                    inst.loc);
        }
        ConstEvalResult place = value_for_ref(*place_ref, env);
        if (place.status != ConstEvalStatus::Constant ||
            !place.value.has_value()) {
            return place;
        }
        std::optional<ConstAddressValue> this_address = as_address(*place.value);
        if (!this_address.has_value()) {
            return make_unsupported(
                "destroy target is not an address constant", inst.loc);
        }
        std::vector<ConstValue> arg_values;
        arg_values.push_back(ConstValue::address_value_of(*this_address));
        ConstEvalResult result = evaluate_direct_entity_call(
            *destructor, std::move(arg_values), inst.loc,
            /*allow_void_return=*/true);
        if (result.status != ConstEvalStatus::Constant) {
            return result;
        }
        return ConstEvalResult::constant(ConstValue::void_value());
    }

public:
    ConstEvalResult apply_transient_allocation_rules(ConstEvalResult result) {
        if (result.status != ConstEvalStatus::Constant) {
            return result;
        }
        if (result.value.has_value() &&
            value_references_dynamic_allocation(*result.value)) {
            return make_error(
                ConstEvalDiagCode::DynamicAllocationEscaped,
                "pointer to constexpr-allocated memory escapes the constant "
                "evaluation",
                request_.loc);
        }
        if (state_.memory().live_dynamic_count() > 0) {
            return make_error(
                ConstEvalDiagCode::DynamicAllocationLeaked,
                "constexpr allocation was not deallocated within the constant "
                "evaluation",
                request_.loc);
        }
        return result;
    }

private:
    bool value_references_dynamic_allocation(const ConstValue& value) const {
        if (value.kind == ConstValueKind::Address) {
            return value.address_value.allocation_id != 0 &&
                   state_.memory().is_dynamic_allocation(
                       value.address_value.allocation_id);
        }
        if (value.kind == ConstValueKind::Object && value.object_value) {
            for (const ConstValue& element : value.object_value->elements) {
                if (value_references_dynamic_allocation(element)) {
                    return true;
                }
            }
        }
        return false;
    }

    ConstEvalResult value_for_ref(ValueRef ref,
                                  std::unordered_map<uint64_t, ConstValue>& env) {
        if (!ref.valid()) {
            return make_error(ConstEvalDiagCode::NullExpression,
                              "constant evaluation encountered an invalid value",
                              request_.loc);
        }
        if (auto found = env.find(inst_key(ref.inst)); found != env.end()) {
            return ConstEvalResult::constant(found->second);
        }
        return evaluate_inst(ref.inst, env);
    }

    Expected<std::vector<ConstValue>> evaluate_value_operands(
        aburi::cir::OperandRange range,
        std::unordered_map<uint64_t, ConstValue>& env) {
        std::vector<ConstValue> out;
        std::vector<ValueRef> operands = file().value_operands(range);
        out.reserve(operands.size());
        for (ValueRef operand : operands) {
            ConstEvalResult result = value_for_ref(operand, env);
            if (result.status != ConstEvalStatus::Constant ||
                !result.value.has_value()) {
                return result;
            }
            out.push_back(*result.value);
        }
        return out;
    }

    ConstEvalResult evaluate_unary(
        const aburi::cir::Inst& inst,
        const aburi::cir::InstPayload& payload,
        std::unordered_map<uint64_t, ConstValue>& env) {
        const auto* descriptor = std::get_if<aburi::cir::UnaryOpDescriptor>(&payload);
        std::vector<ValueRef> operands = value_operands(file(), inst);
        if (!descriptor || operands.empty()) {
            return make_unsupported("unary operator payload is malformed", inst.loc);
        }
        ConstEvalResult operand = value_for_ref(operands[0], env);
        if (operand.status != ConstEvalStatus::Constant ||
            !operand.value.has_value()) {
            return operand;
        }

        if (operand.value->kind == ConstValueKind::Complex &&
            descriptor->op == UnaryOpKind::Minus) {
            if (operand.value->complex_value.has_integer_components) {
                return ConstEvalResult::constant(
                    ConstValue::complex_integer(
                        const_int_neg(
                            operand.value->complex_value.integer_real),
                        const_int_neg(
                            operand.value->complex_value.integer_imag)));
            }
            return ConstEvalResult::constant(
                ConstValue::complex(
                    aburi::floating::negate(
                        operand.value->complex_value.real),
                    aburi::floating::negate(
                        operand.value->complex_value.imag)));
        }
        bool computation_is_floating =
            aburi::cir::is_floating_type(file(), descriptor->computation_type.type);
        if (computation_is_floating) {
            aburi::cir::FloatingSemantics semantics =
                aburi::floating::semantics_for_type(
                    file(), descriptor->computation_type.type);
            auto value = value_to_float(*operand.value, semantics);
            if (!value.has_value() ||
                floating_status_disqualifies(value.status)) {
                return make_unsupported(
                    "unary constant evaluation requires a scalar operand",
                    inst.loc);
            }
            switch (descriptor->op) {
                case UnaryOpKind::Plus:
                    return ConstEvalResult::constant(
                        ConstValue::floating(*value));
                case UnaryOpKind::Minus:
                    return ConstEvalResult::constant(ConstValue::floating(
                        aburi::floating::negate(*value)));
                case UnaryOpKind::LogicalNot: {
                    bool truth = false;
                    if (!is_truthy(*operand.value, truth)) {
                        return make_unsupported(
                            "logical-not constant evaluation requires a scalar operand",
                            inst.loc);
                    }
                    return ConstEvalResult::constant(
                        bool_result_for_type(file(), inst.result_type, !truth));
                }
                case UnaryOpKind::BitwiseNot:
                case UnaryOpKind::Invalid:
                    return make_unsupported("unsupported unary operator", inst.loc);
            }
        }

        auto shape =
            aburi::cir::integer_shape_for_type(file(), descriptor->computation_type.type);
        auto value = value_to_int(*operand.value, shape);
        if (!value.has_value()) {
            return make_unsupported(
                "unary constant evaluation requires an integer operand",
                inst.loc);
        }

        switch (descriptor->op) {
            case UnaryOpKind::Plus:
                return ConstEvalResult::constant(ConstValue::integer(*value));
            case UnaryOpKind::Minus:
                return ConstEvalResult::constant(
                    ConstValue::integer(const_int_neg(*value)));
            case UnaryOpKind::LogicalNot: {
                bool truth = false;
                if (!is_truthy(*operand.value, truth)) {
                    return make_unsupported(
                        "logical-not constant evaluation requires a scalar operand",
                        inst.loc);
                }
                return ConstEvalResult::constant(
                    bool_result_for_type(file(), inst.result_type, !truth));
            }
            case UnaryOpKind::BitwiseNot:
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_bits128(
                        ~value->to_unsigned_u128(),
                        value->bit_width,
                        value->is_unsigned)));
            case UnaryOpKind::Invalid:
                return make_unsupported("invalid unary operator", inst.loc);
        }
        return make_unsupported("unsupported unary operator", inst.loc);
    }

    ConstEvalResult evaluate_binary(
        const aburi::cir::Inst& inst,
        const aburi::cir::InstPayload& payload,
        std::unordered_map<uint64_t, ConstValue>& env) {
        const auto* descriptor = std::get_if<aburi::cir::BinaryOpDescriptor>(&payload);
        std::vector<ValueRef> operands = value_operands(file(), inst);
        if (!descriptor || operands.size() < 2) {
            return make_unsupported("binary operator payload is malformed", inst.loc);
        }

        ConstEvalResult lhs_result = value_for_ref(operands[0], env);
        if (lhs_result.status != ConstEvalStatus::Constant ||
            !lhs_result.value.has_value()) {
            return lhs_result;
        }
        ConstEvalResult rhs_result = value_for_ref(operands[1], env);
        if (rhs_result.status != ConstEvalStatus::Constant ||
            !rhs_result.value.has_value()) {
            return rhs_result;
        }

        if (descriptor->op == BinaryOpKind::LogicalAnd ||
            descriptor->op == BinaryOpKind::LogicalOr) {
            bool lhs = false;
            bool rhs = false;
            if (!is_truthy(*lhs_result.value, lhs) ||
                !is_truthy(*rhs_result.value, rhs)) {
                return make_unsupported(
                    "logical constant evaluation requires scalar operands",
                    inst.loc);
            }
            return ConstEvalResult::constant(bool_result_for_type(
                file(),
                inst.result_type,
                descriptor->op == BinaryOpKind::LogicalAnd ? (lhs && rhs)
                                                           : (lhs || rhs)));
        }

        if (lhs_result.value->kind == ConstValueKind::MetaInfo ||
            rhs_result.value->kind == ConstValueKind::MetaInfo) {
            if (descriptor->op == BinaryOpKind::Equal ||
                descriptor->op == BinaryOpKind::NotEqual) {
                bool equal =
                    const_value_equals(*lhs_result.value, *rhs_result.value);
                return ConstEvalResult::constant(bool_result_for_type(
                    file(),
                    inst.result_type,
                    descriptor->op == BinaryOpKind::Equal ? equal : !equal));
            }
            return make_unsupported(
                "only equality comparison is defined for 'std::meta::info'",
                inst.loc);
        }

        bool lhs_pointer_like =
            lhs_result.value->kind == ConstValueKind::Address ||
            lhs_result.value->is_null(ConstNullKind::Nullptr) ||
            lhs_result.value->is_null(ConstNullKind::Pointer);
        bool rhs_pointer_like =
            rhs_result.value->kind == ConstValueKind::Address ||
            rhs_result.value->is_null(ConstNullKind::Nullptr) ||
            rhs_result.value->is_null(ConstNullKind::Pointer);
        if (lhs_pointer_like || rhs_pointer_like) {
            auto bool_result = [&](bool value) {
                return ConstEvalResult::constant(
                    bool_result_for_type(file(), inst.result_type, value));
            };
            std::optional<size_t> lhs_pointee = pointee_size(
                file(), file().valid(operands[0].inst)
                            ? file().inst(operands[0].inst).result_type
                            : TypeId{});
            std::optional<size_t> rhs_pointee = pointee_size(
                file(), file().valid(operands[1].inst)
                            ? file().inst(operands[1].inst).result_type
                            : TypeId{});

            if (lhs_result.value->kind == ConstValueKind::Address &&
                !lhs_pointee.has_value()) {
                lhs_pointee = 1;
            }
            if (rhs_result.value->kind == ConstValueKind::Address &&
                !rhs_pointee.has_value()) {
                rhs_pointee = 1;
            }
            if (lhs_pointer_like && rhs_pointer_like) {
                std::optional<ConstAddressValue> lhs_address =
                    as_address(*lhs_result.value);
                std::optional<ConstAddressValue> rhs_address =
                    as_address(*rhs_result.value);
                if (!lhs_address.has_value() || !rhs_address.has_value()) {
                    return make_unsupported(
                        "pointer operands are not address constants", inst.loc);
                }
                bool same_base = lhs_address->same_base(*rhs_address);
                switch (descriptor->op) {
                    case BinaryOpKind::Sub: {
                        std::optional<size_t> element =
                            lhs_pointee.has_value() ? lhs_pointee : rhs_pointee;
                        if (!same_base || !element.has_value() || *element == 0) {
                            return make_unsupported(
                                "pointer difference is not a constant expression",
                                inst.loc);
                        }
                        int64_t diff =
                            (lhs_address->byte_offset - rhs_address->byte_offset) /
                            static_cast<int64_t>(*element);
                        auto result_shape = aburi::cir::integer_shape_for_type(
                            file(), inst.result_type);
                        return ConstEvalResult::constant(ConstValue::integer(
                            ConstIntValue::from_signed(diff, result_shape.bit_width)
                                .cast(result_shape.bit_width,
                                      result_shape.is_unsigned)));
                    }
                    case BinaryOpKind::Equal:
                        return bool_result(same_base
                            ? lhs_address->byte_offset == rhs_address->byte_offset
                            : false);
                    case BinaryOpKind::NotEqual:
                        return bool_result(same_base
                            ? lhs_address->byte_offset != rhs_address->byte_offset
                            : true);
                    case BinaryOpKind::Less:
                    case BinaryOpKind::LessEqual:
                    case BinaryOpKind::Greater:
                    case BinaryOpKind::GreaterEqual: {
                        if (!same_base) {
                            return make_unsupported(
                                "relational pointer comparison requires a common base",
                                inst.loc);
                        }
                        int64_t lhs_off = lhs_address->byte_offset;
                        int64_t rhs_off = rhs_address->byte_offset;
                        bool value = descriptor->op == BinaryOpKind::Less
                            ? lhs_off < rhs_off
                            : descriptor->op == BinaryOpKind::LessEqual
                                ? lhs_off <= rhs_off
                                : descriptor->op == BinaryOpKind::Greater
                                    ? lhs_off > rhs_off
                                    : lhs_off >= rhs_off;
                        return bool_result(value);
                    }
                    default:
                        return make_unsupported(
                            "pointer binary operator is not a constant expression",
                            inst.loc);
                }
            }

            const ConstValue& pointer_value =
                lhs_pointer_like ? *lhs_result.value : *rhs_result.value;
            const ConstValue& index_value =
                lhs_pointer_like ? *rhs_result.value : *lhs_result.value;
            std::optional<ConstAddressValue> address = as_address(pointer_value);
            std::optional<int64_t> index = index_value.try_as_int64();
            std::optional<size_t> element =
                lhs_pointer_like ? lhs_pointee : rhs_pointee;
            if (address.has_value() && !index.has_value() &&
                address_is_null_base(*address) &&
                index_value.kind == ConstValueKind::Integer &&
                (descriptor->op == BinaryOpKind::Add ||
                 (descriptor->op == BinaryOpKind::Sub && lhs_pointer_like))) {
                unsigned pointer_bits = file().target_info_ptr()
                    ? file().target_info_ptr()->pointer_width
                    : 64;
                if (pointer_bits > 0 && pointer_bits <= 64) {
                    uint64_t mask = pointer_bits == 64
                        ? std::numeric_limits<uint64_t>::max()
                        : (uint64_t{1} << pointer_bits) - 1;
                    uint64_t base =
                        static_cast<uint64_t>(address->byte_offset) & mask;
                    uint64_t index_bits = index_value.int_value
                        .cast(pointer_bits, true)
                        .to_unsigned_u64();
                    uint64_t scaled_bits =
                        index_bits * static_cast<uint64_t>(element.value_or(1));
                    uint64_t result_bits = descriptor->op == BinaryOpKind::Add
                        ? base + scaled_bits
                        : base - scaled_bits;
                    result_bits &= mask;
                    if (pointer_bits == 64 &&
                        result_bits >
                            static_cast<uint64_t>(
                                std::numeric_limits<int64_t>::max())) {
                        address->byte_offset =
                            std::numeric_limits<int64_t>::min() +
                            static_cast<int64_t>(
                                result_bits - (uint64_t{1} << 63));
                    } else {
                        address->byte_offset =
                            static_cast<int64_t>(result_bits);
                    }
                    return ConstEvalResult::constant(
                        ConstValue::address_value_of(*address));
                }
            }
            if (!address.has_value() || !index.has_value()) {
                return make_unsupported(
                    "pointer arithmetic is not a constant expression", inst.loc);
            }

            int64_t scaled = *index * static_cast<int64_t>(element.value_or(1));
            auto adjust_array_provenance = [&](bool subtract) {
                if (!element.has_value() || address->subobjects.empty() ||
                    !address->subobjects.back().is_array_element) {
                    return;
                }
                ConstSubobjectPathEntry& last = address->subobjects.back();
                __int128 delta = static_cast<__int128>(*index);
                if (subtract) {
                    delta = -delta;
                }
                __int128 adjusted =
                    static_cast<__int128>(last.array_index) + delta;
                if (adjusted < 0 ||
                    adjusted >
                        static_cast<__int128>(
                            std::numeric_limits<uint64_t>::max())) {

                    address->subobjects.clear();
                    return;
                }
                last.array_index = static_cast<uint64_t>(adjusted);
            };
            switch (descriptor->op) {
                case BinaryOpKind::Add:
                    address->byte_offset += scaled;
                    adjust_array_provenance(/*subtract=*/false);
                    return ConstEvalResult::constant(
                        ConstValue::address_value_of(*address));
                case BinaryOpKind::Sub:
                    if (!lhs_pointer_like) {
                        return make_unsupported(
                            "integer minus pointer is not a constant expression",
                            inst.loc);
                    }
                    address->byte_offset -= scaled;
                    adjust_array_provenance(/*subtract=*/true);
                    return ConstEvalResult::constant(
                        ConstValue::address_value_of(*address));
                default:
                    return make_unsupported(
                        "pointer binary operator is not a constant expression",
                        inst.loc);
            }
        }

        aburi::cir::TypeId computation_resolved =
            file().resolved_type(descriptor->computation_type.type);
        bool computation_is_complex =
            file().valid(computation_resolved) &&
            file().type(computation_resolved).kind == aburi::cir::TypeKind::Complex;
        if (computation_is_complex) {
            const auto* complex =
                std::get_if<aburi::cir::ComplexTypePayload>(
                    &file().type_payload(computation_resolved));
            bool integer_components = complex &&
                aburi::cir::is_integer_like_type(
                    file(), complex->element_type.type);
            if (integer_components) {
                aburi::cir::IntegerTypeShape shape =
                    aburi::cir::integer_shape_for_type(
                        file(), complex->element_type.type);
                auto zero_component = [&]() {
                    return ConstIntValue::from_unsigned(0, shape.bit_width)
                        .cast(shape.bit_width, shape.is_unsigned);
                };
                auto as_integer_complex = [&](const ConstValue& value)
                    -> std::optional<ConstComplexValue> {
                    ConstComplexValue result;
                    result.has_integer_components = true;
                    if (value.kind == ConstValueKind::Complex) {
                        if (!value.complex_value.valid() ||
                            !value.complex_value.has_integer_components) {
                            return std::nullopt;
                        }
                        result.integer_real =
                            value.complex_value.integer_real.cast(
                                shape.bit_width, shape.is_unsigned);
                        result.integer_imag =
                            value.complex_value.integer_imag.cast(
                                shape.bit_width, shape.is_unsigned);
                        return result;
                    }
                    auto real = value_to_int(value, shape);
                    if (!real) {
                        return std::nullopt;
                    }
                    result.integer_real = *real;
                    result.integer_imag = zero_component();
                    return result;
                };
                auto lhs = as_integer_complex(*lhs_result.value);
                auto rhs = as_integer_complex(*rhs_result.value);
                if (!lhs || !rhs) {
                    return make_unsupported(
                        "integer complex evaluation requires integer operands",
                        inst.loc);
                }
                ConstIntValue a = lhs->integer_real;
                ConstIntValue b = lhs->integer_imag;
                ConstIntValue c = rhs->integer_real;
                ConstIntValue d = rhs->integer_imag;
                auto complex_integer = [&](ConstIntValue re,
                                           ConstIntValue im) {
                    return ConstEvalResult::constant(
                        ConstValue::complex_integer(re, im));
                };
                switch (descriptor->op) {
                    case BinaryOpKind::Add:
                        return complex_integer(const_int_add(a, c),
                                               const_int_add(b, d));
                    case BinaryOpKind::Sub:
                        return complex_integer(const_int_sub(a, c),
                                               const_int_sub(b, d));
                    case BinaryOpKind::Mul:
                        return complex_integer(
                            const_int_sub(const_int_mul(a, c),
                                          const_int_mul(b, d)),
                            const_int_add(const_int_mul(a, d),
                                          const_int_mul(b, c)));
                    case BinaryOpKind::Div: {
                        ConstIntValue denominator = const_int_add(
                            const_int_mul(c, c), const_int_mul(d, d));
                        ConstIntOpResult real = const_int_div(
                            const_int_add(const_int_mul(a, c),
                                          const_int_mul(b, d)),
                            denominator);
                        ConstIntOpResult imag = const_int_div(
                            const_int_sub(const_int_mul(b, c),
                                          const_int_mul(a, d)),
                            denominator);
                        if (!real.value.has_value() ||
                            !imag.value.has_value()) {
                            return make_unsupported(
                                "integer complex division is not a constant expression",
                                inst.loc);
                        }
                        return complex_integer(*real.value, *imag.value);
                    }
                    case BinaryOpKind::Equal:
                    case BinaryOpKind::NotEqual: {
                        bool equal = a.to_unsigned_u128() ==
                                         c.to_unsigned_u128() &&
                                     b.to_unsigned_u128() ==
                                         d.to_unsigned_u128();
                        return ConstEvalResult::constant(bool_result_for_type(
                            file(), inst.result_type,
                            descriptor->op == BinaryOpKind::Equal
                                ? equal : !equal));
                    }
                    default:
                        break;
                }
                return make_unsupported(
                    "integer complex operator is not a constant expression",
                    inst.loc);
            }
            aburi::cir::FloatingSemantics semantics = complex
                ? aburi::floating::semantics_for_type(
                      file(), complex->element_type.type)
                : aburi::cir::FloatingSemantics::Invalid;
            auto as_complex = [&](const ConstValue& value)
                -> std::optional<ConstComplexValue> {
                if (value.kind == ConstValueKind::Complex &&
                    value.complex_value.valid()) {
                    auto real = aburi::floating::convert(
                        value.complex_value.real, semantics);
                    auto imag = aburi::floating::convert(
                        value.complex_value.imag, semantics);
                    if (real && imag &&
                        !floating_status_disqualifies(real.status) &&
                        !floating_status_disqualifies(imag.status)) {
                        ConstComplexValue result;
                        result.real = *real;
                        result.imag = *imag;
                        return result;
                    }
                    return std::nullopt;
                }
                auto real = value_to_float(value, semantics);
                if (real && !floating_status_disqualifies(real.status)) {
                    ConstComplexValue result;
                    result.real = *real;
                    result.imag = aburi::floating::zero(semantics);
                    return result;
                }
                return std::nullopt;
            };
            auto lhs = as_complex(*lhs_result.value);
            auto rhs = as_complex(*rhs_result.value);
            if (!lhs.has_value() || !rhs.has_value()) {
                return make_unsupported(
                    "complex constant evaluation requires scalar operands",
                    inst.loc);
            }
            bool operation_failed = false;
            auto calculate = [&](aburi::floating::BinaryOperation operation,
                                 aburi::cir::FloatingValue left,
                                 aburi::cir::FloatingValue right) {
                aburi::floating::FloatResult result =
                    aburi::floating::binary(operation, left, right);
                if (!result || floating_status_disqualifies(result.status)) {
                    operation_failed = true;
                    return aburi::cir::FloatingValue{};
                }
                return result.value;
            };
            auto complex_value = [&](aburi::cir::FloatingValue re,
                                     aburi::cir::FloatingValue im) {
                if (operation_failed || !re.valid() || !im.valid()) {
                    return make_unsupported(
                        "complex arithmetic is not a constant expression",
                        inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::complex(re, im));
            };
            aburi::cir::FloatingValue a = lhs->real;
            aburi::cir::FloatingValue b = lhs->imag;
            aburi::cir::FloatingValue c = rhs->real;
            aburi::cir::FloatingValue d = rhs->imag;
            switch (descriptor->op) {
                case BinaryOpKind::Add:
                    return complex_value(
                        calculate(aburi::floating::BinaryOperation::Add, a, c),
                        calculate(aburi::floating::BinaryOperation::Add, b, d));
                case BinaryOpKind::Sub:
                    return complex_value(
                        calculate(aburi::floating::BinaryOperation::Subtract, a, c),
                        calculate(aburi::floating::BinaryOperation::Subtract, b, d));
                case BinaryOpKind::Mul: {
                    aburi::floating::ComplexFloatResult product =
                        aburi::floating::complex_multiply({a, b}, {c, d});
                    if (!product ||
                        floating_status_disqualifies(product.status)) {
                        operation_failed = true;
                    }
                    return complex_value(product.value.real,
                                         product.value.imag);
                }
                case BinaryOpKind::Div: {
                    aburi::floating::ComplexFloatResult quotient =
                        aburi::floating::complex_divide({a, b}, {c, d});
                    if (!quotient ||
                        floating_status_disqualifies(quotient.status)) {
                        operation_failed = true;
                    }
                    return complex_value(quotient.value.real,
                                         quotient.value.imag);
                }
                case BinaryOpKind::Equal:
                case BinaryOpKind::NotEqual: {
                    auto real_comparison = aburi::floating::compare(a, c);
                    auto imag_comparison = aburi::floating::compare(b, d);
                    if (!real_comparison || !imag_comparison ||
                        floating_status_disqualifies(real_comparison.status) ||
                        floating_status_disqualifies(imag_comparison.status)) {
                        return make_unsupported(
                            "complex comparison is not a constant expression",
                            inst.loc);
                    }
                    bool equal = *real_comparison ==
                                     aburi::floating::CompareResult::Equal &&
                                 *imag_comparison ==
                                     aburi::floating::CompareResult::Equal;
                    return ConstEvalResult::constant(bool_result_for_type(
                        file(), inst.result_type,
                        descriptor->op == BinaryOpKind::Equal ? equal : !equal));
                }
                default:
                    break;
            }
            return make_unsupported("unsupported complex binary operator", inst.loc);
        }

        bool computation_is_floating =
            aburi::cir::is_floating_type(file(), descriptor->computation_type.type);
        if (computation_is_floating) {
            aburi::cir::FloatingSemantics semantics =
                aburi::floating::semantics_for_type(
                    file(), descriptor->computation_type.type);
            auto lhs = value_to_float(*lhs_result.value, semantics);
            auto rhs = value_to_float(*rhs_result.value, semantics);
            if (!lhs.has_value() || !rhs.has_value() ||
                floating_status_disqualifies(lhs.status) ||
                floating_status_disqualifies(rhs.status)) {
                return make_unsupported(
                    "floating constant evaluation requires scalar operands",
                    inst.loc);
            }
            auto float_value = [&](aburi::floating::BinaryOperation operation) {
                aburi::floating::FloatResult result =
                    aburi::floating::binary(operation, *lhs, *rhs);
                if (!result) {
                    return make_unsupported(
                        "floating operation has incompatible target semantics",
                        inst.loc);
                }
                if (floating_status_disqualifies(result.status)) {
                    return make_unsupported(
                        result.status.has(
                            aburi::floating::FloatStatusFlag::DivideByZero)
                            ? "floating division by zero is not a constant expression"
                            : "invalid floating arithmetic is not a constant expression",
                        inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::floating(*result));
            };
            auto bool_value = [&](bool value) {
                return ConstEvalResult::constant(
                    bool_result_for_type(file(), inst.result_type, value));
            };
            switch (descriptor->op) {
                case BinaryOpKind::Add:
                    return float_value(aburi::floating::BinaryOperation::Add);
                case BinaryOpKind::Sub:
                    return float_value(aburi::floating::BinaryOperation::Subtract);
                case BinaryOpKind::Mul:
                    return float_value(aburi::floating::BinaryOperation::Multiply);
                case BinaryOpKind::Div:
                    return float_value(aburi::floating::BinaryOperation::Divide);
                case BinaryOpKind::Mod:
                    return float_value(aburi::floating::BinaryOperation::Modulo);
                case BinaryOpKind::Less:
                case BinaryOpKind::LessEqual:
                case BinaryOpKind::Greater:
                case BinaryOpKind::GreaterEqual:
                case BinaryOpKind::Equal:
                case BinaryOpKind::NotEqual: {
                    auto comparison = aburi::floating::compare(*lhs, *rhs);
                    if (!comparison) {
                        return make_unsupported(
                            "floating comparison has incompatible target semantics",
                            inst.loc);
                    }
                    if (floating_status_disqualifies(comparison.status)) {
                        return make_unsupported(
                            "signaling NaN comparison is not a constant expression",
                            inst.loc);
                    }
                    using aburi::floating::CompareResult;
                    bool result = false;
                    switch (descriptor->op) {
                        case BinaryOpKind::Less:
                            result = *comparison == CompareResult::Less;
                            break;
                        case BinaryOpKind::LessEqual:
                            result = *comparison == CompareResult::Less ||
                                     *comparison == CompareResult::Equal;
                            break;
                        case BinaryOpKind::Greater:
                            result = *comparison == CompareResult::Greater;
                            break;
                        case BinaryOpKind::GreaterEqual:
                            result = *comparison == CompareResult::Greater ||
                                     *comparison == CompareResult::Equal;
                            break;
                        case BinaryOpKind::Equal:
                            result = *comparison == CompareResult::Equal;
                            break;
                        case BinaryOpKind::NotEqual:
                            result = *comparison != CompareResult::Equal;
                            break;
                        default:
                            break;
                    }
                    return bool_value(result);
                }
                case BinaryOpKind::BitAnd:
                case BinaryOpKind::BitOr:
                case BinaryOpKind::BitXor:
                case BinaryOpKind::Shl:
                case BinaryOpKind::Shr:
                case BinaryOpKind::LogicalAnd:
                case BinaryOpKind::LogicalOr:
                case BinaryOpKind::Comma:
                case BinaryOpKind::Invalid:
                    break;
            }
            return make_unsupported("unsupported floating binary operator", inst.loc);
        }

        auto shape =
            aburi::cir::integer_shape_for_type(file(), descriptor->computation_type.type);
        auto lhs = value_to_int(*lhs_result.value, shape);
        auto rhs = value_to_int(*rhs_result.value, shape);
        if (!lhs.has_value() || !rhs.has_value()) {
            return make_unsupported(
                "binary constant evaluation requires integer operands",
                inst.loc);
        }

        auto bool_value = [&](bool value) {
            return ConstEvalResult::constant(
                bool_result_for_type(file(), inst.result_type, value));
        };

        switch (descriptor->op) {
            case BinaryOpKind::Add:
                return ConstEvalResult::constant(
                    ConstValue::integer(const_int_add(*lhs, *rhs)));
            case BinaryOpKind::Sub:
                return ConstEvalResult::constant(
                    ConstValue::integer(const_int_sub(*lhs, *rhs)));
            case BinaryOpKind::Mul:
                return ConstEvalResult::constant(
                    ConstValue::integer(const_int_mul(*lhs, *rhs)));
            case BinaryOpKind::Div: {
                auto result = const_int_div(*lhs, *rhs);
                if (!result.value.has_value()) {
                    return make_error(ConstEvalDiagCode::DivisionByZero,
                                      "division by zero in constant expression",
                                      inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::integer(*result.value));
            }
            case BinaryOpKind::Mod: {
                auto result = const_int_mod(*lhs, *rhs);
                if (!result.value.has_value()) {
                    return make_error(ConstEvalDiagCode::DivisionByZero,
                                      "modulo by zero in constant expression",
                                      inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::integer(*result.value));
            }
            case BinaryOpKind::Less:
                return bool_value(compare_less(*lhs, *rhs));
            case BinaryOpKind::LessEqual:
                return bool_value(compare_less_equal(*lhs, *rhs));
            case BinaryOpKind::Greater:
                return bool_value(compare_less(*rhs, *lhs));
            case BinaryOpKind::GreaterEqual:
                return bool_value(compare_less_equal(*rhs, *lhs));
            case BinaryOpKind::Equal:
                return bool_value(lhs->to_unsigned_u128() == rhs->to_unsigned_u128());
            case BinaryOpKind::NotEqual:
                return bool_value(lhs->to_unsigned_u128() != rhs->to_unsigned_u128());
            case BinaryOpKind::BitAnd:
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_bits128(lhs->to_unsigned_u128() &
                                                    rhs->to_unsigned_u128(),
                                                shape.bit_width,
                                                shape.is_unsigned)));
            case BinaryOpKind::BitOr:
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_bits128(lhs->to_unsigned_u128() |
                                                    rhs->to_unsigned_u128(),
                                                shape.bit_width,
                                                shape.is_unsigned)));
            case BinaryOpKind::BitXor:
                return ConstEvalResult::constant(ConstValue::integer(
                    ConstIntValue::from_bits128(lhs->to_unsigned_u128() ^
                                                    rhs->to_unsigned_u128(),
                                                shape.bit_width,
                                                shape.is_unsigned)));
            case BinaryOpKind::Shl: {
                auto result = const_int_shl(*lhs, *rhs);
                if (!result.value.has_value()) {
                    return make_error(ConstEvalDiagCode::InvalidShiftAmount,
                                      "invalid shift amount in constant expression",
                                      inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::integer(*result.value));
            }
            case BinaryOpKind::Shr: {
                auto result = const_int_shr(*lhs, *rhs);
                if (!result.value.has_value()) {
                    return make_error(ConstEvalDiagCode::InvalidShiftAmount,
                                      "invalid shift amount in constant expression",
                                      inst.loc);
                }
                return ConstEvalResult::constant(ConstValue::integer(*result.value));
            }
            case BinaryOpKind::Comma:
                return ConstEvalResult::constant(*rhs_result.value);
            case BinaryOpKind::LogicalAnd:
            case BinaryOpKind::LogicalOr:
            case BinaryOpKind::Invalid:
                break;
        }
        return make_unsupported("unsupported binary operator", inst.loc);
    }

    bool compare_less(ConstIntValue lhs, ConstIntValue rhs) const {
        return lhs.is_unsigned ? lhs.to_unsigned_u128() < rhs.to_unsigned_u128()
                               : lhs.to_signed_i128() < rhs.to_signed_i128();
    }

    bool compare_less_equal(ConstIntValue lhs, ConstIntValue rhs) const {
        return lhs.is_unsigned ? lhs.to_unsigned_u128() <= rhs.to_unsigned_u128()
                               : lhs.to_signed_i128() <= rhs.to_signed_i128();
    }

    ConstEvalResult evaluate_cast(
        const aburi::cir::Inst& inst,
        std::unordered_map<uint64_t, ConstValue>& env) {
        auto type_ref = first_type_operand(file(), inst);
        std::vector<ValueRef> operands = value_operands(file(), inst);
        if (!type_ref.has_value() || operands.empty()) {
            return make_unsupported("cast payload is malformed", inst.loc);
        }
        ConstEvalResult inner = value_for_ref(operands[0], env);
        if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
            return inner;
        }

        TypeId target = file().resolved_type(type_ref->type);
        if (!file().valid(target)) {
            return make_unsupported("cast target type is invalid", inst.loc);
        }
        TypeKind target_kind = file().type(target).kind;
        if (target_kind == TypeKind::LValueReference ||
            target_kind == TypeKind::RValueReference) {
            if (inner.value->kind == ConstValueKind::Address) {
                return ConstEvalResult::constant(*inner.value);
            }
            return make_unsupported(
                "reference cast operand is not an address constant",
                inst.loc);
        }
        if (target_kind == TypeKind::Pointer) {
            if (inner.value->kind == ConstValueKind::Address) {
                return ConstEvalResult::constant(*inner.value);
            }
            if (inner.value->is_null(ConstNullKind::Nullptr)) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            if (inner.value->is_null(ConstNullKind::Pointer)) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            if (inner.value->kind == ConstValueKind::Integer) {
                unsigned pointer_bits = file().target_info_ptr()
                    ? file().target_info_ptr()->pointer_width
                    : 64;
                if (pointer_bits > 0 && pointer_bits <= 64) {
                    uint64_t bits = inner.value->int_value
                        .cast(pointer_bits, true)
                        .to_unsigned_u64();
                    if (bits == 0) {
                        return ConstEvalResult::constant(
                            ConstValue::null_pointer());
                    }
                    ConstAddressValue absolute;
                    if (pointer_bits == 64 &&
                        bits >
                            static_cast<uint64_t>(
                                std::numeric_limits<int64_t>::max())) {
                        absolute.byte_offset =
                            std::numeric_limits<int64_t>::min() +
                            static_cast<int64_t>(
                                bits - (uint64_t{1} << 63));
                    } else {
                        absolute.byte_offset = static_cast<int64_t>(bits);
                    }
                    return ConstEvalResult::constant(
                        ConstValue::address_value_of(absolute));
                }
            }
            if (std::optional<int64_t> as_int = inner.value->try_as_int64()) {

                if (*as_int == 0) {
                    return ConstEvalResult::constant(ConstValue::null_pointer());
                }
                ConstAddressValue absolute;
                absolute.byte_offset = *as_int;
                return ConstEvalResult::constant(
                    ConstValue::address_value_of(absolute));
            }
            return make_unsupported(
                "pointer cast is not a constant expression", inst.loc);
        }
        if (target_kind == TypeKind::MemberPointer) {
            if (inner.value->is_null(ConstNullKind::MemberPointer) ||
                inner.value->kind == ConstValueKind::MemberPointer) {
                return ConstEvalResult::constant(*inner.value);
            }
            if (inner.value->is_null(ConstNullKind::Nullptr)) {
                return ConstEvalResult::constant(
                    ConstValue::null_member_pointer());
            }
            if (std::optional<int64_t> as_int = inner.value->try_as_int64();
                as_int && *as_int == 0) {
                return ConstEvalResult::constant(
                    ConstValue::null_member_pointer());
            }
            return make_unsupported(
                "member pointer cast is not a constant expression", inst.loc);
        }
        if (is_bool_type(file(), target)) {

            bool truthy = false;
            if (is_truthy(*inner.value, truthy)) {
                return ConstEvalResult::constant(ConstValue::boolean(truthy));
            }
            return make_unsupported(
                "boolean conversion operand is not a scalar constant", inst.loc);
        }
        {
            aburi::cir::TypeId cast_resolved = file().resolved_type(target);
            bool target_is_complex = file().valid(cast_resolved) &&
                file().type(cast_resolved).kind == aburi::cir::TypeKind::Complex;
            if (target_is_complex) {
                const auto* complex =
                    std::get_if<aburi::cir::ComplexTypePayload>(
                        &file().type_payload(cast_resolved));
                bool target_integer = complex &&
                    aburi::cir::is_integer_like_type(
                        file(), complex->element_type.type);
                if (target_integer) {
                    aburi::cir::IntegerTypeShape shape =
                        aburi::cir::integer_shape_for_type(
                            file(), complex->element_type.type);
                    if (inner.value->kind == ConstValueKind::Complex) {
                        if (!inner.value->complex_value.has_integer_components) {

                            auto real = aburi::floating::to_integer(
                                inner.value->complex_value.real,
                                shape.bit_width, !shape.is_unsigned);
                            auto imag = aburi::floating::to_integer(
                                inner.value->complex_value.imag,
                                shape.bit_width, !shape.is_unsigned);
                            if (!real || !imag) {
                                return make_unsupported(
                                    "floating complex to integer complex "
                                    "conversion is not constant",
                                    inst.loc);
                            }
                            return ConstEvalResult::constant(
                                ConstValue::complex_integer(
                                    ConstIntValue::from_bits128(
                                        *real, shape.bit_width,
                                        shape.is_unsigned),
                                    ConstIntValue::from_bits128(
                                        *imag, shape.bit_width,
                                        shape.is_unsigned)));
                        }
                        return ConstEvalResult::constant(
                            ConstValue::complex_integer(
                                inner.value->complex_value.integer_real.cast(
                                    shape.bit_width, shape.is_unsigned),
                                inner.value->complex_value.integer_imag.cast(
                                    shape.bit_width, shape.is_unsigned)));
                    }
                    auto real = value_to_int(*inner.value, shape);
                    if (real) {
                        ConstIntValue zero =
                            ConstIntValue::from_unsigned(0, shape.bit_width)
                                .cast(shape.bit_width, shape.is_unsigned);
                        return ConstEvalResult::constant(
                            ConstValue::complex_integer(*real, zero));
                    }
                    return make_unsupported(
                        "integer complex conversion operand is not constant",
                        inst.loc);
                }
                aburi::cir::FloatingSemantics semantics = complex
                    ? aburi::floating::semantics_for_type(
                          file(), complex->element_type.type)
                    : aburi::cir::FloatingSemantics::Invalid;
                if (inner.value->kind == ConstValueKind::Complex) {
                    aburi::floating::FloatResult real;
                    aburi::floating::FloatResult imag;
                    if (inner.value->complex_value.has_integer_components) {
                        const ConstIntValue& source_real =
                            inner.value->complex_value.integer_real;
                        const ConstIntValue& source_imag =
                            inner.value->complex_value.integer_imag;
                        real = aburi::floating::from_integer(
                            source_real.to_unsigned_u128(),
                            source_real.bit_width, !source_real.is_unsigned,
                            semantics);
                        imag = aburi::floating::from_integer(
                            source_imag.to_unsigned_u128(),
                            source_imag.bit_width, !source_imag.is_unsigned,
                            semantics);
                    } else {
                        real = aburi::floating::convert(
                            inner.value->complex_value.real, semantics);
                        imag = aburi::floating::convert(
                            inner.value->complex_value.imag, semantics);
                    }
                    if (real && imag &&
                        !floating_status_disqualifies(real.status) &&
                        !floating_status_disqualifies(imag.status)) {
                        return ConstEvalResult::constant(
                            ConstValue::complex(*real, *imag));
                    }
                    return make_unsupported(
                        "complex conversion components cannot be represented",
                        inst.loc);
                }
                auto real = value_to_float(*inner.value, semantics);
                if (real && !floating_status_disqualifies(real.status)) {
                    return ConstEvalResult::constant(ConstValue::complex(
                        *real, aburi::floating::zero(semantics)));
                }
                return make_unsupported(
                    "complex conversion operand is not a scalar constant", inst.loc);
            }
            if (inner.value->kind == ConstValueKind::Complex) {

                if (inner.value->complex_value.has_integer_components) {
                    inner.value = ConstValue::integer(
                        inner.value->complex_value.integer_real);
                } else {
                    aburi::cir::FloatingSemantics semantics =
                        aburi::floating::semantics_for_type(file(), target);
                    auto real = aburi::floating::convert(
                        inner.value->complex_value.real, semantics);
                    if (!real || floating_status_disqualifies(real.status)) {
                        return make_unsupported(
                            "complex conversion cannot represent its real component",
                            inst.loc);
                    }
                    inner.value = ConstValue::floating(*real);
                }
            }
        }
        if (aburi::cir::is_integer_like_type(file(), target)) {
            auto shape = aburi::cir::integer_shape_for_type(file(), target);

            if (inner.value->kind == ConstValueKind::Address) {

                if (address_is_null_base(inner.value->address_value)) {
                    return ConstEvalResult::constant(ConstValue::integer(
                        ConstIntValue::from_signed(
                            inner.value->address_value.byte_offset,
                            shape.bit_width)
                            .cast(shape.bit_width, shape.is_unsigned)));
                }

                int pointer_bits = file().target_info_ptr()
                    ? file().target_info_ptr()->pointer_width
                    : 64;
                if (shape.bit_width >= pointer_bits) {
                    return ConstEvalResult::constant(*inner.value);
                }
            }
            auto as_int = value_to_int(*inner.value, shape);
            if (!as_int.has_value() && inner.value->kind == ConstValueKind::Floating) {
                aburi::floating::FloatIntegerResult bits =
                    aburi::floating::to_integer(
                        inner.value->float_value.value,
                        shape.bit_width,
                        !shape.is_unsigned);
                if (bits) {
                    as_int = ConstIntValue::from_bits128(
                        *bits, shape.bit_width, shape.is_unsigned);
                }
            }
            if (!as_int.has_value()) {
                return make_unsupported(
                    "integer cast constant evaluation requires scalar integer input",
                    inst.loc);
            }
            return ConstEvalResult::constant(ConstValue::integer(*as_int));
        }
        if (target_kind == TypeKind::Pointer) {
            auto as_int =
                value_to_int(*inner.value, aburi::cir::IntegerTypeShape{64, true});
            if (as_int.has_value()) {
                if (as_int->to_unsigned_u64() == 0) {
                    return ConstEvalResult::constant(ConstValue::null_pointer());
                }
                return ConstEvalResult::constant(ConstValue::integer(*as_int));
            }
        }
        if (aburi::cir::is_floating_type(file(), target) &&
            (inner.value->kind == ConstValueKind::Floating ||
             inner.value->kind == ConstValueKind::Integer ||
             inner.value->kind == ConstValueKind::Boolean)) {
            aburi::cir::FloatingSemantics semantics =
                aburi::floating::semantics_for_type(file(), target);
            auto as_float = value_to_float(*inner.value, semantics);
            if (!as_float.has_value() ||
                floating_status_disqualifies(as_float.status)) {
                return make_unsupported(
                    "floating cast constant evaluation requires scalar input",
                    inst.loc);
            }
            return ConstEvalResult::constant(ConstValue::floating(*as_float));
        }
        return make_unsupported("cast is not supported in constant evaluation yet",
                                inst.loc);
    }

    const ConstEvalContext& context_;
    ConstEvalRequest request_;
    EvalState state_;
    size_t construct_at_call_depth_ = 0;
    std::unordered_map<uint64_t, uint64_t> local_allocations_;
    std::unordered_map<uint64_t, uint64_t> string_literal_allocations_;
};

} // namespace

ConstEvalResult ConstEvalEngine::evaluate_inst(aburi::cir::InstId inst,
                                               ConstEvalRequest request) const {
    if (!context_.file) {
        return make_error(ConstEvalDiagCode::NullExpression,
                          "constant evaluator has no CIR file",
                          request.loc);
    }
    if (!is_enabled()) {
        return make_not_evaluated("constexpr engine is disabled",
                                  ConstEvalDiagCode::EngineDisabled,
                                  request.loc);
    }
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ConstexprEvalCalls);
    }
    Evaluator evaluator(context_, request);
    return evaluator.apply_transient_allocation_rules(
        evaluator.evaluate_inst(inst));
}

ConstEvalResult ConstEvalEngine::evaluate_fragment(
    const aburi::cir::Fragment& fragment,
    aburi::cir::ValueRef result,
    ConstEvalRequest request) const {
    if (!context_.file) {
        return make_error(ConstEvalDiagCode::NullExpression,
                          "constant evaluator has no CIR file",
                          request.loc);
    }
    if (!is_enabled()) {
        return make_not_evaluated("constexpr engine is disabled",
                                  ConstEvalDiagCode::EngineDisabled,
                                  request.loc);
    }
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ConstexprEvalCalls);
    }
    Evaluator evaluator(context_, request);
    return evaluator.apply_transient_allocation_rules(
        evaluator.evaluate_fragment(fragment, result));
}

ConstEvalResult ConstEvalEngine::evaluate_fragment_with_object_seeds(
    const aburi::cir::Fragment& fragment,
    aburi::cir::ValueRef result,
    ConstEvalRequest request,
    const std::vector<ConstEvalObjectSeed>& object_seeds) const {
    if (!context_.file) {
        return make_error(ConstEvalDiagCode::NullExpression,
                          "constant evaluator has no CIR file",
                          request.loc);
    }
    if (!is_enabled()) {
        return make_not_evaluated("constexpr engine is disabled",
                                  ConstEvalDiagCode::EngineDisabled,
                                  request.loc);
    }
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(PerfCounter::ConstexprEvalCalls);
    }
    Evaluator evaluator(context_, request);
    return evaluator.apply_transient_allocation_rules(
        evaluator.evaluate_fragment_with_object_seeds(fragment,
                                                      result,
                                                      object_seeds));
}
