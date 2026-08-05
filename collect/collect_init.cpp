#include "collect.h"
#include "collect_template_state.h"

#include "../abi/endian.h"
#include "../numeric/floating_cir.h"
#include "../cir/layout.h"
#include "../constexpr/constant_state.h"
#include "../constexpr/consteval_engine.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::collect {

namespace {

bool is_named_initializable_field(const cir::RecordFieldFact& field) {
    return field.name.valid() || (!field.is_bitfield && field.type.type.valid());
}

cir::TemplateNullKind template_null_kind_from_const(ConstNullKind kind) {
    switch (kind) {
        case ConstNullKind::Nullptr:
            return cir::TemplateNullKind::Nullptr;
        case ConstNullKind::Pointer:
            return cir::TemplateNullKind::Pointer;
        case ConstNullKind::MemberPointer:
            return cir::TemplateNullKind::MemberPointer;
        case ConstNullKind::None:
            return cir::TemplateNullKind::None;
    }
    return cir::TemplateNullKind::None;
}

std::optional<size_t> array_size(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Array) {
        return std::nullopt;
    }
    const auto* array = std::get_if<cir::ArrayTypePayload>(&file.type_payload(type_id));
    return array ? array->size : std::nullopt;
}

const cir::ArrayTypePayload* array_payload(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Array) {
        return nullptr;
    }
    return std::get_if<cir::ArrayTypePayload>(&file.type_payload(type_id));
}

const cir::MemberPointerTypePayload* member_pointer_payload(
    const cir::File& file,
    cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) ||
        file.type(type_id).kind != cir::TypeKind::MemberPointer) {
        return nullptr;
    }
    return std::get_if<cir::MemberPointerTypePayload>(
        &file.type_payload(type_id));
}

cir::TypeId array_element_type(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Array) {
        return {};
    }
    const auto* array = std::get_if<cir::ArrayTypePayload>(&file.type_payload(type_id));
    return array ? array->element_type.type : cir::TypeId{};
}

cir::TypeId vector_element_type(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Vector) {
        return {};
    }
    return file.vector_element_type(type_id);
}

const cir::BuiltinTypePayload* builtin_payload(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id) || file.type(type_id).kind != cir::TypeKind::Builtin) {
        return nullptr;
    }
    return std::get_if<cir::BuiltinTypePayload>(&file.type_payload(type_id));
}

bool is_character_type(const cir::File& file, cir::TypeId type_id) {
    const cir::BuiltinTypePayload* builtin = builtin_payload(file, type_id);
    if (!builtin) {
        return false;
    }
    switch (builtin->kind) {
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
            return true;
        default:
            return false;
    }
}

bool is_character_array_type(const cir::File& file, cir::TypeId type_id) {
    const cir::ArrayTypePayload* array = array_payload(file, type_id);
    return array && is_character_type(file, array->element_type.type);
}

bool initializer_contains_unbound_pack_expansion(const ExprResult& expr) {
    if (!expr.pack_expansion_references.empty()) {
        return true;
    }
    if (!expr.init_list) {
        return false;
    }
    return std::any_of(
        expr.init_list->elements.begin(),
        expr.init_list->elements.end(),
        [](const InitElementInput& element) {
            return initializer_contains_unbound_pack_expansion(element.value);
        });
}

std::optional<size_t> string_literal_unit_width(const cir::File& file,
                                                const ExprResult& expr) {
    cir::InstId inst = expr.place.valid() ? expr.place : expr.value;
    if (!inst.valid() || !file.valid(inst) ||
        file.inst(inst).kind != cir::InstKind::StringLiteral) {
        return std::nullopt;
    }
    cir::TypeId object = file.place_object_type(file.inst(inst).result_type);
    const cir::ArrayTypePayload* array = array_payload(file, object);
    if (!array) {
        return std::nullopt;
    }
    return cir::size_of_type(file, array->element_type.type);
}

bool array_accepts_string_literal(const cir::File& file, cir::TypeId array_type,
                                  size_t literal_unit_width) {
    if (literal_unit_width == 0) {
        return false;
    }
    if (is_character_array_type(file, array_type)) {
        return literal_unit_width == 1;
    }
    const cir::ArrayTypePayload* array = array_payload(file, array_type);
    if (!array || !cir::is_integer_like_type(file, array->element_type.type)) {
        return false;
    }
    std::optional<size_t> element_size =
        cir::size_of_type(file, array->element_type.type);
    return element_size.has_value() && *element_size == literal_unit_width;
}

bool record_has_non_defaulted_copy_constructor(const cir::File& file,
                                               cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    const cir::RecordFacts* facts = file.record_facts_for_type(type_id);
    if (!facts) {
        return false;
    }
    for (const cir::RecordMethodFact& method : facts->methods) {
        if (!method.entity.valid() ||
            file.entity(method.entity).kind != cir::EntityKind::Constructor) {
            continue;
        }
        const auto* payload = std::get_if<cir::FunctionTypePayload>(
            &file.type_payload(file.resolved_type(method.type.type)));
        if (!payload || payload->parameters.size() != 1) {
            continue;
        }
        cir::TypeId parameter =
            file.resolved_type(payload->parameters.front().type);
        if (!file.valid(parameter) ||
            file.type(parameter).kind != cir::TypeKind::LValueReference) {
            continue;
        }
        cir::TypeId referred =
            file.resolved_type(file.reference_referred_type(parameter));
        if (referred == type_id && !method.is_defaulted) {
            return true;
        }
    }
    return false;
}

cir::InstId loaded_place_for_value(const cir::File& file, cir::InstId value) {
    if (!value.valid() || !file.valid(value)) {
        return {};
    }
    const cir::Inst& load = file.inst(value);
    if (load.kind != cir::InstKind::LValueToRValue) {
        return {};
    }
    std::vector<cir::ValueRef> operands = file.value_operands(load.operands);
    if (operands.empty()) {
        return {};
    }
    return operands.front().inst;
}

bool can_zero_initialize_with_memset(const cir::File& file, cir::TypeId type_id) {
    type_id = file.resolved_type(type_id);
    if (!file.valid(type_id)) {
        return false;
    }

    const cir::Type& type = file.type(type_id);
    switch (type.kind) {
        case cir::TypeKind::Builtin: {
            const cir::BuiltinTypePayload* builtin = builtin_payload(file, type_id);
            return builtin &&
                   builtin->kind != cir::BuiltinTypeKind::Void &&
                   builtin->kind != cir::BuiltinTypeKind::Other;
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
        case cir::TypeKind::Enum:
        case cir::TypeKind::BitInt:
            return true;
        case cir::TypeKind::Array: {
            const cir::ArrayTypePayload* array = array_payload(file, type_id);
            return array &&
                   array->size_kind == cir::ArraySizeKind::Constant &&
                   array->size.has_value() &&
                   can_zero_initialize_with_memset(file, array->element_type.type);
        }
        case cir::TypeKind::Vector:
            return file.vector_element_count(type_id) > 0 &&
                   can_zero_initialize_with_memset(file, vector_element_type(file, type_id));
        case cir::TypeKind::Complex: {
            const auto* complex =
                std::get_if<cir::ComplexTypePayload>(&file.type_payload(type_id));
            return complex && can_zero_initialize_with_memset(file, complex->element_type.type);
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts = file.record_facts_for_type(type_id);
            if (!facts || facts->is_incomplete) {
                return false;
            }
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_flexible_array_member) {
                    continue;
                }
                if (!is_named_initializable_field(field)) {
                    continue;
                }
                if (field.is_bitfield ||
                    field.storage_size_override > 0 ||
                    field.storage_alignment_override > 0 ||
                    field.is_base_subobject ||
                    field.is_virtual_base_storage) {
                    return false;
                }
                if (!can_zero_initialize_with_memset(file, field.type.type)) {
                    return false;
                }
            }
            return true;
        }
        default:
            return false;
    }
}

const cir::LiteralByteArray* string_literal_bytes(const cir::File& file,
                                                  const ExprResult& expr) {

    cir::InstId literal_inst =
        expr.place.valid() ? expr.place : expr.value;
    if (!literal_inst.valid() || !file.valid(literal_inst)) {
        return nullptr;
    }
    const cir::Inst& inst = file.inst(literal_inst);
    if (inst.kind != cir::InstKind::StringLiteral) {
        return nullptr;
    }
    const auto* literal = std::get_if<cir::LiteralPayload>(&file.payload(inst.payload_index));
    return literal ? std::get_if<cir::LiteralByteArray>(&literal->value) : nullptr;
}

bool is_pointer_or_reference_type(const cir::File& file,
                                  cir::TypeId type,
                                  bool* is_reference = nullptr) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved)) {
        return false;
    }
    cir::TypeKind kind = file.type(resolved).kind;
    bool reference = kind == cir::TypeKind::LValueReference ||
                     kind == cir::TypeKind::RValueReference;
    if (is_reference) {
        *is_reference = reference;
    }
    return kind == cir::TypeKind::Pointer ||
           kind == cir::TypeKind::BlockPointer ||
           reference;
}

const cir::StaticInitializerRelocation* static_relocation_at(
    const std::vector<cir::StaticInitializerRelocation>* relocations,
    size_t offset) {
    if (!relocations) {
        return nullptr;
    }
    for (const cir::StaticInitializerRelocation& relocation : *relocations) {
        if (relocation.offset == offset) {
            return &relocation;
        }
    }
    return nullptr;
}

bool bytes_are_zero(const std::vector<uint8_t>& bytes,
                    size_t offset,
                    size_t size) {
    if (offset + size > bytes.size()) {
        return false;
    }
    for (size_t index = 0; index < size; ++index) {
        if (bytes[offset + index] != 0) {
            return false;
        }
    }
    return true;
}

bool validate_template_address_target(Session& session,
                                      cir::EntityId entity,
                                      uint64_t allocation_id,
                                      const char* subject,
                                      SrcLoc loc) {
    if (!entity.valid()) {
        if (allocation_id != 0) {
            session.report_error(
                std::string(subject) + " must not point to a temporary",
                loc);
        } else {
            session.report_error(
                std::string(subject) + " must name an entity",
                loc);
        }
        return false;
    }

    const cir::File& file = session.file();
    if (!file.valid(entity)) {
        session.report_error(std::string(subject) + " must name an entity",
                             loc);
        return false;
    }

    const cir::Entity& target = file.entity(entity);
    switch (target.object_origin) {
        case cir::EntityObjectOrigin::StructuredBindingBacking:
            break;
        case cir::EntityObjectOrigin::AnonymousUnion:
            break;
        case cir::EntityObjectOrigin::TemplateParameterObject:
            break;
        case cir::EntityObjectOrigin::StringLiteral:
            session.report_error(
                std::string(subject) + " must not point to a string literal",
                loc);
            return false;
        case cir::EntityObjectOrigin::TypeInfo:
            session.report_error(
                std::string(subject) + " must not point to a typeid result",
                loc);
            return false;
        case cir::EntityObjectOrigin::PredefinedFunctionVariable:
            session.report_error(
                std::string(subject) +
                    " must not point to a predefined function variable",
                loc);
            return false;
        case cir::EntityObjectOrigin::Ordinary:
            break;
    }

    if (target.storage_duration == cir::StorageDuration::Automatic ||
        target.storage_duration == cir::StorageDuration::Parameter ||
        target.storage_duration == cir::StorageDuration::Temporary) {
        session.report_error(
            std::string(subject) + " must have static storage duration",
            loc);
        return false;
    }
    return true;
}

bool build_template_address_constant(Session& session,
                                     cir::EntityId entity,
                                     int64_t byte_offset,
                                     uint64_t allocation_id,
                                     Session::TemplateValueConstant& value,
                                     const char* subject,
                                     SrcLoc loc) {
    if (!validate_template_address_target(session,
                                          entity,
                                          allocation_id,
                                          subject,
                                          loc)) {
        return false;
    }
    value = Session::TemplateValueConstant{};
    value.kind = cir::TemplateValueKind::Address;
    value.entity = entity;
    value.byte_offset = byte_offset;
    return true;
}

bool build_template_address_constant(Session& session,
                                     const ConstAddressValue& address,
                                     Session::TemplateValueConstant& value,
                                     const char* subject,
                                     SrcLoc loc) {
    if (address.string_literal.valid()) {
        session.report_error(
            std::string(subject) + " must not point to a string literal",
            loc);
        return false;
    }
    return build_template_address_constant(session,
                                           address.entity,
                                           address.byte_offset,
                                           address.allocation_id,
                                           value,
                                           subject,
                                           loc);
}

std::optional<size_t> find_record_field_index(const cir::File& file,
                                              const cir::RecordFacts& facts,
                                              std::string_view name) {
    for (size_t index = 0; index < facts.fields.size(); ++index) {
        const cir::RecordFieldFact& field = facts.fields[index];
        if (field.name.valid() && file.name(field.name) == name) {
            return index;
        }
    }
    return std::nullopt;
}

std::optional<size_t> next_initializable_field(const cir::RecordFacts& facts, size_t cursor) {
    for (size_t index = cursor; index < facts.fields.size(); ++index) {
        if (is_named_initializable_field(facts.fields[index])) {
            return index;
        }
    }
    return std::nullopt;
}

void write_integer_bytes(const cir::File& file,
                         std::vector<uint8_t>& bytes,
                         size_t offset,
                         size_t size,
                         cir::IntegerValue value) {
    if (offset >= bytes.size()) {
        return;
    }
    uint8_t sign_fill = value.is_negative() ? 0xff : 0x00;
    abi::write_scalar_bits(bytes.data() + offset,
                           std::min(size, bytes.size() - offset),
                           value.low_bits,
                           value.high_bits,
                           file.target_info().endianness,
                           sign_fill);
}

void write_integer_bytes(const cir::File& file,
                         std::vector<uint8_t>& bytes,
                         size_t offset,
                         size_t size,
                         int64_t value) {
    write_integer_bytes(file, bytes, offset, size,
                        cir::IntegerValue::from_signed(value, 64));
}

int64_t read_signed_integer_bytes(const cir::File& file,
                                  const std::vector<uint8_t>& bytes,
                                  size_t offset,
                                  size_t size) {
    if (offset >= bytes.size()) {
        return 0;
    }
    size_t count = std::min(size, bytes.size() - offset);
    abi::ScalarBits raw = abi::read_scalar_bits(
        bytes.data() + offset, count, file.target_info().endianness);
    size_t bits = std::min<size_t>(count, sizeof(uint64_t)) * 8;
    uint64_t value = raw.low;
    if (bits != 0 && bits < 64 &&
        (value & (uint64_t{1} << (bits - 1))) != 0) {
        value |= (~uint64_t{0}) << bits;
    }
    return static_cast<int64_t>(value);
}

bool bytes_are_zero(const std::vector<uint8_t>& bytes) {
    return std::all_of(bytes.begin(), bytes.end(), [](uint8_t byte) {
        return byte == 0;
    });
}

bool try_evaluate_semantic_integer_constant(const cir::File& file,
                                            const ExprResult& expr,
                                            cir::IntegerValue& value) {
    if (!expr.entity.valid() || !file.valid(expr.entity)) {
        return false;
    }
    const cir::Entity& entity = file.entity(expr.entity);
    cir::TypeId type = file.resolved_type(entity.type);
    if (entity.kind != cir::EntityKind::Variable ||
        !entity.has_constant_value ||
        (entity.qualifiers & cir::QualConst) == 0 ||
        (entity.qualifiers & cir::QualVolatile) != 0 ||
        !file.valid(type) || !cir::is_integer_like_type(file, type) ||
        (entity.constant_value_kind != cir::TemplateValueKind::Integer &&
         entity.constant_value_kind != cir::TemplateValueKind::Boolean)) {
        return false;
    }

    value = entity.constant_integer_value;
    return true;
}

bool try_evaluate_semantic_integer_constant(const cir::File& file,
                                            const ExprResult& expr,
                                            int64_t& value) {
    cir::IntegerValue exact;
    if (!try_evaluate_semantic_integer_constant(file, expr, exact)) {
        return false;
    }
    if (std::optional<int64_t> converted = exact.try_as_int64()) {
        value = *converted;
        return true;
    }
    if (exact.bit_width <= 64) {
        value = static_cast<int64_t>(exact.low_bits);
        return true;
    }
    return false;
}

} // namespace

ExprResult Session::collect_init_list_expr(std::vector<InitElementInput> elements,
                                           SrcLoc loc,
                                           InitListSyntax syntax) {
    bool has_error = false;
    for (const InitElementInput& element : elements) {
        has_error = has_error || element.value.has_error;
        for (const InitDesignator& designator : element.designators) {
            has_error = has_error || designator.index.has_error || designator.range_end.has_error;
        }
    }

    auto value = std::make_shared<InitListValue>();
    value->elements = std::move(elements);
    value->loc = loc;
    value->syntax = syntax;
    value->has_error = has_error;

    ExprResult result;
    result.type = builder_.unknown_type();
    result.init_list = std::move(value);
    result.category = ValueCategory::InitList;
    result.has_error = has_error;
    return result;
}

bool Session::is_aggregate_type(cir::TypeId type_id) const {
    if (!file_.valid(type_id)) {
        return false;
    }
    type_id = file_.resolved_type(type_id);
    if (!file_.valid(type_id)) {
        return false;
    }
    cir::TypeKind kind = file_.type(type_id).kind;
    if (kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(type_id);
        return facts &&
            facts->is_aggregate == cir::ClassPropertyState::True;
    }
    return kind == cir::TypeKind::Array ||
           kind == cir::TypeKind::Vector;
}

cir::TypeId Session::aggregate_child_type(cir::TypeId type_id, size_t index, SrcLoc loc) const {
    type_id = file_.resolved_type(type_id);
    if (!file_.valid(type_id)) {
        return {};
    }

    const cir::Type& type = file_.type(type_id);
    if (type.kind == cir::TypeKind::Array) {
        std::optional<size_t> size = array_size(file_, type_id);
        if (size.has_value() && index >= *size) {
            const_cast<Session*>(this)->report_error("array initializer index is out of bounds", loc);
            return {};
        }
        return array_element_type(file_, type_id);
    }

    if (type.kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(type_id);
        if (!facts || facts->is_incomplete || index >= facts->fields.size()) {
            const_cast<Session*>(this)->report_error("record initializer index is out of bounds", loc);
            return {};
        }
        return facts->fields[index].type.type;
    }

    if (type.kind == cir::TypeKind::Vector) {
        uint32_t size = file_.vector_element_count(type_id);
        if (size != 0 && index >= size) {
            const_cast<Session*>(this)->report_error("vector initializer index is out of bounds", loc);
            return {};
        }
        return vector_element_type(file_, type_id);
    }

    return {};
}

bool Session::eval_integer_constant(const ExprResult& expr, int64_t& value, SrcLoc loc) {
    return eval_integer_constant(expr,
                                 value,
                                 loc,
                                 "initializer designator is not an integer constant expression");
}

bool Session::evaluate_integer_constant(const ExprResult& expr,
                                        int64_t& value,
                                        SrcLoc loc,
                                        std::string_view diagnostic) {
    return eval_integer_constant(expr, value, loc, diagnostic);
}

bool Session::eval_integer_constant(const ExprResult& expr,
                                    int64_t& value,
                                    SrcLoc loc,
                                    std::string_view diagnostic) {
    if (try_evaluate_semantic_integer_constant(file_, expr, value)) {
        return true;
    }
    if (!expr.value.valid()) {
        report_error(std::string(diagnostic), loc);
        return false;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::c_ice();
    request.loc = loc;
    request.required = true;

    ConstEvalResult result =
        engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value), request);
    if (result.status == ConstEvalStatus::Constant) {
        if (result.value.has_value()) {
            if (std::optional<int64_t> converted =
                    result.value->try_as_int64()) {
                value = *converted;
                return true;
            }
            if (result.value->kind == ConstValueKind::Integer &&
                result.value->int_value.bit_width <= 64) {
                value = static_cast<int64_t>(
                    result.value->int_value.low_bits);
                return true;
            }
        }
    }

    if (result.status == ConstEvalStatus::Error && !result.diagnostics.empty()) {
        report_error(result.diagnostics.front().message,
                     result.diagnostics.front().loc);
    } else {
        report_error(std::string(diagnostic), loc);
    }
    return false;
}

bool Session::try_evaluate_integer_constant(
    const ExprResult& expr,
    int64_t& value,
    cir::EntityId* dependency) {
    cir::IntegerValue exact;
    if (!try_evaluate_integer_constant_value(expr, exact, dependency)) {
        return false;
    }
    if (std::optional<int64_t> signed_value = exact.try_as_int64()) {
        value = *signed_value;
        return true;
    }

    if (exact.bit_width <= 64) {
        value = static_cast<int64_t>(exact.low_bits);
        return true;
    }
    return false;
}

bool Session::try_evaluate_integer_constant_value(
    const ExprResult& expr,
    cir::IntegerValue& value,
    cir::EntityId* dependency) {
    if (dependency) {
        *dependency = {};
    }
    if (try_evaluate_semantic_integer_constant(file_, expr, value)) {
        return true;
    }
    if (!expr.value.valid()) {
        return false;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::c_ice();
    request.required = false;

    ConstEvalResult result =
        engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value), request);
    if (result.status == ConstEvalStatus::Constant) {
        if (result.value.has_value() &&
            result.value->kind == ConstValueKind::Integer) {
            value = result.value->int_value;
            return true;
        }
        if (result.value.has_value() &&
            result.value->kind == ConstValueKind::Boolean) {
            value = cir::IntegerValue::from_unsigned(
                result.value->bool_value ? 1 : 0, 1);
            return true;
        }
    }
    if (dependency) {
        *dependency = result.dependency_entity;
    }
    return false;
}

bool Session::try_evaluate_required_integer_constant(const ExprResult& expr,
                                                     int64_t& value,
                                                     SrcLoc loc) {
    if (try_evaluate_semantic_integer_constant(file_, expr, value)) {
        return true;
    }
    if (!expr.value.valid()) {
        return false;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::c_ice();
    request.loc = loc;
    request.required = true;

    ConstEvalResult result =
        engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value), request);
    if (result.status == ConstEvalStatus::Constant) {
        if (result.value.has_value()) {
            if (std::optional<int64_t> converted =
                    result.value->try_as_int64()) {
                value = *converted;
                return true;
            }
            if (result.value->kind == ConstValueKind::Integer &&
                result.value->int_value.bit_width <= 64) {
                value = static_cast<int64_t>(
                    result.value->int_value.low_bits);
                return true;
            }
        }
    }
    return false;
}

bool Session::evaluate_constraint_expression(ExprResult expr,
                                             bool value_dependent,
                                             std::optional<bool>& value,
                                             SrcLoc loc) {
    value.reset();
    if (expr.has_error) {
        return false;
    }

    ExprResult result = require_value(std::move(expr), UseContext::RValue, loc);
    if (result.has_error) {
        return false;
    }
    bool type_dependent = expr_is_dependent(result);
    if (type_dependent) {
        return true;
    }
    if (!is_bool_type(result.type)) {
        report_error("constraint-expression shall have type bool", loc);
        return false;
    }
    if (value_dependent || result.references_template_value_parameter) {
        return true;
    }
    if (!result.value.valid()) {
        report_error("constraint-expression is not a constant expression", loc);
        return false;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_core_constant_expression();
    request.loc = loc;
    request.required = true;

    ConstEvalResult evaluated =
        engine.evaluate_fragment(result.fragment,
                                 cir::ValueRef(result.value),
                                 request);
    if (evaluated.status == ConstEvalStatus::Constant &&
        evaluated.value.has_value() &&
        evaluated.value->kind == ConstValueKind::Boolean) {
        value = evaluated.value->bool_value;
        return true;
    }

    if ((evaluated.status == ConstEvalStatus::Error ||
         evaluated.status == ConstEvalStatus::Unsupported) &&
        !evaluated.diagnostics.empty()) {
        report_error(evaluated.diagnostics.front().message,
                     evaluated.diagnostics.front().loc);
    } else {
        report_error("constraint-expression is not a constant expression", loc);
    }
    return false;
}

bool Session::evaluate_template_value_constant(ExprResult expr,
                                               cir::TypeId expected_type,
                                               TemplateValueConstant& value,
                                               SrcLoc loc,
                                               std::string_view diagnostic) {
    cir::TypeId expected = file_.resolved_type(expected_type);
    if (file_.valid(expected) &&
        file_.template_value_kind_for_type(expected) ==
            cir::TemplateValueKind::Closure &&
        !lang_opts_.is_cxx20_or_later()) {
        report_error(
            "lambda closure template arguments require C++20",
            loc);
        return false;
    }
    bool expects_structural_object =
        file_.valid(expected) &&
        file_.template_value_kind_for_type(expected) ==
            cir::TemplateValueKind::StructuralObject;
    if (expects_structural_object &&
        file_.type(expected).kind == cir::TypeKind::Record &&
        record_has_user_constructor(expected)) {
        if (!lang_opts_.consteval_function_interpreter_enabled()) {
            report_error(
                "class template parameter object initialization with constructors requires constexpr function interpretation",
                loc);
            return false;
        }
    }
    if (file_.valid(expected) &&
        expects_structural_object &&
        expr.category == ValueCategory::InitList &&
        (file_.type(expected).kind != cir::TypeKind::Record ||
         !record_has_user_constructor(expected))) {
        cir::EntityId active_union_member{};
        if (file_.type(expected).kind == cir::TypeKind::Record) {
            const cir::RecordFacts* facts = file_.record_facts_for_type(expected);
            if (facts && facts->kind == cir::RecordKind::Union &&
                expr.init_list && !expr.init_list->elements.empty()) {
                const InitElementInput& first = expr.init_list->elements.front();
                if (!first.designators.empty() &&
                    first.designators.front().kind == InitDesignatorKind::Field) {
                    std::string_view selected =
                        first.designators.front().field_name;
                    for (const cir::RecordFieldFact& field : facts->fields) {
                        if (field.name.valid() &&
                            file_.name(field.name) == selected) {
                            active_union_member = field.entity;
                            break;
                        }
                    }
                } else {
                    for (const cir::RecordFieldFact& field : facts->fields) {
                        if (!field.is_virtual_base_storage &&
                            !field.is_flexible_array_member) {
                            active_union_member = field.entity;
                            break;
                        }
                    }
                }
            }
        }
        std::vector<cir::StaticInitializerRelocation> relocations;
        std::optional<std::vector<uint8_t>> bytes =
            static_initializer_bytes(expected_type,
                                     std::move(expr),
                                     loc,
                                     &relocations);
        if (!bytes.has_value()) {
            return false;
        }
        bool converted = template_value_constant_from_static_bytes(
            expected_type, *bytes, 0, &relocations, value, loc);
        if (converted && active_union_member.valid()) {
            value.entity = active_union_member;
        }
        return converted;
    }
    if (file_.valid(expected) &&
        file_.template_value_kind_for_type(expected) ==
            cir::TemplateValueKind::StructuralObject &&
        expr.place.valid() &&
        !expr.has_error) {
        const cir::Inst& place = file_.inst(expr.place);
        if (place.place_fact.valid() && file_.valid(place.place_fact)) {
            const cir::PlaceFact& fact = file_.place_fact(place.place_fact);
            if (fact.entity.valid() && file_.valid(fact.entity)) {
                const cir::Entity& entity = file_.entity(fact.entity);
                if (entity.decl_flags.is_constexpr &&
                    entity.has_static_initializer &&
                    type_equal(entity.type, expected_type)) {
                    return template_value_constant_from_static_bytes(
                        expected_type,
                        entity.static_initializer_bytes,
                        0,
                        &entity.static_initializer_relocations,
                        value,
                        loc);
                }
            }
        }
    }
    if ((expr.category == ValueCategory::OverloadDesignator &&
         member_pointer_payload(file_, expected)) ||
        expr.category == ValueCategory::MemberPointerDesignator ||
        (expr.category == ValueCategory::PrValue &&
         expr.entity.valid() && member_pointer_payload(file_, expected))) {
        if (expr.has_error) {
            return false;
        }
        const cir::MemberPointerTypePayload* target =
            member_pointer_payload(file_, expected);
        if (!target) {
            report_error("template argument is not a converted constant expression",
                         loc);
            return false;
        }
        if (expr.category == ValueCategory::OverloadDesignator) {
            std::shared_ptr<const OverloadDesignator> designator =
                canonical_overload_designator(expr);
            std::vector<cir::EntityId> candidates;
            if (designator) {
                for (const OverloadDesignatorCandidate& candidate :
                     designator->candidates) {
                    if (candidate.address_category ==
                        OverloadAddressCategory::MemberPointer) {
                        candidates.push_back(candidate.entity);
                    }
                }
            }
            std::vector<cir::EntityId> selected =
                select_member_pointer_targets(
                    candidates,
                    expected,
                    loc,
                    !designator ||
                            designator->explicit_template_arguments.empty()
                        ? nullptr
                        : &designator->explicit_template_arguments,
                    !designator
                        ? nullptr
                        : &designator
                               ->candidate_explicit_template_arguments);
            if (selected.empty()) {
                report_error("no matching member function for template argument",
                             loc);
                return false;
            }
            if (selected.size() > 1) {
                report_error("member function template argument is ambiguous",
                             loc);
                return false;
            }
            expr.entity = selected.front();
            expr.type = expected_type;
            expr.category = ValueCategory::MemberPointerDesignator;
        }
        if (expr.type.valid() &&
            file_.resolved_type(expr.type) != expected) {
            report_error("member pointer template argument has incompatible type",
                         loc);
            return false;
        }
        if (!expr.entity.valid() ||
            !file_.valid(expr.entity) ||
            (file_.entity(expr.entity).kind != cir::EntityKind::Field &&
             file_.entity(expr.entity).kind != cir::EntityKind::Method)) {
            report_error(std::string(diagnostic), loc);
            return false;
        }
        value.kind = cir::TemplateValueKind::MemberPointer;
        value.entity = expr.entity;
        if (const cir::RecordFieldFact* field = file_.field_fact(expr.entity)) {
            value.byte_offset = static_cast<int64_t>(field->offset);
        }
        if (file_.entity(expr.entity).kind == cir::EntityKind::Method) {
            mark_record_method_required(expr.entity, loc);
        }
        return true;
    }
    bool expects_reference = file_.valid(expected) &&
        (file_.type(expected).kind == cir::TypeKind::LValueReference ||
         file_.type(expected).kind == cir::TypeKind::RValueReference);
    if (expects_reference) {
        if (expr.category == ValueCategory::OverloadDesignator) {
            expr = convert_overload_designator_to_target(std::move(expr),
                                                         expected_type,
                                                         loc);
            if (expr.has_error || !expr.value.valid()) {
                report_error(std::string(diagnostic), loc);
                return false;
            }
        } else if (expr.category == ValueCategory::FunctionDesignator) {
            expr = convert_function_designator_to_target(std::move(expr),
                                                         expected_type,
                                                         loc);
            if (expr.has_error || !expr.value.valid()) {
                report_error(std::string(diagnostic), loc);
                return false;
            }
        } else {

            if (expr.category != ValueCategory::LValue || !expr.place.valid()) {
                report_error(
                    "reference template argument cannot bind to a temporary",
                    loc);
                return false;
            }
            ExprResult place =
                require_place(std::move(expr), UseContext::LValue, loc);
            if (!place.place.valid()) {
                report_error(std::string(diagnostic), loc);
                return false;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.template_ref_addr");
            cir::InstId address = builder_.addr_of(place.place, loc);
            cir::Fragment address_fragment =
                finish_fragment_block(block, previous);
            place.fragment = chain(std::move(place.fragment),
                                   std::move(address_fragment), loc);
            place.value = address;
            place.type = file_.inst(address).result_type;
            place.category = ValueCategory::PrValue;
            expr = std::move(place);
        }
    } else {
        if (expr.category == ValueCategory::OverloadDesignator) {
            expr = convert_overload_designator_to_target(std::move(expr),
                                                         expected_type,
                                                         loc);
        } else if (expr.category == ValueCategory::FunctionDesignator &&
                   (!expr.candidates.empty() ||
                    expr.overload_designator)) {
            expr = convert_function_designator_to_target(std::move(expr),
                                                         expected_type,
                                                         loc);
        }
        expr = require_value(std::move(expr), UseContext::RValue, loc);
    }
    if (!expr.value.valid()) {
        report_error(std::string(diagnostic), loc);
        return false;
    }

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_non_type_template_argument();
    request.target_type = expected_type;
    request.loc = loc;
    request.required = true;

    ConstEvalResult result =
        engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value), request);
    if (result.status != ConstEvalStatus::Constant || !result.value.has_value()) {
        if (result.status == ConstEvalStatus::Error &&
            !result.diagnostics.empty()) {
            report_error(result.diagnostics.front().message,
                         result.diagnostics.front().loc);
        } else {
            report_error(std::string(diagnostic), loc);
        }
        return false;
    }

    const ConstValue& constant = *result.value;
    switch (constant.kind) {
        case ConstValueKind::Integer:
            value.kind = cir::TemplateValueKind::Integer;
            value.integer_value = constant.int_value;
            return true;
        case ConstValueKind::Boolean:
            value.kind = cir::TemplateValueKind::Boolean;
            value.integer_value = cir::IntegerValue::from_unsigned(
                constant.bool_value ? 1 : 0, 1);
            return true;
        case ConstValueKind::Floating:
            value.kind = cir::TemplateValueKind::Floating;
            value.floating_value = constant.float_value.value;
            return true;
        case ConstValueKind::Null:
            value.kind = cir::TemplateValueKind::Null;
            value.null_kind = template_null_kind_from_const(constant.null_kind);
            return true;
        case ConstValueKind::MemberPointer:
            value.kind = cir::TemplateValueKind::MemberPointer;
            value.entity = constant.member_pointer_value.method_entity;
            value.byte_offset = constant.member_pointer_value.byte_offset;
            return true;
        case ConstValueKind::MetaInfo: {
            const std::shared_ptr<ConstMetaInfoValue>& handle =
                constant.meta_info_value;
            value.kind = cir::TemplateValueKind::MetaInfo;
            if (handle) {
                value.meta_kind = handle->kind;
                value.meta_type = handle->type;
                value.entity = handle->entity;
            }
            return true;
        }
        case ConstValueKind::Object:
            if (file_.valid(expected) &&
                (file_.template_value_kind_for_type(expected) ==
                     cir::TemplateValueKind::StructuralObject ||
                 file_.template_value_kind_for_type(expected) ==
                     cir::TemplateValueKind::Closure)) {
                if (file_.type(expected).kind == cir::TypeKind::Record &&
                    record_has_user_constructor(expected) &&
                    record_has_non_defaulted_copy_constructor(file_, expected) &&
                    !validate_template_parameter_object_copy(expected_type,
                                                             expr,
                                                             constant,
                                                             loc)) {
                    return false;
                }
                return template_value_constant_from_const_value(expected_type,
                                                                constant,
                                                                value,
                                                                loc);
            }
            report_error(std::string(diagnostic), loc);
            return false;
        case ConstValueKind::Address:
            return build_template_address_constant(*this,
                                                   constant.address_value,
                                                   value,
                                                   "template address argument",
                                                   loc);
        default:
            report_error(std::string(diagnostic), loc);
            return false;
    }
}

bool Session::validate_template_parameter_object_copy(
    cir::TypeId type,
    const ExprResult& candidate,
    const ConstValue& candidate_value,
    SrcLoc loc) {
    cir::InstId source_place = loaded_place_for_value(file_, candidate.value);
    ExprResult source;
    std::vector<ConstEvalObjectSeed> object_seeds;
    if (source_place.valid()) {
        source.fragment = candidate.fragment;
    } else {
        std::string source_name =
            ".nttp.candidate.object." +
            std::to_string(compound_literal_counter_++);
        cir::EntityId source_entity =
            builder_.add_entity(cir::EntityKind::Variable,
                                source_name,
                                type,
                                {},
                                loc,
                                cir::StorageDuration::Automatic,
                                cir::MemorySpace::Default,
                                {});
        file_.entity_mut(source_entity).is_definition = true;
        file_.entity_mut(source_entity).qualifiers = cir::QualConst;

        cir::BlockId source_previous = builder_.current_block();
        cir::BlockId source_block =
            begin_fragment_block("nttp.candidate.object.place");
        source_place = builder_.local_place(source_entity, type, loc);
        source.fragment = finish_fragment_block(source_block, source_previous);
        object_seeds.push_back(ConstEvalObjectSeed{
            source_entity,
            type,
            candidate_value,
            loc,
        });
    }
    source.place = source_place;
    source.type = type;
    source.category = ValueCategory::LValue;

    std::vector<ExprResult> arguments;
    arguments.push_back(std::move(source));
    ConstructorCallMaterialization materialized =
        materialize_constructor_call(type, std::move(arguments), loc);
    if (!materialized.constructor.valid()) {
        report_error(
            std::string(materialized.ambiguous
                            ? "ambiguous copy constructor for class template parameter object"
                            : "no matching copy constructor for class template parameter object"),
            loc);
        return false;
    }
    if (materialized.has_error) {
        return false;
    }

    std::string temp_name =
        ".nttp.parameter.object.copy." +
        std::to_string(compound_literal_counter_++);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;

    cir::BlockId place_previous = builder_.current_block();
    cir::BlockId place_block = begin_fragment_block("nttp.parameter.object.place");
    cir::InstId place = builder_.local_place(temp, type, loc);
    cir::Fragment place_fragment =
        finish_fragment_block(place_block, place_previous);

    cir::BlockId construct_previous = builder_.current_block();
    cir::BlockId construct_block =
        begin_fragment_block("nttp.parameter.object.copy");
    emit_construct_in_place(place,
                            structor_complete_variant(materialized.constructor),
                            materialized.argument_values,
                            loc);
    cir::Fragment construct_fragment =
        finish_fragment_block(construct_block, construct_previous);

    cir::BlockId load_previous = builder_.current_block();
    cir::BlockId load_block = begin_fragment_block("nttp.parameter.object.load");
    cir::InstId copied = builder_.lvalue_to_rvalue(place, loc);
    cir::Fragment load_fragment = finish_fragment_block(load_block, load_previous);

    cir::Fragment copy_fragment = chain(std::move(materialized.argument_fragment),
                                        std::move(place_fragment),
                                        loc);
    copy_fragment = chain(std::move(copy_fragment),
                          std::move(construct_fragment),
                          loc);
    copy_fragment = chain(std::move(copy_fragment),
                          std::move(load_fragment),
                          loc);

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_non_type_template_argument();
    request.target_type = type;
    request.loc = loc;
    request.required = true;

    ConstEvalResult result =
        engine.evaluate_fragment_with_object_seeds(copy_fragment,
                                                  cir::ValueRef(copied),
                                                  request,
                                                  object_seeds);
    if (result.status != ConstEvalStatus::Constant || !result.value.has_value()) {
        if (result.status == ConstEvalStatus::Error &&
            !result.diagnostics.empty()) {
            report_error(result.diagnostics.front().message,
                         result.diagnostics.front().loc);
        } else {
            report_error(
                "class template parameter object copy/equivalence is not a constant expression",
                loc);
        }
        return false;
    }

    if (!const_value_equals(candidate_value, *result.value)) {
        report_error(
            "class template parameter object copy/equivalence is not template-argument-equivalent to the candidate initializer",
            loc);
        return false;
    }
    return true;
}

bool Session::template_value_constant_from_const_value(
    cir::TypeId type,
    const ConstValue& constant,
    TemplateValueConstant& value,
    SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        report_error("structural object template argument has invalid subobject",
                     loc);
        return false;
    }

    auto build_element = [&](cir::TypeId element_type,
                             const ConstValue& element_value,
                             TemplateArgument& argument) {
        TemplateValueConstant element_constant;
        if (!template_value_constant_from_const_value(element_type,
                                                      element_value,
                                                      element_constant,
                                                      loc)) {
            return false;
        }
        std::string error;
        if (!build_template_value_argument(element_type,
                                           element_constant,
                                           argument,
                                           &error)) {
            report_error(error, loc);
            return false;
        }
        return true;
    };

    switch (file_.type(resolved).kind) {
        case cir::TypeKind::Array: {
            const auto* array =
                std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(resolved));
            if (!array || !array->size.has_value()) {
                report_error(
                    "structural object template argument has incomplete array type",
                    loc);
                return false;
            }
            if (constant.kind != ConstValueKind::Object ||
                !constant.object_value ||
                constant.object_value->kind != ConstObjectValueKind::Array ||
                constant.object_value->elements.size() != *array->size) {
                report_error(
                    "structural object template argument has invalid array value",
                    loc);
                return false;
            }
            value = TemplateValueConstant{};
            value.kind = cir::TemplateValueKind::StructuralObject;
            value.elements.reserve(*array->size);
            for (size_t index = 0; index < *array->size; ++index) {
                TemplateArgument element;
                if (!build_element(array->element_type.type,
                                   constant.object_value->elements[index],
                                   element)) {
                    return false;
                }
                value.elements.push_back(std::move(element));
            }
            return true;
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts =
                file_.record_facts_for_type(resolved);
            if (!facts || facts->is_incomplete) {
                report_error(
                    "structural object template argument has incomplete class type",
                    loc);
                return false;
            }
            if (facts->is_lambda_closure) {
                if (facts->lambda_has_capture ||
                    !file_.valid(facts->closure_identity)) {
                    report_error(
                        "capturing lambda closure type is not structural",
                        loc);
                    return false;
                }
                if (constant.kind != ConstValueKind::Object ||
                    !constant.object_value ||
                    constant.object_value->kind !=
                        ConstObjectValueKind::Record) {
                    report_error(
                        "closure template argument has invalid constant value",
                        loc);
                    return false;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Closure;
                value.closure_identity = facts->closure_identity;
                return true;
            }
            if (constant.kind != ConstValueKind::Object ||
                !constant.object_value ||
                constant.object_value->kind != ConstObjectValueKind::Record) {
                report_error(
                    "structural object template argument has invalid class value",
                    loc);
                return false;
            }
            value = TemplateValueConstant{};
            value.kind = cir::TemplateValueKind::StructuralObject;
            if (facts->kind == cir::RecordKind::Union &&
                constant.object_value->active_union_member.valid()) {
                value.entity = constant.object_value->active_union_member;
            }
            bool sparse_union = facts->kind == cir::RecordKind::Union &&
                constant.object_value->active_union_member.valid() &&
                constant.object_value->elements.size() == 1;
            size_t element_index = 0;
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (sparse_union &&
                    field.entity !=
                        constant.object_value->active_union_member) {
                    continue;
                }
                if (field.is_bitfield) {
                    report_error(
                        "structural object template arguments with bit-field subobjects are not supported yet",
                        loc);
                    return false;
                }
                if (element_index >= constant.object_value->elements.size()) {
                    report_error(
                        "structural object template argument has invalid class value",
                        loc);
                    return false;
                }
                TemplateArgument element;
                if (!build_element(
                        field.type.type,
                        constant.object_value->elements[element_index],
                        element)) {
                    return false;
                }
                value.elements.push_back(std::move(element));
                ++element_index;
            }
            if (element_index != constant.object_value->elements.size()) {
                report_error(
                    "structural object template argument has invalid class value",
                    loc);
                return false;
            }
            return true;
        }
        case cir::TypeKind::Builtin: {
            const auto* builtin =
                std::get_if<cir::BuiltinTypePayload>(
                    &file_.type_payload(resolved));
            if (builtin && builtin->kind == cir::BuiltinTypeKind::Bool) {
                if (constant.kind == ConstValueKind::Boolean) {
                    value = TemplateValueConstant{};
                    value.kind = cir::TemplateValueKind::Boolean;
                    value.integer_value = cir::IntegerValue::from_unsigned(
                        constant.bool_value ? 1 : 0, 1);
                    return true;
                }
                if (constant.kind == ConstValueKind::Integer) {
                    value = TemplateValueConstant{};
                    value.kind = cir::TemplateValueKind::Boolean;
                    value.integer_value = cir::IntegerValue::from_unsigned(
                        constant.int_value.is_zero() ? 0 : 1, 1);
                    return true;
                }
                break;
            }
            if (builtin && builtin->kind == cir::BuiltinTypeKind::NullPtr) {
                if (!constant.is_null(ConstNullKind::Nullptr)) {
                    break;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Null;
                value.null_kind = cir::TemplateNullKind::Nullptr;
                return true;
            }
            if (builtin &&
                (builtin->kind == cir::BuiltinTypeKind::Float ||
                 builtin->kind == cir::BuiltinTypeKind::Double ||
                 builtin->kind == cir::BuiltinTypeKind::LongDouble)) {
                if (constant.kind != ConstValueKind::Floating) {
                    break;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Floating;
                value.floating_value = constant.float_value.value;
                return true;
            }
            if (builtin && builtin->kind == cir::BuiltinTypeKind::MetaInfo) {
                if (constant.kind != ConstValueKind::MetaInfo) {
                    break;
                }
                const std::shared_ptr<ConstMetaInfoValue>& handle =
                    constant.meta_info_value;
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::MetaInfo;
                if (handle) {
                    value.meta_kind = handle->kind;
                    value.meta_type = handle->type;
                    value.entity = handle->entity;
                }
                return true;
            }
            break;
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
            if (constant.kind == ConstValueKind::Address) {
                return build_template_address_constant(
                    *this,
                    constant.address_value,
                    value,
                    "structural object pointer/reference subobject",
                    loc);
            }
            if (constant.is_null(ConstNullKind::Pointer) ||
                constant.is_null(ConstNullKind::Nullptr)) {
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Null;
                value.null_kind = cir::TemplateNullKind::Pointer;
                return true;
            }
            break;
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            if (constant.kind == ConstValueKind::Address) {
                return build_template_address_constant(
                    *this,
                    constant.address_value,
                    value,
                    "structural object pointer/reference subobject",
                    loc);
            }
            report_error(
                "structural object reference subobject must not bind to a temporary",
                loc);
            return false;
        case cir::TypeKind::MemberPointer:
            if (constant.kind == ConstValueKind::MemberPointer) {
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::MemberPointer;
                value.entity = constant.member_pointer_value.method_entity;
                value.byte_offset = constant.member_pointer_value.byte_offset;
                return true;
            }
            if (constant.is_null(ConstNullKind::MemberPointer) ||
                constant.is_null(ConstNullKind::Nullptr)) {
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Null;
                value.null_kind = cir::TemplateNullKind::MemberPointer;
                return true;
            }
            break;
        default:
            break;
    }

    if (cir::is_integer_like_type(file_, resolved)) {
        if (constant.kind != ConstValueKind::Integer &&
            constant.kind != ConstValueKind::Boolean) {
            report_error(
                "unsupported structural object subobject type in template argument",
                loc);
            return false;
        }
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file_, resolved);
        ConstIntValue int_value = constant.kind == ConstValueKind::Boolean
            ? ConstIntValue::from_unsigned(constant.bool_value ? 1 : 0,
                                           shape.bit_width)
            : constant.int_value.cast(shape.bit_width, shape.is_unsigned);
        value = TemplateValueConstant{};
        value.kind = cir::TemplateValueKind::Integer;
        value.integer_value = int_value;
        return true;
    }

    report_error(
        "unsupported structural object subobject type in template argument",
        loc);
    return false;
}

bool Session::template_value_constant_from_static_bytes(
    cir::TypeId type,
    const std::vector<uint8_t>& bytes,
    size_t offset,
    const std::vector<cir::StaticInitializerRelocation>* relocations,
    TemplateValueConstant& value,
    SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(type);
    std::optional<size_t> size = size_of_type(type, loc);
    if (!file_.valid(resolved) || !size.has_value() ||
        offset + *size > bytes.size()) {
        report_error("structural object template argument has invalid subobject",
                     loc);
        return false;
    }

    auto build_element = [&](cir::TypeId element_type,
                             size_t element_offset,
                             TemplateArgument& argument) {
        TemplateValueConstant element_constant;
        if (!template_value_constant_from_static_bytes(element_type,
                                                       bytes,
                                                       element_offset,
                                                       relocations,
                                                       element_constant,
                                                       loc)) {
            return false;
        }
        std::string error;
        if (!build_template_value_argument(element_type,
                                           element_constant,
                                           argument,
                                           &error)) {
            report_error(error, loc);
            return false;
        }
        return true;
    };

    switch (file_.type(resolved).kind) {
        case cir::TypeKind::Array: {
            const auto* array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(resolved));
            if (!array || !array->size.has_value()) {
                report_error(
                    "structural object template argument has incomplete array type",
                    loc);
                return false;
            }
            std::optional<size_t> element_size =
                size_of_type(array->element_type.type, loc);
            if (!element_size.has_value()) {
                return false;
            }
            value = TemplateValueConstant{};
            value.kind = cir::TemplateValueKind::StructuralObject;
            value.elements.reserve(*array->size);
            for (size_t index = 0; index < *array->size; ++index) {
                TemplateArgument element;
                if (!build_element(array->element_type.type,
                                   offset + index * *element_size,
                                   element)) {
                    return false;
                }
                value.elements.push_back(std::move(element));
            }
            return true;
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts =
                file_.record_facts_for_type(resolved);
            if (!facts || facts->is_incomplete) {
                report_error(
                    "structural object template argument has incomplete class type",
                    loc);
                return false;
            }
            if (facts->is_lambda_closure) {
                if (facts->lambda_has_capture ||
                    !file_.valid(facts->closure_identity)) {
                    report_error(
                        "capturing lambda closure type is not structural",
                        loc);
                    return false;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Closure;
                value.closure_identity = facts->closure_identity;
                return true;
            }
            value = TemplateValueConstant{};
            value.kind = cir::TemplateValueKind::StructuralObject;
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (field.is_bitfield) {
                    report_error(
                        "structural object template arguments with bit-field subobjects are not supported yet",
                        loc);
                    return false;
                }
                TemplateArgument element;
                if (!build_element(field.type.type,
                                   offset + field.offset,
                                   element)) {
                    return false;
                }
                value.elements.push_back(std::move(element));
            }
            return true;
        }
        case cir::TypeKind::Builtin: {
            const auto* builtin =
                std::get_if<cir::BuiltinTypePayload>(
                    &file_.type_payload(resolved));
            if (builtin && builtin->kind == cir::BuiltinTypeKind::Bool) {
                bool nonzero = false;
                for (size_t i = 0; i < *size; ++i) {
                    nonzero = nonzero || bytes[offset + i] != 0;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Boolean;
                value.integer_value = cir::IntegerValue::from_unsigned(
                    nonzero ? 1 : 0, 1);
                return true;
            }
            if (builtin && builtin->kind == cir::BuiltinTypeKind::NullPtr) {
                bool all_zero = true;
                for (size_t i = 0; i < *size; ++i) {
                    all_zero = all_zero && bytes[offset + i] == 0;
                }
                if (!all_zero) {
                    report_error(
                        "nullptr_t structural object subobject has non-null bytes",
                        loc);
                    return false;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Null;
                value.null_kind = cir::TemplateNullKind::Nullptr;
                return true;
            }
            break;
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {
            bool is_reference = false;
            is_pointer_or_reference_type(file_, resolved, &is_reference);
            if (const cir::StaticInitializerRelocation* relocation =
                    static_relocation_at(relocations, offset)) {
                return build_template_address_constant(
                    *this,
                    relocation->entity,
                    relocation->addend,
                    0,
                    value,
                    "structural object pointer/reference subobject",
                    loc);
            }
            if (!is_reference && bytes_are_zero(bytes, offset, *size)) {
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Null;
                value.null_kind = cir::TemplateNullKind::Pointer;
                return true;
            }
            if (is_reference) {
                report_error(
                    "structural object reference subobject must not bind to a temporary",
                    loc);
            } else {
                report_error(
                    "structural object pointer subobject must name an entity or be null",
                    loc);
            }
            return false;
        }
        case cir::TypeKind::MemberPointer: {
            bool points_to_function =
                file_.member_pointer_points_to_function(resolved);
            if (!points_to_function) {
                if (static_relocation_at(relocations, offset)) {
                    report_error(
                        "structural object data-member pointer subobject has an unexpected relocation",
                        loc);
                    return false;
                }
                int64_t member_offset =
                    read_signed_integer_bytes(file_, bytes, offset, *size);
                value = TemplateValueConstant{};
                if (member_offset == -1) {
                    value.kind = cir::TemplateValueKind::Null;
                    value.null_kind = cir::TemplateNullKind::MemberPointer;
                } else {
                    value.kind = cir::TemplateValueKind::MemberPointer;
                    value.byte_offset = member_offset;
                }
                return true;
            }

            if (const cir::StaticInitializerRelocation* relocation =
                    static_relocation_at(relocations, offset)) {
                if (!relocation->entity.valid() ||
                    !file_.method_fact(relocation->entity)) {
                    report_error(
                        "structural object member-function pointer subobject must name a method",
                        loc);
                    return false;
                }
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::MemberPointer;
                value.entity = relocation->entity;
                return true;
            }
            if (bytes_are_zero(bytes, offset, *size)) {
                value = TemplateValueConstant{};
                value.kind = cir::TemplateValueKind::Null;
                value.null_kind = cir::TemplateNullKind::MemberPointer;
                return true;
            }
            report_error(
                "structural object member-function pointer subobject must name a method relocation or be null",
                loc);
            return false;
        }
        default:
            break;
    }

    if (cir::is_integer_like_type(file_, resolved)) {
        if (*size > 16) {
            report_error(
                "structural object integer subobject is wider than 128 bits",
                loc);
            return false;
        }
        unsigned __int128 raw = 0;
        for (size_t i = 0; i < *size; ++i) {
            raw |= static_cast<unsigned __int128>(bytes[offset + i])
                   << (i * 8);
        }
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file_, resolved);
        ConstIntValue int_value =
            ConstIntValue::from_bits128(raw,
                                        shape.bit_width,
                                        shape.is_unsigned);
        value = TemplateValueConstant{};
        value.kind = cir::TemplateValueKind::Integer;
        value.integer_value = int_value;
        return true;
    }

    if (cir::is_floating_type(file_, resolved)) {
        if (*size > 16) {
            report_error(
                "structural object floating subobject is wider than 128 bits",
                loc);
            return false;
        }
        abi::ScalarBits bits = abi::read_scalar_bits(
            bytes.data() + offset,
            *size,
            file_.target_info().endianness);
        cir::FloatingSemantics semantics =
            floating::semantics_for_type(file_, resolved);
        cir::FloatingValue floating_value{semantics, bits.low, bits.high};
        if (semantics == cir::FloatingSemantics::IEEEBinary16) {
            floating_value.low_bits &= 0xffffu;
            floating_value.high_bits = 0;
        } else if (semantics == cir::FloatingSemantics::IEEEBinary32) {
            floating_value.low_bits &= 0xffffffffu;
            floating_value.high_bits = 0;
        } else if (semantics == cir::FloatingSemantics::IEEEBinary64) {
            floating_value.high_bits = 0;
        } else if (semantics == cir::FloatingSemantics::X87Extended80) {
            floating_value.high_bits &= 0xffffu;
        }
        if (!floating_value.canonical()) {
            report_error(
                "structural object floating subobject has invalid bits",
                loc);
            return false;
        }
        value = TemplateValueConstant{};
        value.kind = cir::TemplateValueKind::Floating;
        value.floating_value = floating_value;
        return true;
    }

    report_error(
        "unsupported structural object subobject type in template argument",
        loc);
    return false;
}

InferredArrayBound Session::infer_array_initializer_bound(
    cir::TypeId type,
    const ExprResult& initializer,
    SrcLoc loc) {
    const cir::ArrayTypePayload* array = array_payload(file_, type);
    if (!array) {
        return {};
    }

    const ExprResult* string_expr = nullptr;
    if (string_literal_bytes(file_, initializer)) {
        string_expr = &initializer;
    } else if (initializer.category == ValueCategory::InitList &&
               initializer.init_list &&
               initializer.init_list->elements.size() == 1 &&
               initializer.init_list->elements.front().designators.empty() &&
               string_literal_bytes(
                   file_, initializer.init_list->elements.front().value)) {
        string_expr = &initializer.init_list->elements.front().value;
    }
    if (string_expr) {
        std::optional<size_t> unit_width =
            string_literal_unit_width(file_, *string_expr);
        if (unit_width && array_accepts_string_literal(file_, type, *unit_width)) {
            const cir::LiteralByteArray* bytes =
                string_literal_bytes(file_, *string_expr);
            return {InferredArrayBoundKind::Concrete,
                    bytes->size() / *unit_width + 1};
        }
    }

    if (initializer.category != ValueCategory::InitList || !initializer.init_list) {
        return {};
    }

    bool dependent = initializer_contains_unbound_pack_expansion(initializer);
    size_t cursor = 0;
    size_t inferred = 0;
    for (const InitElementInput& element : initializer.init_list->elements) {
        if (element.designators.empty()) {
            inferred = std::max(inferred, cursor + 1);
            ++cursor;
            continue;
        }

        const InitDesignator& first = element.designators.front();
        if (first.kind == InitDesignatorKind::Field) {
            report_error("field designator cannot complete an array type", first.loc);
            return {InferredArrayBoundKind::Invalid, 0};
        }
        int64_t begin = 0;
        if (!eval_integer_constant(first.index, begin, first.loc)) {
            return {InferredArrayBoundKind::Invalid, 0};
        }
        int64_t end = begin;
        if (first.kind == InitDesignatorKind::Range &&
            !eval_integer_constant(first.range_end, end, first.loc)) {
            return {InferredArrayBoundKind::Invalid, 0};
        }
        if (begin < 0 || end < begin) {
            report_error("array designator range cannot complete an array type", first.loc);
            return {InferredArrayBoundKind::Invalid, 0};
        }
        if (static_cast<uint64_t>(end) >=
            static_cast<uint64_t>(std::numeric_limits<size_t>::max())) {
            report_error("array initializer designator is too large", first.loc);
            return {InferredArrayBoundKind::Invalid, 0};
        }
        inferred = std::max(inferred, static_cast<size_t>(end) + 1);
        cursor = static_cast<size_t>(end) + 1;
    }
    return {dependent ? InferredArrayBoundKind::Dependent
                      : InferredArrayBoundKind::Concrete,
            inferred};
}

cir::TypeId Session::complete_initializer_type(cir::TypeId type,
                                               const ExprResult& initializer,
                                               SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(type);
    const cir::ArrayTypePayload* array = array_payload(file_, resolved);
    if (!array || array->size_kind != cir::ArraySizeKind::Incomplete) {
        return type;
    }
    InferredArrayBound inferred =
        infer_array_initializer_bound(resolved, initializer, loc);
    switch (inferred.kind) {
        case InferredArrayBoundKind::NotInferable:
        case InferredArrayBoundKind::Invalid:
            return type;
        case InferredArrayBoundKind::Dependent:

            bump_pattern_taint();
            return array_type(array->element_type,
                              cir::ArraySizeKind::Variable,
                              std::nullopt,
                              {},
                              true);
        case InferredArrayBoundKind::Concrete:
            if (inferred.size == 0) {
                if (lang_opts_.is_gnu_mode()) {
                    return array_type(array->element_type, size_t{0});
                }
                report_error(
                    "array initializer must contain at least one element to infer a bound",
                    loc);
                return type;
            }
            return array_type(array->element_type, inferred.size);
    }
    return type;
}

std::optional<std::vector<uint8_t>> Session::string_literal_initializer_bytes(
    cir::TypeId type,
    const ExprResult& initializer,
    SrcLoc loc) {

    const ExprResult* string_expr = nullptr;
    const cir::LiteralByteArray* literal = string_literal_bytes(file_, initializer);
    if (literal) {
        string_expr = &initializer;
    } else if (initializer.category == ValueCategory::InitList &&
               initializer.init_list &&
               initializer.init_list->elements.size() == 1 &&
               initializer.init_list->elements.front().designators.empty()) {
        literal = string_literal_bytes(
            file_, initializer.init_list->elements.front().value);
        if (literal) {
            string_expr = &initializer.init_list->elements.front().value;
        }
    }
    if (!literal) {
        return std::nullopt;
    }
    std::optional<size_t> unit_width =
        string_literal_unit_width(file_, *string_expr);
    if (!unit_width || !array_accepts_string_literal(file_, type, *unit_width)) {
        return std::nullopt;
    }

    std::optional<size_t> object_size = size_of_type(type, loc);
    if (!object_size.has_value()) {
        return std::nullopt;
    }
    if (*object_size < literal->size()) {
        report_error("string literal initializer is too long for character array", loc);
        return std::nullopt;
    }

    std::vector<uint8_t> bytes(*object_size, 0);
    std::copy(literal->begin(), literal->end(), bytes.begin());
    return bytes;
}

bool Session::resolve_initializer_designators(const std::vector<InitDesignator>& designators,
                                              cir::TypeId base_type,
                                              std::vector<InitPath>& paths,
                                              size_t& outer_end,
                                              bool& has_range) {
    paths.clear();
    paths.push_back(InitPath{{}, base_type});
    outer_end = 0;
    has_range = false;
    bool ok = true;
    bool outer_end_set = false;

    for (size_t designator_index = 0; designator_index < designators.size(); ++designator_index) {
        const InitDesignator& designator = designators[designator_index];
        std::vector<InitPath> next_paths;
        for (const InitPath& path : paths) {
            cir::TypeId current_type = file_.resolved_type(path.target_type);
            if (!file_.valid(current_type)) {
                ok = false;
                continue;
            }

            if (designator.kind == InitDesignatorKind::Field) {
                if (file_.type(current_type).kind != cir::TypeKind::Record) {
                    report_error("field designator requires a record initializer", designator.loc);
                    ok = false;
                    continue;
                }
                const cir::RecordFacts* facts = file_.record_facts_for_type(current_type);
                if (!facts || facts->is_incomplete) {
                    report_error("field designator requires a complete record type", designator.loc);
                    ok = false;
                    continue;
                }
                std::optional<size_t> field_index =
                    find_record_field_index(file_, *facts, designator.field_name);
                if (!field_index.has_value()) {
                    FieldPathLookupResult lookup =
                        lookup_field_path(current_type, designator.field_name);
                    if (!lookup.found) {
                        report_error("record initializer has no field named '" +
                                         designator.field_name + "'",
                                     designator.loc);
                        ok = false;
                        continue;
                    }
                    if (lookup.ambiguous) {
                        report_error("field designator '" + designator.field_name +
                                         "' is ambiguous through anonymous members",
                                     designator.loc);
                        ok = false;
                        continue;
                    }
                    InitPath promoted = path;
                    cir::TypeId walk_type = current_type;
                    for (cir::EntityId entity : lookup.entities) {
                        const cir::RecordFacts* walk_facts =
                            file_.record_facts_for_type(walk_type);
                        if (!walk_facts || walk_facts->is_incomplete) {
                            ok = false;
                            break;
                        }
                        auto found = std::find_if(
                            walk_facts->fields.begin(),
                            walk_facts->fields.end(),
                            [&](const cir::RecordFieldFact& field) {
                                return field.entity == entity;
                            });
                        if (found == walk_facts->fields.end()) {
                            ok = false;
                            break;
                        }
                        promoted.indices.push_back(
                            static_cast<size_t>(found - walk_facts->fields.begin()));
                        promoted.target_type = found->type.type;
                        walk_type = file_.resolved_type(found->type.type);
                    }
                    if (!ok) {
                        continue;
                    }
                    if (designator_index == 0 && !outer_end_set &&
                        promoted.indices.size() > path.indices.size()) {
                        outer_end = promoted.indices[path.indices.size()] + 1;
                        outer_end_set = true;
                    }
                    next_paths.push_back(std::move(promoted));
                    continue;
                }
                InitPath next = path;
                next.indices.push_back(*field_index);
                next.target_type = facts->fields[*field_index].type.type;
                next_paths.push_back(std::move(next));
                if (designator_index == 0 && !outer_end_set) {
                    outer_end = *field_index + 1;
                    outer_end_set = true;
                }
                continue;
            }

            if (file_.type(current_type).kind != cir::TypeKind::Array) {
                report_error("array designator requires an array initializer", designator.loc);
                ok = false;
                continue;
            }

            int64_t begin = 0;
            if (!eval_integer_constant(designator.index, begin, designator.loc)) {
                ok = false;
                continue;
            }
            int64_t end = begin;
            if (designator.kind == InitDesignatorKind::Range) {
                has_range = true;
                if (!eval_integer_constant(designator.range_end, end, designator.loc)) {
                    ok = false;
                    continue;
                }
                if (end < begin) {
                    report_error("initializer range designator has an empty range", designator.loc);
                    ok = false;
                    continue;
                }
            }
            if (begin < 0) {
                report_error("array designator index must be non-negative", designator.loc);
                ok = false;
                continue;
            }

            std::optional<size_t> known_size = array_size(file_, current_type);
            cir::TypeId element_type = array_element_type(file_, current_type);
            for (int64_t value = begin; value <= end; ++value) {
                size_t index = static_cast<size_t>(value);
                if (known_size.has_value() && index >= *known_size) {
                    report_error("array designator index is out of bounds", designator.loc);
                    ok = false;
                    continue;
                }
                InitPath next = path;
                next.indices.push_back(index);
                next.target_type = element_type;
                next_paths.push_back(std::move(next));
                if (value == std::numeric_limits<int64_t>::max()) {
                    break;
                }
            }
            if (designator_index == 0 && !outer_end_set) {
                outer_end = static_cast<size_t>(end) + 1;
                outer_end_set = true;
            }
        }
        paths = std::move(next_paths);
    }

    return ok && !paths.empty();
}

bool Session::try_evaluate_floating_constant(const ExprResult& expr,
                                             cir::FloatingValue& value) {
    if (!expr.value.valid()) {
        return false;
    }
    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_core_constant_expression();
    request.required = false;
    ConstEvalResult result =
        engine.evaluate_fragment(expr.fragment, cir::ValueRef(expr.value),
                                 request);
    if (result.status == ConstEvalStatus::Constant &&
        result.value.has_value() &&
        result.value->kind == ConstValueKind::Floating) {
        value = result.value->float_value.value;
        return true;
    }
    return false;
}

bool Session::diagnose_braced_narrowing(cir::TypeId target_type,
                                        const ExprResult& value,
                                        SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() || expr_is_dependent(value) ||
        value.has_error || !value.type.valid()) {
        return false;
    }
    cir::TypeId target = file_.resolved_type(target_type);
    cir::TypeId source = file_.resolved_type(value.type);
    if (!file_.valid(target) || !file_.valid(source) ||
        type_equal(source, target)) {
        return false;
    }

    auto report_narrowing = [&]() {
        report_error("type '" + file_.format_type(value.type) +
                         "' cannot be narrowed to '" +
                         file_.format_type(target_type) +
                         "' in initializer list",
                     loc);
        return true;
    };

    bool source_floating = is_floating_type(source);
    bool target_floating = is_floating_type(target);
    bool source_integer = is_integer_type(source);
    bool target_bool = is_bool_type(target);
    bool target_integer = !target_bool && is_integer_type(target) &&
        file_.type(target).kind != cir::TypeKind::Enum;

    if (source_floating && (target_integer || target_bool)) {
        return report_narrowing();
    }

    if (source_floating && target_floating) {
        auto floating_rank_of = [&](cir::TypeId type) {
            std::optional<size_t> size = size_of_type(type, loc);
            return size.value_or(0);
        };
        if (floating_rank_of(target) >= floating_rank_of(source)) {
            return false;
        }
        cir::FloatingValue constant;
        if (try_evaluate_floating_constant(value, constant)) {
            cir::FloatingSemantics target_semantics =
                floating::semantics_for_type(file_, target);
            floating::FloatResult converted =
                floating::convert(constant, target_semantics);
            if (converted &&
                !converted.status.has(floating::FloatStatusFlag::Overflow)) {
                return false;
            }
        }
        return report_narrowing();
    }

    if (source_integer && target_floating) {
        int64_t constant = 0;
        if (try_evaluate_integer_constant(value, constant)) {
            cir::FloatingSemantics target_semantics =
                floating::semantics_for_type(file_, target);
            floating::FloatResult converted = floating::from_integer(
                static_cast<unsigned __int128>(
                    static_cast<__int128>(constant)),
                64, true, target_semantics);
            floating::FloatIntegerResult round_trip = converted
                ? floating::to_integer(converted.value, 64, true)
                : floating::FloatIntegerResult{};
            if (round_trip &&
                static_cast<int64_t>(static_cast<uint64_t>(*round_trip)) ==
                    constant) {
                return false;
            }
        }
        return report_narrowing();
    }

    if (source_integer && (target_integer || target_bool)) {
        cir::IntegerTypeShape source_shape =
            cir::integer_shape_for_type(file_, source);
        cir::IntegerTypeShape target_shape =
            cir::integer_shape_for_type(file_, target);
        bool covers;
        if (target_bool) {
            covers = is_bool_type(source);
        } else if (source_shape.is_unsigned == target_shape.is_unsigned) {
            covers = target_shape.bit_width >= source_shape.bit_width;
        } else if (source_shape.is_unsigned) {
            covers = target_shape.bit_width > source_shape.bit_width;
        } else {
            covers = false;
        }
        if (covers) {
            return false;
        }
        int64_t constant = 0;
        if (try_evaluate_integer_constant(value, constant)) {
            bool fits;
            if (target_bool) {
                fits = constant == 0 || constant == 1;
            } else if (target_shape.is_unsigned) {
                fits = constant >= 0 &&
                    (target_shape.bit_width >= 64 ||
                     static_cast<uint64_t>(constant) <=
                         (uint64_t{1} << target_shape.bit_width) - 1);
            } else {
                fits = target_shape.bit_width >= 64 ||
                    (constant >= -static_cast<int64_t>(
                                      uint64_t{1}
                                      << (target_shape.bit_width - 1)) &&
                     constant <= static_cast<int64_t>(
                                     (uint64_t{1}
                                      << (target_shape.bit_width - 1)) -
                                     1));
            }
            if (fits) {
                return false;
            }
        }
        return report_narrowing();
    }

    if (target_bool &&
        (is_pointer_type(source) ||
         file_.type(source).kind == cir::TypeKind::MemberPointer)) {
        return report_narrowing();
    }
    return false;
}
namespace {

std::shared_ptr<InitListValue> clone_init_list_value(const InitListValue& list) {
    auto clone = std::make_shared<InitListValue>(list);
    for (InitElementInput& element : clone->elements) {
        element.value.fragment = cir::Fragment{};
        for (InitDesignator& designator : element.designators) {
            designator.index.fragment = cir::Fragment{};
            designator.range_end.fragment = cir::Fragment{};
        }
        if (element.value.init_list) {
            element.value.init_list =
                clone_init_list_value(*element.value.init_list);
        }
    }
    return clone;
}

}  // namespace

bool Session::list_initializes_aggregate_from_single_class_element(
    cir::TypeId target_type,
    const ExprResult& initializer) const {
    if (!lang_opts_.is_cxx_mode() ||
        initializer.category != ValueCategory::InitList ||
        !initializer.init_list ||
        initializer.init_list->elements.size() != 1 ||
        !initializer.init_list->elements.front().designators.empty()) {
        return false;
    }

    cir::TypeId target = file_.resolved_type(target_type);
    cir::TypeId source = file_.resolved_type(
        initializer.init_list->elements.front().value.type);
    if (!file_.valid(target) || !file_.valid(source) ||
        file_.type(target).kind != cir::TypeKind::Record ||
        file_.type(source).kind != cir::TypeKind::Record ||
        !is_aggregate_type(target)) {
        return false;
    }
    return type_equal(target, source) ||
        analyze_derived_to_base_path(source, target).kind !=
            DerivedToBasePathKind::NotFound;
}

void Session::collect_init_value_assignment(cir::TypeId target_type,
                                            ExprResult value,
                                            std::vector<InitPath> paths,
                                            std::vector<InitAssignment>& assignments,
                                            SrcLoc loc,
                                            InitListSyntax syntax) {
    if (paths.empty()) {
        return;
    }

    if (value.category == ValueCategory::InitList) {
        if (!value.init_list) {
            return;
        }

        if (is_character_array_type(file_, target_type) &&
            value.init_list->elements.size() == 1 &&
            value.init_list->elements.front().designators.empty() &&
            string_literal_bytes(
                file_, value.init_list->elements.front().value) != nullptr) {
            collect_init_value_assignment(
                target_type,
                std::move(value.init_list->elements.front().value),
                std::move(paths),
                assignments,
                value.init_list->elements.front().loc);
            return;
        }

        cir::TypeId resolved_target = file_.resolved_type(target_type);
        if (file_.valid(resolved_target) &&
            file_.type(resolved_target).kind == cir::TypeKind::Record &&
            !is_aggregate_type(resolved_target) &&
            !is_dependent_type(resolved_target)) {
            ExprResult initialized = materialize_list_initialization(
                std::move(value), target_type, UseContext::Init, loc);
            collect_init_value_assignment(
                target_type, std::move(initialized), std::move(paths),
                assignments, loc, syntax);
            return;
        }

        if (list_initializes_aggregate_from_single_class_element(
                target_type, value)) {
            InitElementInput& element = value.init_list->elements.front();
            collect_init_value_assignment(
                target_type,
                std::move(element.value),
                std::move(paths),
                assignments,
                element.loc,
                value.init_list->syntax);
            return;
        }

        if (is_aggregate_type(target_type)) {

            std::vector<std::shared_ptr<InitListValue>> replays;
            replays.reserve(paths.size() - 1);
            for (size_t index = 1; index < paths.size(); ++index) {
                replays.push_back(clone_init_list_value(*value.init_list));
            }
            collect_init_assignments(target_type,
                                     value.init_list->elements,
                                     assignments,
                                     paths.front().indices,
                                     value.init_list->syntax,
                                     loc);
            for (size_t index = 1; index < paths.size(); ++index) {
                const std::shared_ptr<InitListValue>& replay = replays[index - 1];
                collect_init_assignments(target_type,
                                         replay->elements,
                                         assignments,
                                         paths[index].indices,
                                         replay->syntax,
                                         loc);
            }
            return;
        }

        std::vector<InitElementInput>& elements = value.init_list->elements;
        if (elements.empty()) {
            return;
        }
        if (elements.size() > 1 || !elements.front().designators.empty()) {
            report_error("scalar initializer list has too many elements", loc);
            return;
        }
        collect_init_value_assignment(target_type,
                                      std::move(elements.front().value),
                                      std::move(paths),
                                      assignments,
                                      elements.front().loc,
                                      value.init_list->syntax);
        return;
    }

    if (syntax == InitListSyntax::Braced && !paths.empty() &&
        paths.front().target_type.valid()) {
        (void)diagnose_braced_narrowing(paths.front().target_type, value, loc);
    }

    InitAssignment assignment;
    assignment.paths = std::move(paths);
    assignment.value = std::move(value);
    assignment.loc = loc;
    assignments.push_back(std::move(assignment));
}

void Session::collect_init_assignments(cir::TypeId type,
                                       std::vector<InitElementInput>& elements,
                                       std::vector<InitAssignment>& assignments,
                                       std::vector<size_t> prefix,
                                       InitListSyntax syntax,
                                       SrcLoc loc) {
    type = file_.resolved_type(type);
    if (!file_.valid(type)) {
        report_error("initializer has invalid target type", loc);
        return;
    }

    if (!is_aggregate_type(type)) {
        bool initialized = false;
        for (InitElementInput& element : elements) {
            if (!element.designators.empty()) {
                report_error("designated initializer requires an aggregate target", element.loc);
                continue;
            }
            if (initialized) {
                report_error("too many elements in scalar initializer", element.loc);
                continue;
            }
            initialized = true;
            collect_init_value_assignment(type,
                                          std::move(element.value),
                                          std::vector<InitPath>{InitPath{prefix, type}},
                                          assignments,
                                          element.loc,
                                      syntax);
        }
        return;
    }

    bool allow_brace_elision = syntax == InitListSyntax::Braced;
    auto assign_brace_elided_scalar =
        [&](auto&& self,
            cir::TypeId aggregate_type,
            ExprResult value,
            std::vector<size_t> base_path,
            size_t& cursor,
            SrcLoc elem_loc) -> bool {
            aggregate_type = file_.resolved_type(aggregate_type);
            if (!file_.valid(aggregate_type)) {
                return true;
            }

            if (type_equal(aggregate_type, value.type) ||
                (is_character_array_type(file_, aggregate_type) &&
                 string_literal_bytes(file_, value) != nullptr)) {
                collect_init_value_assignment(
                    aggregate_type,
                    std::move(value),
                    std::vector<InitPath>{InitPath{std::move(base_path), aggregate_type}},
                    assignments,
                    elem_loc,
                                      syntax);
                cursor = std::numeric_limits<size_t>::max();
                return true;
            }
            const cir::Type& aggregate = file_.type(aggregate_type);
            if (aggregate.kind == cir::TypeKind::Array) {
                std::optional<size_t> known_size = array_size(file_, aggregate_type);
                if (known_size.has_value() && cursor >= *known_size) {
                    report_error("too many elements in array initializer", elem_loc);
                    return true;
                }
                cir::TypeId child_type = array_element_type(file_, aggregate_type);
                std::vector<size_t> path = std::move(base_path);
                path.push_back(cursor);
                if (is_aggregate_type(child_type)) {
                    size_t child_cursor = 0;
                    (void)self(self,
                               child_type,
                               std::move(value),
                               std::move(path),
                               child_cursor,
                               elem_loc);
                } else {
                    collect_init_value_assignment(
                        child_type,
                        std::move(value),
                        std::vector<InitPath>{InitPath{std::move(path), child_type}},
                        assignments,
                        elem_loc,
                                      syntax);
                }
                ++cursor;
                return known_size.has_value() && cursor >= *known_size;
            }

            if (aggregate.kind == cir::TypeKind::Record) {
                const cir::RecordFacts* nested_facts =
                    file_.record_facts_for_type(aggregate_type);
                if (!nested_facts || nested_facts->is_incomplete) {
                    report_error("record initializer requires a complete record type", elem_loc);
                    return true;
                }
                std::optional<size_t> field_index =
                    next_initializable_field(*nested_facts, cursor);
                if (!field_index.has_value()) {
                    report_error("too many elements in record initializer", elem_loc);
                    return true;
                }
                const cir::RecordFieldFact& field = nested_facts->fields[*field_index];
                std::vector<size_t> path = std::move(base_path);
                path.push_back(*field_index);
                if (is_aggregate_type(field.type.type)) {
                    size_t child_cursor = 0;
                    (void)self(self,
                               field.type.type,
                               std::move(value),
                               std::move(path),
                               child_cursor,
                               elem_loc);
                } else {
                    collect_init_value_assignment(
                        field.type.type,
                        std::move(value),
                        std::vector<InitPath>{InitPath{std::move(path), field.type.type}},
                        assignments,
                        elem_loc,
                                      syntax);
                }
                cursor = nested_facts->kind == cir::RecordKind::Union
                    ? nested_facts->fields.size()
                    : *field_index + 1;
                return cursor >= nested_facts->fields.size();
            }

            if (aggregate.kind == cir::TypeKind::Vector) {
                uint32_t known_size = file_.vector_element_count(aggregate_type);
                if (known_size != 0 && cursor >= known_size) {
                    report_error("too many elements in vector initializer", elem_loc);
                    return true;
                }
                cir::TypeId child_type = vector_element_type(file_, aggregate_type);
                std::vector<size_t> path = std::move(base_path);
                path.push_back(cursor);
                collect_init_value_assignment(
                    child_type,
                    std::move(value),
                    std::vector<InitPath>{InitPath{std::move(path), child_type}},
                    assignments,
                    elem_loc,
                                      syntax);
                ++cursor;
                return known_size != 0 && cursor >= known_size;
            }
            return true;
        };

    const cir::Type& resolved = file_.type(type);
    if (resolved.kind == cir::TypeKind::Array) {
        std::optional<size_t> known_size = array_size(file_, type);
        cir::TypeId element_type = array_element_type(file_, type);
        size_t cursor = 0;
        std::unordered_map<size_t, size_t> nested_cursors;
        for (InitElementInput& element : elements) {
            if (!element.designators.empty()) {
                std::vector<InitPath> paths;
                size_t outer_end = cursor;
                bool has_range = false;
                if (resolve_initializer_designators(element.designators,
                                                    type,
                                                    paths,
                                                    outer_end,
                                                    has_range)) {
                    for (InitPath& path : paths) {
                        path.indices.insert(path.indices.begin(), prefix.begin(), prefix.end());
                    }
                    collect_init_value_assignment(paths.front().target_type,
                                                  std::move(element.value),
                                                  std::move(paths),
                                                  assignments,
                                                  element.loc,
                                      syntax);
                    cursor = std::max(cursor, outer_end);
                }
                continue;
            }

            if (known_size.has_value() && cursor >= *known_size) {
                report_error("too many elements in array initializer", element.loc);
                continue;
            }
            std::vector<size_t> path = prefix;
            path.push_back(cursor);
            if (allow_brace_elision &&
                is_aggregate_type(element_type) &&
                element.value.category != ValueCategory::InitList) {
                size_t child_cursor = nested_cursors[cursor];
                bool completed =
                    assign_brace_elided_scalar(assign_brace_elided_scalar,
                                               element_type,
                                               std::move(element.value),
                                               std::move(path),
                                               child_cursor,
                                               element.loc);
                if (completed) {
                    nested_cursors.erase(cursor);
                    ++cursor;
                } else {
                    nested_cursors[cursor] = child_cursor;
                }
                continue;
            }
            collect_init_value_assignment(element_type,
                                          std::move(element.value),
                                          std::vector<InitPath>{InitPath{std::move(path), element_type}},
                                          assignments,
                                          element.loc,
                                      syntax);
            ++cursor;
        }
        return;
    }

    if (resolved.kind == cir::TypeKind::Vector) {
        uint32_t known_size = file_.vector_element_count(type);
        cir::TypeId element_type = vector_element_type(file_, type);
        size_t cursor = 0;
        for (InitElementInput& element : elements) {
            if (!element.designators.empty()) {
                report_error("designated vector initializers are not supported yet",
                             element.loc);
                continue;
            }
            if (known_size != 0 && cursor >= known_size) {
                report_error("too many elements in vector initializer", element.loc);
                continue;
            }
            std::vector<size_t> path = prefix;
            path.push_back(cursor);
            collect_init_value_assignment(element_type,
                                          std::move(element.value),
                                          std::vector<InitPath>{InitPath{std::move(path), element_type}},
                                          assignments,
                                          element.loc,
                                      syntax);
            ++cursor;
        }
        return;
    }

    const cir::RecordFacts* facts = file_.record_facts_for_type(type);
    if (!facts || facts->is_incomplete) {
        report_error("record initializer requires a complete record type", loc);
        return;
    }

    size_t cursor = 0;
    bool is_union = facts->kind == cir::RecordKind::Union;
    std::unordered_map<size_t, size_t> nested_cursors;

    std::vector<size_t> anon_continuation;

    auto record_type_at = [&](const std::vector<size_t>& path,
                              size_t steps) -> cir::TypeId {
        cir::TypeId walk = type;
        for (size_t i = 0; i < steps; ++i) {
            cir::TypeId resolved_walk = file_.resolved_type(walk);
            const cir::RecordFacts* walk_facts =
                file_.record_facts_for_type(resolved_walk);
            if (!walk_facts || path[i] >= walk_facts->fields.size()) {
                return {};
            }
            walk = walk_facts->fields[path[i]].type.type;
        }
        return file_.resolved_type(walk);
    };

    auto advance_anon = [&](std::vector<size_t> path)
        -> std::optional<std::vector<size_t>> {
        while (path.size() > 1) {
            cir::TypeId parent = record_type_at(path, path.size() - 1);
            const cir::RecordFacts* parent_facts =
                file_.valid(parent) ? file_.record_facts_for_type(parent)
                                    : nullptr;
            if (!parent_facts) {
                return std::nullopt;
            }
            if (parent_facts->kind != cir::RecordKind::Union) {
                if (std::optional<size_t> next =
                        next_initializable_field(*parent_facts, path.back() + 1)) {
                    path.back() = *next;
                    return path;
                }
            }
            path.pop_back();
        }
        return std::nullopt;
    };

    for (InitElementInput& element : elements) {
        if (!element.designators.empty()) {
            std::vector<InitPath> paths;
            size_t outer_end = cursor;
            bool has_range = false;
            if (resolve_initializer_designators(element.designators,
                                                type,
                                                paths,
                                                outer_end,
                                                has_range)) {
                anon_continuation = paths.front().indices;
                for (InitPath& path : paths) {
                    path.indices.insert(path.indices.begin(), prefix.begin(), prefix.end());
                }
                collect_init_value_assignment(paths.front().target_type,
                                              std::move(element.value),
                                              std::move(paths),
                                              assignments,
                                              element.loc,
                                      syntax);
                cursor = std::max(cursor, outer_end);
            }
            continue;
        }

        if (anon_continuation.size() > 1) {
            if (std::optional<std::vector<size_t>> next =
                    advance_anon(anon_continuation)) {
                cir::TypeId parent = record_type_at(*next, next->size() - 1);
                const cir::RecordFacts* parent_facts =
                    file_.valid(parent) ? file_.record_facts_for_type(parent)
                                        : nullptr;
                if (parent_facts && next->back() < parent_facts->fields.size()) {
                    cir::TypeId field_type =
                        parent_facts->fields[next->back()].type.type;
                    std::vector<size_t> full = prefix;
                    full.insert(full.end(), next->begin(), next->end());
                    collect_init_value_assignment(
                        field_type,
                        std::move(element.value),
                        std::vector<InitPath>{InitPath{std::move(full), field_type}},
                        assignments,
                        element.loc);
                    anon_continuation = std::move(*next);
                    continue;
                }
            }

            anon_continuation.clear();
        }

        std::optional<size_t> field_index = next_initializable_field(*facts, cursor);
        if (!field_index.has_value()) {
            report_error("too many elements in record initializer", element.loc);
            continue;
        }
        anon_continuation = {*field_index};
        std::vector<size_t> path = prefix;
        path.push_back(*field_index);
        cir::TypeId field_type = facts->fields[*field_index].type.type;
        if (allow_brace_elision &&
            is_aggregate_type(field_type) &&
            element.value.category != ValueCategory::InitList) {
            size_t child_cursor = nested_cursors[*field_index];
            bool completed =
                assign_brace_elided_scalar(assign_brace_elided_scalar,
                                           field_type,
                                           std::move(element.value),
                                           std::move(path),
                                           child_cursor,
                                           element.loc);
            if (completed) {
                nested_cursors.erase(*field_index);
                cursor = is_union ? facts->fields.size() : *field_index + 1;
            } else {
                nested_cursors[*field_index] = child_cursor;
            }
            continue;
        }
        collect_init_value_assignment(field_type,
                                      std::move(element.value),
                                      std::vector<InitPath>{InitPath{std::move(path), field_type}},
                                      assignments,
                                      element.loc,
                                      syntax);
        cursor = is_union ? facts->fields.size() : *field_index + 1;
    }
}

cir::Fragment Session::emit_zero_initializer(cir::InstId place, cir::TypeId type, SrcLoc loc) {
    cir::Fragment fragment;
    type = file_.resolved_type(type);
    if (!file_.valid(type)) {
        return fragment;
    }

    const cir::Type& resolved = file_.type(type);
    if (is_reference_type(type)) {
        return fragment;
    }

    if ((resolved.kind == cir::TypeKind::Array ||
         resolved.kind == cir::TypeKind::Record ||
         resolved.kind == cir::TypeKind::Vector) &&
        can_zero_initialize_with_memset(file_, type)) {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("init.zero.object");
        builder_.zero_object(place, loc);
        cir::Fragment zero_fragment = finish_fragment_block(block, previous);
        return chain(std::move(fragment), std::move(zero_fragment), loc);
    }

    if (resolved.kind == cir::TypeKind::Array) {
        std::optional<size_t> size = array_size(file_, type);
        cir::TypeId element_type = array_element_type(file_, type);
        if (!size.has_value()) {
            report_error("cannot zero-initialize incomplete array type", loc);
            return fragment;
        }
        for (size_t index = 0; index < *size; ++index) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.zero.elem");
            cir::InstId index_value = builder_.integer_literal(static_cast<int64_t>(index),
                                                               std::to_string(index),
                                                               loc);
            cir::InstId element_place = builder_.array_element_place(place, index_value, loc);
            cir::Fragment element_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(element_fragment), loc);
            fragment = chain(std::move(fragment),
                             emit_zero_initializer(element_place, element_type, loc),
                             loc);
        }
        return fragment;
    }

    if (resolved.kind == cir::TypeKind::Record) {
        const cir::RecordFacts* facts = file_.record_facts_for_type(type);
        if (!facts || facts->is_incomplete) {
            report_error("cannot zero-initialize incomplete record type", loc);
            return fragment;
        }
        for (const cir::RecordFieldFact& field : facts->fields) {

            if (field.is_flexible_array_member) {
                continue;
            }
            if (!is_named_initializable_field(field)) {
                continue;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.zero.field");
            cir::InstId field_place =
                builder_.field_addr(place, field.entity, field.type.type, loc);
            cir::Fragment field_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(field_fragment), loc);
            fragment = chain(std::move(fragment),
                             emit_zero_initializer(field_place, field.type.type, loc),
                             loc);
            if (facts->kind == cir::RecordKind::Union) {
                break;
            }
        }
        return fragment;
    }

    if (resolved.kind == cir::TypeKind::Vector) {
        uint32_t size = file_.vector_element_count(type);
        cir::TypeId element_type = vector_element_type(file_, type);
        for (uint32_t index = 0; index < size; ++index) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.zero.vector_elem");
            cir::InstId index_value = builder_.integer_literal(static_cast<int64_t>(index),
                                                               std::to_string(index),
                                                               loc);
            cir::InstId element_place = builder_.vector_element_place(place, index_value, loc);
            cir::Fragment element_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(element_fragment), loc);
            fragment = chain(std::move(fragment),
                             emit_zero_initializer(element_place, element_type, loc),
                             loc);
        }
        return fragment;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("init.zero.scalar");
    cir::InstId zero{};
    if (is_floating_type(type)) {
        zero = builder_.floating_literal(
            floating::zero(floating::semantics_for_type(file_, type)),
            type,
            "0",
            loc);
    } else if (is_pointer_type(type)) {
        cir::InstId integer_zero = builder_.integer_literal(0, "0", loc);
        zero = builder_.cast(type, integer_zero, "zero", loc);
    } else if (resolved.kind == cir::TypeKind::MemberPointer) {
        cir::InstId null = builder_.nullptr_literal("nullptr", loc);
        zero = builder_.cast(type, null, "zero", loc);
    } else {
        zero = builder_.integer_literal(0, type, "0", loc);
    }
    builder_.store(place, zero, loc);
    cir::Fragment zero_fragment = finish_fragment_block(block, previous);
    return chain(std::move(fragment), std::move(zero_fragment), loc);
}

cir::InstId Session::place_for_init_path(cir::InstId base_place,
                                         cir::TypeId base_type,
                                         const std::vector<size_t>& path,
                                         SrcLoc loc,
                                         cir::Fragment& fragment) {
    cir::InstId place = base_place;
    cir::TypeId type = file_.resolved_type(base_type);
    for (size_t index : path) {
        if (!file_.valid(type)) {
            return place;
        }
        const cir::Type& resolved = file_.type(type);
        if (resolved.kind == cir::TypeKind::Array) {
            cir::TypeId element_type = array_element_type(file_, type);
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.path.elem");
            cir::InstId index_value = builder_.integer_literal(static_cast<int64_t>(index),
                                                               std::to_string(index),
                                                               loc);
            place = builder_.array_element_place(place, index_value, loc);
            cir::Fragment element_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(element_fragment), loc);
            type = file_.resolved_type(element_type);
            continue;
        }

        if (resolved.kind == cir::TypeKind::Record) {
            const cir::RecordFacts* facts = file_.record_facts_for_type(type);
            if (!facts || index >= facts->fields.size()) {
                report_error("initializer path references an invalid record field", loc);
                return place;
            }
            const cir::RecordFieldFact& field = facts->fields[index];
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.path.field");
            place = builder_.field_addr(place, field.entity, field.type.type, loc);
            cir::Fragment field_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(field_fragment), loc);
            type = file_.resolved_type(field.type.type);
            continue;
        }

        if (resolved.kind == cir::TypeKind::Vector) {
            cir::TypeId element_type = vector_element_type(file_, type);
            if (file_.vector_element_count(type) != 0 &&
                index >= file_.vector_element_count(type)) {
                report_error("initializer path references an invalid vector element", loc);
                return place;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.path.vector_elem");
            cir::InstId index_value = builder_.integer_literal(static_cast<int64_t>(index),
                                                               std::to_string(index),
                                                               loc);
            place = builder_.vector_element_place(place, index_value, loc);
            cir::Fragment element_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(element_fragment), loc);
            type = file_.resolved_type(element_type);
            continue;
        }

        report_error("initializer path reaches a non-aggregate type", loc);
        return place;
    }
    return place;
}

bool Session::aggregate_has_default_member_initializer(
    cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type)) {
        return false;
    }
    const cir::Type& resolved = file_.type(type);
    if (resolved.kind == cir::TypeKind::Array) {
        return aggregate_has_default_member_initializer(
            array_element_type(file_, type));
    }
    if (resolved.kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(type);
    if (!facts) {
        return false;
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.has_default_member_initializer ||
            (!field.is_base_subobject &&
             aggregate_has_default_member_initializer(field.type.type))) {
            return true;
        }
    }
    return false;
}

cir::Fragment Session::emit_initializer_for_place(cir::InstId place,
                                                  cir::TypeId type,
                                                  ExprResult initializer,
                                                  SrcLoc loc,
                                                  UseContext context,
                                                  const std::function<
                                                      cir::InstId(SrcLoc)>*
                                                      action_place) {
    if (std::optional<ExprResult> enum_value =
            try_materialize_fixed_enum_direct_list(
                initializer, type, context, loc)) {
        return emit_initializer_for_place(place,
                                          type,
                                          std::move(*enum_value),
                                          loc,
                                          context,
                                          action_place);
    }

    if (list_initializes_aggregate_from_single_class_element(
            type, initializer)) {
        InitElementInput& element =
            initializer.init_list->elements.front();
        return emit_initializer_for_place(
            place,
            type,
            std::move(element.value),
            element.loc,
            context,
            action_place);
    }

    cir::TypeId resolved_target = file_.resolved_type(type);
    cir::TypeId resolved_source = file_.resolved_type(initializer.type);
    if (lang_opts_.is_cxx_mode() && file_.valid(resolved_target) &&
        file_.type(resolved_target).kind == cir::TypeKind::Array &&
        file_.valid(resolved_source) &&
        file_.type(resolved_source).kind == cir::TypeKind::Array &&
        initializer.place.valid() &&
        (initializer.category == ValueCategory::LValue ||
         initializer.category == ValueCategory::XValue)) {
        const cir::ArrayTypePayload* target_array =
            array_payload(file_, resolved_target);
        const cir::ArrayTypePayload* source_array =
            array_payload(file_, resolved_source);
        if (target_array && source_array &&
            target_array->size_kind == cir::ArraySizeKind::Constant &&
            source_array->size_kind == cir::ArraySizeKind::Constant &&
            target_array->size == source_array->size) {
            cir::Fragment fragment = std::move(initializer.fragment);
            initializer.fragment = {};

            ClassArrayShape shape = class_array_shape(resolved_target);
            if (shape.valid()) {
                bool is_move = initializer.category == ValueCategory::XValue;
                cir::EntityId transfer = is_move
                    ? record_move_constructor(shape.leaf_type)
                    : record_copy_constructor(shape.leaf_type);
                if (is_move && !transfer.valid()) {
                    bool deleted_move = false;
                    if (const cir::RecordFacts* facts =
                            file_.record_facts_for_type(shape.leaf_type)) {
                        for (const cir::RecordMethodFact& method :
                             facts->methods) {
                            deleted_move = deleted_move ||
                                (method.special_member_kind ==
                                     cir::SpecialMemberKind::MoveConstructor &&
                                 method.is_eligible && method.is_deleted);
                        }
                    }
                    if (deleted_move) {
                        report_error(
                            "use of deleted move constructor while initializing structured-binding array",
                            loc);
                        return fragment;
                    }
                    transfer = record_copy_constructor(shape.leaf_type);
                    is_move = false;
                }
                const cir::RecordMethodFact* transfer_fact =
                    transfer.valid() ? file_.method_fact(transfer) : nullptr;
                if (!transfer_fact) {
                    report_error(
                        "no viable constructor for structured-binding array element type '" +
                            file_.format_type(shape.leaf_type) + "'",
                        loc);
                    return fragment;
                }
                check_member_access(transfer,
                                    transfer_fact->declared_access,
                                    loc);
                if (!transfer_fact->is_trivial) {
                    bool transfer_error = false;
                    fragment = chain(
                        std::move(fragment),
                        array_transfer_loop_fragment(
                            place,
                            initializer.place,
                            resolved_target,
                            transfer,
                            /*assign=*/false,
                            is_move,
                            loc,
                            &transfer_error),
                        loc);
                    return fragment;
                }
            }

            for (uint64_t index = 0; index < target_array->size;
                 ++index) {
                cir::BlockId previous = builder_.current_block();
                cir::BlockId block =
                    begin_fragment_block("init.array.copy.elem");
                cir::InstId index_value = builder_.integer_literal(
                    static_cast<int64_t>(index), std::to_string(index), loc);
                cir::InstId target_place =
                    builder_.array_element_place(place, index_value, loc);
                cir::InstId source_place = builder_.array_element_place(
                    initializer.place, index_value, loc);
                cir::Fragment places = finish_fragment_block(block, previous);
                fragment = chain(std::move(fragment), std::move(places), loc);

                ExprResult element;
                element.type = source_array->element_type.type;
                element.category = initializer.category;
                element.place = source_place;
                fragment = chain(
                    std::move(fragment),
                    emit_initializer_for_place(
                        target_place,
                        target_array->element_type.type,
                        std::move(element),
                        loc,
                        context),
                    loc);
            }
            return fragment;
        }
    }

    bool adopted_prvalue = false;
    if (lang_opts_.is_cxx_mode() &&
        initializer.category == ValueCategory::PrValue &&
        initializer.type.valid() && type_equal(initializer.type, type)) {
        cir::TypeId resolved = file_.resolved_type(type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Record) {
            adopted_prvalue =
                adopt_materialized_object_storage(initializer, place);
            if (adopted_prvalue) {
                for (cir::LifetimeId lifetime :
                     initializer.materialized_lifetimes) {
                    retire_lifetime(lifetime);
                }
            }
        }
    }
    if (std::optional<std::vector<uint8_t>> string_bytes =
            string_literal_initializer_bytes(type, initializer, loc)) {
        cir::Fragment fragment;
        cir::TypeId element_type = array_element_type(file_, type);
        for (size_t index = 0; index < string_bytes->size(); ++index) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.string.elem");
            cir::InstId index_value = builder_.integer_literal(static_cast<int64_t>(index),
                                                               std::to_string(index),
                                                               loc);
            cir::InstId element_place = builder_.array_element_place(place, index_value, loc);
            cir::InstId byte_value =
                builder_.integer_literal(static_cast<int64_t>((*string_bytes)[index]),
                                         element_type,
                                         std::to_string((*string_bytes)[index]),
                                         loc);
            builder_.store(element_place, byte_value, loc);
            cir::Fragment element_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(element_fragment), loc);
        }
        return fragment;
    }

    cir::TypeId class_target = file_.resolved_type(type);
    const cir::RecordFacts* class_facts =
        file_.record_facts_for_type(class_target);
    if (lang_opts_.is_cxx_mode() && !adopted_prvalue &&
        initializer.category != ValueCategory::InitList &&
        class_facts && class_facts->is_non_trivial_for_calls) {
        std::vector<ExprResult> arguments;
        arguments.push_back(std::move(initializer));
        ConstructorCallMaterialization materialized =
            materialize_constructor_call(
                class_target, std::move(arguments), loc,
                context == UseContext::DirectInit
                    ? ConstructorInitializationKind::Direct
                    : ConstructorInitializationKind::Copy);
        if (!materialized.constructor.valid()) {
            report_error("cannot initialize non-trivial class subobject of type '" +
                             file_.format_type(class_target) + "'",
                         loc);
            return std::move(materialized.argument_fragment);
        }
        if (materialized.has_error) {
            return std::move(materialized.argument_fragment);
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block =
            begin_fragment_block("init.class.construct");
        emit_construct_in_place(
            place, structor_complete_variant(materialized.constructor),
            materialized.argument_values, loc);
        cir::Fragment construct_fragment =
            finish_fragment_block(block, previous);
        return chain(std::move(materialized.argument_fragment),
                     std::move(construct_fragment), loc);
    }

    if (initializer.category != ValueCategory::InitList || !initializer.init_list) {
        if (is_aggregate_type(type)) {
            bool whole_value_ok =
                initializer.type.valid() && type_equal(initializer.type, type);
            if (!whole_value_ok && lang_opts_.is_cxx_mode() &&
                initializer.type.valid()) {
                cir::TypeId source = file_.resolved_type(initializer.type);
                cir::TypeId target = file_.resolved_type(type);
                if (file_.valid(source) && file_.valid(target) &&
                    file_.type(source).kind == cir::TypeKind::Record &&
                    file_.type(target).kind == cir::TypeKind::Record) {
                    whole_value_ok =
                        analyze_derived_to_base_path(source, target).kind !=
                        DerivedToBasePathKind::NotFound;
                }
            }

            if (!whole_value_ok && is_vector_type(type) &&
                is_vector_type(initializer.type) &&
                file_.vector_element_count(type) ==
                    file_.vector_element_count(initializer.type)) {
                whole_value_ok = true;
            }

            if (!whole_value_ok && lang_opts_.is_cxx_mode() &&
                initializer.type.valid()) {
                cir::TypeId source_resolved =
                    file_.resolved_type(initializer.type);
                if (file_.valid(source_resolved) &&
                    file_.type(source_resolved).kind == cir::TypeKind::Record) {
                    if (initializer.category == ValueCategory::PrValue &&
                        initializer.value.valid()) {
                        MemberAccessBase materialized =
                            collect_member_access_base(std::move(initializer),
                                                       /*is_arrow=*/false,
                                                       loc);
                        initializer = std::move(materialized.base_place);
                    }
                    UserConversionSequence sequence =
                        resolve_initialization_user_conversion(
                            initializer, type,
                            UserConversionContext::CopyInitialization,
                            loc);
                    if (sequence.kind ==
                        UserConversionSequence::Kind::Ambiguous) {
                        report_error("conversion from '" +
                                         file_.format_type(initializer.type) +
                                         "' to '" + file_.format_type(type) +
                                         "' is ambiguous",
                                     loc);
                        report_overload_ambiguity_notes(sequence.ambiguity,
                                                        loc);
                        return {};
                    }
                    if (sequence.kind ==
                        UserConversionSequence::Kind::ConversionFunction) {
                        initializer = apply_user_conversion_sequence(
                            std::move(initializer), type, sequence, loc);
                        whole_value_ok = initializer.type.valid() &&
                            type_equal(initializer.type, type);
                    }
                }
            }
            if (!whole_value_ok) {
                report_error("aggregate initializer requires an initializer list", loc);
                return {};
            }
            ExprResult value = convert_to(std::move(initializer), type,
                                          context, loc);
            if (value.has_error || !value.value.valid() ||
                expr_is_dependent(value)) {
                return std::move(value.fragment);
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.aggregate.copy");
            cir::InstId store = builder_.store(place, value.value, loc);
            if (adopted_prvalue) {
                file_.inst_mut(store).runtime_elided_object_operation = true;
            }
            cir::Fragment store_fragment = finish_fragment_block(block, previous);
            return chain(std::move(value.fragment), std::move(store_fragment), loc);
        }
        ExprResult value = convert_to(std::move(initializer), type,
                                      context, loc);
        if (value.has_error || !value.value.valid() ||
            expr_is_dependent(value)) {
            return std::move(value.fragment);
        }
        bool converted_adopted = false;
        cir::TypeId converted_target = file_.resolved_type(type);
        if (lang_opts_.is_cxx_mode() && file_.valid(converted_target) &&
            file_.type(converted_target).kind == cir::TypeKind::Record &&
            value.category == ValueCategory::PrValue &&
            value.type.valid() && type_equal(value.type, type)) {
            converted_adopted =
                adopt_materialized_object_storage(value, place);
            if (converted_adopted) {
                for (cir::LifetimeId lifetime : value.materialized_lifetimes) {
                    retire_lifetime(lifetime);
                }
            }
        }
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("init.scalar");
        cir::InstId store = builder_.store(place, value.value, loc);
        if (adopted_prvalue || converted_adopted) {
            file_.inst_mut(store).runtime_elided_object_operation = true;
        }
        cir::Fragment store_fragment = finish_fragment_block(block, previous);
        return chain(std::move(value.fragment), std::move(store_fragment), loc);
    }

    cir::Fragment fragment;
    std::vector<InitAssignment> assignments;
    collect_init_assignments(type,
                             initializer.init_list->elements,
                             assignments,
                             {},
                             initializer.init_list->syntax,
                             initializer.init_list->loc);

    ClassArrayShape lifecycle_shape;
    if (lang_opts_.is_cxx_mode()) {
        lifecycle_shape = class_array_shape(type);
    }
    bool class_array_selects_default_constructor =
        lifecycle_shape.valid() &&
        record_requires_default_constructor_selection(
            lifecycle_shape.leaf_type);
    if ((is_aggregate_type(type) ||
         initializer.init_list->elements.empty()) &&
        !class_array_selects_default_constructor) {
        fragment = chain(std::move(fragment),
                         emit_zero_initializer(place, type, loc), loc);
    }

    auto emit_assignment = [&](InitAssignment& assignment) {
        if (assignment.paths.empty()) {
            return;
        }
        cir::TypeId target_type = assignment.paths.front().target_type;
        cir::TypeId resolved_target = file_.resolved_type(target_type);
        if (assignment.paths.size() == 1 && file_.valid(resolved_target) &&
            file_.type(resolved_target).kind == cir::TypeKind::Record) {
            cir::Fragment path_fragment;
            cir::InstId target_place = place_for_init_path(
                place, type, assignment.paths.front().indices,
                assignment.loc, path_fragment);
            fragment = chain(std::move(fragment), std::move(path_fragment),
                             assignment.loc);
            fragment = chain(
                std::move(fragment),
                emit_initializer_for_place(target_place, target_type,
                                           std::move(assignment.value),
                                           assignment.loc),
                assignment.loc);
            return;
        }
        bool use_nested_initializer =
            is_character_array_type(file_, target_type) &&
            (string_literal_bytes(file_, assignment.value) != nullptr ||
             (assignment.value.category == ValueCategory::InitList &&
              assignment.value.init_list &&
              assignment.value.init_list->elements.size() == 1 &&
              assignment.value.init_list->elements.front().designators.empty() &&
              string_literal_bytes(
                  file_,
                  assignment.value.init_list->elements.front().value) != nullptr));
        ExprResult value;
        if (!use_nested_initializer) {
            value = convert_to(std::move(assignment.value),
                               target_type,
                               UseContext::Init,
                               assignment.loc);
            fragment = chain(std::move(fragment),
                             std::move(value.fragment),
                             assignment.loc);
        } else if (assignment.paths.size() > 1) {
            report_error("range designator with string literal array initializer is not supported yet",
                         assignment.loc);
            return;
        }
        if (!use_nested_initializer &&
            (value.has_error || !value.value.valid() ||
             expr_is_dependent(value))) {
            return;
        }
        for (const InitPath& path : assignment.paths) {
            cir::Fragment path_fragment;
            cir::InstId target_place =
                place_for_init_path(place, type, path.indices, assignment.loc, path_fragment);
            fragment = chain(std::move(fragment), std::move(path_fragment), assignment.loc);

            if (use_nested_initializer) {
                fragment = chain(
                    std::move(fragment),
                    emit_initializer_for_place(target_place,
                                               target_type,
                                               std::move(assignment.value),
                                               assignment.loc),
                    assignment.loc);
                continue;
            }

            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("init.store");
            builder_.store(target_place, value.value, assignment.loc);
            cir::Fragment store_fragment = finish_fragment_block(block, previous);
            fragment = chain(std::move(fragment), std::move(store_fragment), assignment.loc);

            if (lang_opts_.is_cxx_mode()) {
                cir::TypeId stored = file_.resolved_type(target_type);
                if (file_.valid(stored) &&
                    file_.type(stored).kind == cir::TypeKind::Record) {
                    if (!value.materialized_lifetimes.empty()) {
                        for (cir::LifetimeId lifetime :
                             value.materialized_lifetimes) {
                            retire_lifetime(lifetime);
                        }
                    } else {
                        remove_destructor_cleanup(
                            temporary_entity_of_value(value.value));
                    }
                }
            }
        }
    };

    bool emitted_class_array_order = false;
    if (lang_opts_.is_cxx_mode()) {
        if (lifecycle_shape.extent_overflow) {
            report_error("class-array extent product exceeds the supported "
                         "object size",
                         loc);
        } else if (lifecycle_shape.valid()) {
            struct LeafInitializerGroup {
                uint64_t leaf = 0;
                std::vector<size_t> assignments;
            };
            std::vector<LeafInitializerGroup> groups;
            bool mapping_valid = true;
            for (size_t assignment_index = 0;
                 assignment_index < assignments.size(); ++assignment_index) {
                const InitAssignment& assignment = assignments[assignment_index];
                if (assignment.paths.size() != 1 ||
                    assignment.paths.front().indices.size() <
                        lifecycle_shape.extents.size()) {
                    mapping_valid = false;
                    break;
                }
                uint64_t leaf_index = 0;
                for (size_t dimension = 0;
                     dimension < lifecycle_shape.extents.size(); ++dimension) {
                    uint64_t index = static_cast<uint64_t>(
                        assignment.paths.front().indices[dimension]);
                    uint64_t extent = lifecycle_shape.extents[dimension];
                    if (index >= extent) {
                        mapping_valid = false;
                        break;
                    }
                    leaf_index = leaf_index * extent + index;
                }
                if (!mapping_valid) {
                    break;
                }
                if (groups.empty() || groups.back().leaf != leaf_index) {
                    if (!groups.empty() && groups.back().leaf > leaf_index) {
                        mapping_valid = false;
                        break;
                    }
                    groups.push_back(LeafInitializerGroup{leaf_index, {}});
                }
                groups.back().assignments.push_back(assignment_index);
            }

            if (mapping_valid) {
                emitted_class_array_order = true;
                cir::BlockId saved_target = builder_.current_unwind_target();
                cir::InstId progress_place = begin_array_construct_unwind(
                    place, lifecycle_shape.array_type,
                    lifecycle_shape.leaf_type, saved_target, loc,
                    action_place);

                auto advance_progress = [&](uint64_t completed) {
                    if (!progress_place.valid()) {
                        return;
                    }
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block =
                        begin_fragment_block("array.init.progress");
                    cir::InstId count = builder_.integer_literal(
                        static_cast<int64_t>(completed),
                        builder_.usize_type(), {}, loc);
                    builder_.store(
                        rematerialize_entity_place(progress_place, loc),
                        count, loc);
                    fragment = chain(
                        std::move(fragment),
                        finish_fragment_block(block, previous), loc);
                };

                auto initialize_implicit_range =
                    [&](uint64_t first, uint64_t past_last) {
                        if (first >= past_last) {
                            return;
                        }
                        if (record_requires_default_constructor_selection(
                                lifecycle_shape.leaf_type)) {
                            bool construct_error = false;
                            fragment = chain(
                                std::move(fragment),
                                array_construct_loop_fragment(
                                    place, lifecycle_shape.array_type,
                                    first, past_last, loc, &construct_error,
                                    action_place, progress_place),
                                loc);
                        } else {

                            advance_progress(past_last);
                        }
                    };

                advance_progress(0);
                uint64_t next_leaf = 0;
                for (const LeafInitializerGroup& group : groups) {
                    initialize_implicit_range(next_leaf, group.leaf);
                    for (size_t assignment_index : group.assignments) {
                        emit_assignment(assignments[assignment_index]);
                    }
                    next_leaf = group.leaf + 1;
                    advance_progress(next_leaf);
                }
                initialize_implicit_range(
                    next_leaf, lifecycle_shape.total_leaf_count);

                if (progress_place.valid()) {
                    builder_.set_current_unwind_target(saved_target);
                }
            }
        }
    }

    bool emitted_record_order = false;
    if (!emitted_class_array_order && lang_opts_.is_cxx_mode()) {
        cir::TypeId resolved = file_.resolved_type(type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Record) {
            if (const cir::RecordFacts* facts =
                    file_.record_facts_for_type(resolved)) {
                emitted_record_order = true;
                cir::RecordKind record_kind = facts->kind;
                std::vector<cir::RecordFieldFact> stable_fields =
                    facts->fields;
                std::vector<bool> emitted(assignments.size(), false);
                bool union_has_explicit = false;
                if (record_kind == cir::RecordKind::Union) {
                    for (const InitAssignment& assignment : assignments) {
                        for (const InitPath& path : assignment.paths) {
                            union_has_explicit = union_has_explicit ||
                                !path.indices.empty();
                        }
                    }
                }
                bool union_dmi_used = false;
                for (size_t field_index = 0;
                     field_index < stable_fields.size(); ++field_index) {
                    bool field_written = false;
                    for (size_t assignment_index = 0;
                         assignment_index < assignments.size();
                         ++assignment_index) {
                        if (emitted[assignment_index]) {
                            continue;
                        }
                        const InitAssignment& assignment =
                            assignments[assignment_index];
                        bool starts_here = std::any_of(
                            assignment.paths.begin(),
                            assignment.paths.end(),
                            [&](const InitPath& path) {
                                return !path.indices.empty() &&
                                    path.indices.front() == field_index;
                            });
                        if (!starts_here) {
                            continue;
                        }
                        field_written = true;
                        emitted[assignment_index] = true;
                        emit_assignment(assignments[assignment_index]);
                    }

                    const cir::RecordFieldFact& field =
                        stable_fields[field_index];
                    bool may_use_union_dmi =
                        record_kind != cir::RecordKind::Union ||
                        (!union_has_explicit && !union_dmi_used);
                    if (field_written || !may_use_union_dmi ||
                        (!field.has_default_member_initializer &&
                         !aggregate_has_default_member_initializer(
                             field.type.type))) {
                        continue;
                    }
                    SrcLoc dmi_loc = field.default_member_initializer_loc;
                    if (dmi_loc.isInvalid()) {
                        dmi_loc = loc;
                    }
                    ExprResult dmi;
                    if (field.has_default_member_initializer &&
                        default_member_initializer_replay_callback_) {
                        dmi = default_member_initializer_replay_callback_(
                            field.entity, place, dmi_loc);
                    } else {
                        dmi = collect_init_list_expr({}, dmi_loc);
                    }
                    cir::BlockId previous = builder_.current_block();
                    cir::BlockId block =
                        begin_fragment_block("init.aggregate.dmi.place");
                    cir::InstId field_place = builder_.field_addr(
                        place, field.entity, field.type.type, dmi_loc);
                    cir::Fragment place_fragment =
                        finish_fragment_block(block, previous);
                    fragment = chain(std::move(fragment),
                                     std::move(place_fragment), dmi_loc);
                    fragment = chain(
                        std::move(fragment),
                        emit_initializer_for_place(field_place,
                                                   field.type.type,
                                                   std::move(dmi),
                                                   dmi_loc),
                        dmi_loc);
                    union_dmi_used =
                        union_dmi_used ||
                        record_kind == cir::RecordKind::Union;
                }
                for (size_t assignment_index = 0;
                     assignment_index < assignments.size();
                     ++assignment_index) {
                    if (!emitted[assignment_index]) {
                        emit_assignment(assignments[assignment_index]);
                    }
                }
            }
        }
    }
    if (!emitted_record_order && !emitted_class_array_order) {
        for (InitAssignment& assignment : assignments) {
            emit_assignment(assignment);
        }
    }
    return fragment;
}

ExprResult Session::collect_compound_literal_expr(cir::TypeId type,
                                                  ExprResult initializer,
                                                  SrcLoc loc) {
    type = complete_initializer_type(type, initializer, loc);
    if (!type.valid()) {
        type = builder_.unknown_type();
    }

    std::string name = ".compoundlit." + std::to_string(compound_literal_counter_++);
    cir::StorageDuration storage_duration =
        is_file_scope() ? cir::StorageDuration::Static
                        : cir::StorageDuration::Automatic;
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                               name,
                                               type,
                                               {},
                                               loc,
                                               storage_duration,
                                               cir::MemorySpace::Default,
                                               {});
    cir::Entity& entity_ref = file_.entity_mut(entity);
    entity_ref.is_definition = true;
    entity_ref.lexical_context = current_decl_context();
    entity_ref.semantic_context = current_decl_context();
    entity_ref.linkage = is_file_scope() ? cir::LinkageKind::Internal
                                         : cir::LinkageKind::None;

    ExprResult result;
    result.type = type;
    result.entity = entity;
    result.category = ValueCategory::LValue;
    result.has_error = initializer.has_error;

    if (storage_duration == cir::StorageDuration::Static) {
        std::vector<cir::StaticInitializerRelocation> relocations;
        std::optional<std::vector<uint8_t>> bytes =
            static_initializer_bytes(type, std::move(initializer), loc, &relocations);
        if (!bytes.has_value()) {
            result.has_error = true;
        } else {
            cir::Entity& variable = file_.entity_mut(entity);
            variable.has_static_initializer = true;
            variable.static_initializer_bytes = std::move(*bytes);
            variable.static_initializer_relocations = std::move(relocations);
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.compound_literal.global");
        result.place = builder_.global_place(entity, loc);
        result.fragment = finish_fragment_block(block, previous);
        return result;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId place_block = begin_fragment_block("expr.compound_literal.place");
    result.place = builder_.local_place(entity, type, loc);
    cir::Fragment fragment = finish_fragment_block(place_block, previous);

    if (initializer.init_list) {
        result.init_list = clone_init_list_value(*initializer.init_list);
    }
    cir::Fragment init_fragment =
        emit_initializer_for_place(result.place, type, std::move(initializer), loc);
    result.fragment = chain(std::move(fragment), std::move(init_fragment), loc);
    return result;
}

ExprResult Session::collect_initialized_prvalue(cir::TypeId type,
                                                ExprResult initializer,
                                                SrcLoc loc) {
    if (in_template_definition() &&
        ((type.valid() &&
          (is_dependent_type(type) ||
           type_contains_dependent_alias_specialization(type))) ||
         expr_is_dependent(initializer))) {
        return make_dependent_expr(std::move(initializer), loc);
    }

    ExprResult result;
    result.type = type;
    result.category = ValueCategory::PrValue;
    result.has_error = initializer.has_error;

    cir::TypeId resolved = file_.resolved_type(type);
    const bool is_record = file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::Record;
    const bool is_class_array =
        file_.valid(resolved) && class_array_shape(resolved).valid();
    const bool is_aggregate =
        file_.valid(resolved) && is_aggregate_type(resolved);
    const bool is_enum =
        file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::Enum;
    if (!file_.valid(resolved) ||
        (!is_scalar_type(resolved) &&
         !is_enum &&
         !is_aggregate)) {
        report_error("type conversion requires a supported object type", loc);
        result.has_error = true;
        return result;
    }
    if (is_record && diagnose_abstract_instantiation(resolved, loc)) {
        result.has_error = true;
        return result;
    }

    std::string temp_name =
        ".expr.aggregate.tmp." + std::to_string(compound_literal_counter_++);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId place_block = begin_fragment_block("expr.aggregate.temp.place");
    cir::InstId place = builder_.local_place(temp, type, loc);
    cir::Fragment place_fragment = finish_fragment_block(place_block, previous);

    cir::Fragment init_fragment =
        emit_initializer_for_place(place, type, std::move(initializer), loc);
    cir::LifetimeId lifetime{};
    if (is_record || is_class_array) {
        lifetime = register_destructor_cleanup(
            temp, type, loc, /*full_expression_temporary=*/true);
    }

    cir::BlockId load_previous = builder_.current_block();
    cir::BlockId load_block = begin_fragment_block("expr.aggregate.temp.load");
    cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
    cir::Fragment load_fragment =
        finish_fragment_block(load_block, load_previous);

    result.fragment = chain(std::move(place_fragment),
                            std::move(init_fragment),
                            loc);
    result.fragment =
        chain(std::move(result.fragment), std::move(load_fragment), loc);
    result.value = value;
    if (lifetime.valid()) {
        result.materialized_lifetimes.push_back(lifetime);
    }
    return result;
}

std::optional<ExprResult>
Session::try_materialize_fixed_enum_direct_list(ExprResult& expr,
                                                cir::TypeId type,
                                                UseContext context,
                                                SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() ||
        expr.category != ValueCategory::InitList || !expr.init_list ||
        expr.init_list->syntax != InitListSyntax::Braced) {
        return std::nullopt;
    }

    cir::TypeId target = file_.resolved_type(type);
    if (!file_.valid(target) ||
        file_.type(target).kind != cir::TypeKind::Enum) {
        return std::nullopt;
    }
    const auto* enumeration =
        std::get_if<cir::EnumTypePayload>(&file_.type_payload(target));
    if (!enumeration || expr.init_list->elements.size() != 1 ||
        !expr.init_list->elements.front().designators.empty()) {
        return std::nullopt;
    }

    ExprResult& element = expr.init_list->elements.front().value;
    cir::TypeId source = file_.resolved_type(element.type);
    if (!file_.valid(source) || expr_is_dependent(element) ||
        type_equal(source, target)) {
        return std::nullopt;
    }

    bool source_is_scalar = is_scalar_type(source) ||
        file_.type(source).kind == cir::TypeKind::Enum ||
        is_nullptr_type(source);
    bool direct_fixed_enum = context == UseContext::DirectInit &&
        enumeration->has_fixed_underlying_type && source_is_scalar &&
        enumeration->underlying_type.valid() &&
        conversion_rank(element,
                        enumeration->underlying_type,
                        /*from_qualifiers=*/0,
                        /*detail=*/nullptr,
                        /*allow_user_defined=*/false) != ConversionRank::Bad;

    ExprResult value = std::move(element);
    if (!direct_fixed_enum) {
        report_error("cannot convert expression of type '" +
                         file_.format_type(value.type) + "' to '" +
                         file_.format_type(type) + "'",
                     loc);
        value = require_value(std::move(value), UseContext::RValue, loc);
        value.has_error = true;
        return cast_if_needed(std::move(value), type,
                              "invalid enum list initialization", loc);
    }

    bool narrowing = diagnose_braced_narrowing(
        enumeration->underlying_type.type, value, loc);
    value = convert_to(std::move(value),
                       enumeration->underlying_type.type,
                       UseContext::Init,
                       loc);
    value.has_error = value.has_error || narrowing || expr.has_error;
    return cast_if_needed(std::move(value), type,
                          "direct-list enum initialization", loc);
}

ExprResult Session::materialize_list_initialization(ExprResult expr,
                                                    cir::TypeId type,
                                                    UseContext context,
                                                    SrcLoc loc,
                                                    cir::StorageDuration
                                                        backing_duration) {
    if (!expr.init_list || expr.category != ValueCategory::InitList) {
        return convert_to(std::move(expr), type, context, loc);
    }
    if (std::optional<ExprResult> enum_value =
            try_materialize_fixed_enum_direct_list(expr, type, context, loc)) {
        return std::move(*enum_value);
    }
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        expr.has_error = true;
        expr.type = type;
        return expr;
    }

    if (std::optional<cir::TypeRef> element_type =
            initializer_list_element_type(resolved)) {
        (void)require_complete_class_type(
            resolved, loc, cir::InstantiationDemandKind::CompleteClass);
        const cir::RecordFacts* facts = file_.record_facts_for_type(resolved);
        std::vector<cir::RecordFieldFact> object_fields;
        if (facts) {
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (!field.is_base_subobject &&
                    !field.is_virtual_base_storage) {
                    object_fields.push_back(field);
                }
            }
        }
        bool representation_ok = object_fields.size() == 2;
        cir::TypeId pointer_type;
        if (representation_ok) {
            pointer_type = file_.resolved_type(object_fields[0].type.type);
            representation_ok = file_.valid(pointer_type) &&
                file_.type(pointer_type).kind == cir::TypeKind::Pointer &&
                file_.resolved_type(file_.pointer_pointee_type(pointer_type)) ==
                    file_.resolved_type(element_type->type) &&
                (file_.pointer_pointee_ref(pointer_type).qualifiers &
                 cir::QualConst) != 0 &&
                is_integer_type(object_fields[1].type.type);
        }
        if (!representation_ok) {
            report_error(
                "std::initializer_list specialization has an unsupported "
                "object representation",
                loc);
            expr.has_error = true;
            expr.type = type;
            expr.category = ValueCategory::PrValue;
            expr.init_list.reset();
            return expr;
        }
        for (const InitElementInput& element : expr.init_list->elements) {
            if (!element.designators.empty()) {
                report_error(
                    "designated initializer is not permitted in a "
                    "std::initializer_list",
                    element.loc);
                expr.has_error = true;
            }
        }
        bool has_error = expr.has_error;

        const size_t count = expr.init_list->elements.size();
        cir::TypeRef const_element = *element_type;
        const_element.qualifiers |= cir::QualConst;
        cir::TypeId backing_type = file_.array_type(
            const_element, cir::ArraySizeKind::Constant, count);
        bool stable_backing =
            backing_duration == cir::StorageDuration::Static ||
            backing_duration == cir::StorageDuration::Thread;
        cir::EntityId backing = builder_.add_entity(
            cir::EntityKind::Variable,
            ".initializer_list.backing." +
                std::to_string(compound_literal_counter_++),
            backing_type, {}, loc,
            stable_backing ? backing_duration
                           : cir::StorageDuration::Temporary,
            cir::MemorySpace::Default, {});
        cir::Entity& backing_entity = file_.entity_mut(backing);
        backing_entity.is_definition = true;
        backing_entity.has_initializer = true;
        backing_entity.qualifiers = cir::QualConst;
        backing_entity.linkage = stable_backing
            ? cir::LinkageKind::Internal
            : cir::LinkageKind::None;
        backing_entity.lexical_context = current_decl_context();
        backing_entity.semantic_context = current_decl_context();

        cir::BlockId previous = builder_.current_block();
        cir::BlockId backing_block =
            begin_fragment_block("expr.initializer_list.backing");
        cir::InstId backing_place = stable_backing
            ? builder_.global_place(backing, loc)
            : builder_.local_place(backing, backing_type, loc);
        cir::Fragment fragment =
            finish_fragment_block(backing_block, previous);
        fragment = chain(
            std::move(fragment),
            emit_initializer_for_place(backing_place, backing_type,
                                       std::move(expr), loc),
            loc);

        cir::LifetimeId backing_lifetime = register_destructor_cleanup(
            backing, backing_type, loc, /*full_expression_temporary=*/true);
        if (stable_backing) {
            cir::EntityId cleanup = array_destroy_helper(backing_type, loc);
            if (cleanup.valid()) {
                cir::TypeId void_type = builder_.void_type();
                cir::TypeId void_pointer = builder_.pointer_type(void_type);
                cir::TypeId erased_cleanup_type = function_type(
                    file_.type_ref(void_type),
                    {file_.type_ref(void_pointer)}, false, true);
                cir::TypeId erased_cleanup_pointer =
                    builder_.pointer_type(erased_cleanup_type);
                previous = builder_.current_block();
                cir::BlockId registration_block = begin_fragment_block(
                    backing_duration == cir::StorageDuration::Thread
                        ? "initializer_list.thread.cleanup"
                        : "initializer_list.static.cleanup");
                cir::EntityId registration = runtime_function(
                    backing_duration == cir::StorageDuration::Thread
                        ? "__cxa_thread_atexit"
                        : "__cxa_atexit",
                    function_type(
                        file_.type_ref(builder_.int_type()),
                        {file_.type_ref(erased_cleanup_pointer),
                         file_.type_ref(void_pointer),
                         file_.type_ref(void_pointer)},
                        false, true),
                    loc);
                cir::EntityId dso = extern_runtime_global("__dso_handle", loc);
                cir::InstId cleanup_pointer = builder_.cast(
                    erased_cleanup_pointer,
                    builder_.function_to_pointer(cleanup, loc),
                    "value", loc);
                cir::InstId object_pointer = builder_.cast(
                    void_pointer, builder_.addr_of(backing_place, loc),
                    "value", loc);
                cir::InstId dso_pointer = builder_.cast(
                    void_pointer,
                    builder_.addr_of(builder_.global_place(dso, loc), loc),
                    "value", loc);
                builder_.call(registration, builder_.int_type(),
                              {cleanup_pointer, object_pointer, dso_pointer},
                              loc);
                fragment = chain(
                    std::move(fragment),
                    finish_fragment_block(registration_block, previous), loc);

                LifetimeOwnerKind owner =
                    backing_duration == cir::StorageDuration::Thread
                    ? LifetimeOwnerKind::ThreadExit
                    : LifetimeOwnerKind::StaticExit;
                cir::LifetimeId lifetime{
                    static_cast<uint32_t>(lifetime_obligations_.size()),
                    next_lifetime_generation_++};
                lifetime_obligations_.push_back(LifetimeObligation{
                    lifetime, backing, backing_type, cleanup, loc, owner,
                    static_cast<uint64_t>(backing.index), true});
            }
        }

        cir::EntityId object = builder_.add_entity(
            cir::EntityKind::Variable,
            ".initializer_list.object." +
                std::to_string(compound_literal_counter_++),
            type, {}, loc, cir::StorageDuration::Temporary,
            cir::MemorySpace::Default, {});
        file_.entity_mut(object).is_definition = true;
        previous = builder_.current_block();
        cir::BlockId object_block =
            begin_fragment_block("expr.initializer_list.object");
        cir::InstId object_place = builder_.local_place(object, type, loc);
        cir::InstId pointer_field = builder_.field_addr(
            object_place, object_fields[0].entity,
            object_fields[0].type.type, loc);
        cir::InstId size_field = builder_.field_addr(
            object_place, object_fields[1].entity,
            object_fields[1].type.type, loc);
        cir::InstId pointer_value;
        if (count == 0) {
            cir::InstId zero = builder_.integer_literal(
                0, builder_.usize_type(), "0", loc);
            pointer_value = builder_.cast(object_fields[0].type.type, zero,
                                          "value", loc);
        } else {
            cir::InstId zero = builder_.integer_literal(
                0, builder_.usize_type(), "0", loc);
            cir::InstId first =
                builder_.array_element_place(backing_place, zero, loc);
            pointer_value = builder_.addr_of(first, loc);
            if (file_.inst(pointer_value).result_type !=
                object_fields[0].type.type) {
                pointer_value = builder_.cast(object_fields[0].type.type,
                                              pointer_value, "value", loc);
            }
        }
        cir::InstId size_value = builder_.integer_literal(
            static_cast<int64_t>(count), object_fields[1].type.type,
            std::to_string(count), loc);
        builder_.store(pointer_field, pointer_value, loc);
        builder_.store(size_field, size_value, loc);
        cir::InstId value = builder_.lvalue_to_rvalue(object_place, loc);
        cir::Fragment object_fragment =
            finish_fragment_block(object_block, previous);

        ExprResult result;
        result.fragment = chain(std::move(fragment),
                                std::move(object_fragment), loc);
        result.value = value;
        result.type = type;
        result.category = ValueCategory::PrValue;
        result.has_error = has_error;
        if (backing_lifetime.valid()) {
            result.materialized_lifetimes.push_back(backing_lifetime);
        }
        if (cir::LifetimeId object_lifetime = register_destructor_cleanup(
                object, type, loc, /*full_expression_temporary=*/true);
            object_lifetime.valid()) {
            result.materialized_lifetimes.push_back(object_lifetime);
        }
        return result;
    }

    if (file_.type(resolved).kind == cir::TypeKind::Record &&
        !is_dependent_type(resolved)) {

        (void)require_complete_class_type(resolved, loc);
    }
    if (file_.type(resolved).kind == cir::TypeKind::Record &&
        !is_aggregate_type(resolved)) {
        std::vector<ExprResult> arguments;
        arguments.push_back(std::move(expr));
        return collect_functional_cast(
            type, std::move(arguments), loc, InitListSyntax::Braced,
            context == UseContext::Init ||
                context == UseContext::DirectInit);
    }
    return collect_initialized_prvalue(type, std::move(expr), loc);
}

cir::EntityId Session::string_literal_entity(cir::InstId literal_inst, SrcLoc loc) {
    if (!file_.valid(literal_inst) ||
        file_.inst(literal_inst).kind != cir::InstKind::StringLiteral) {
        return {};
    }
    uint64_t key = (uint64_t(literal_inst.generation) << 32) | literal_inst.index;
    if (auto found = string_literal_entities_.find(key);
        found != string_literal_entities_.end()) {
        return found->second;
    }
    const auto* literal = std::get_if<cir::LiteralPayload>(
        &file_.payload(file_.inst(literal_inst).payload_index));
    const auto* bytes =
        literal ? std::get_if<cir::LiteralByteArray>(&literal->value) : nullptr;
    if (!bytes) {
        return {};
    }
    std::vector<uint8_t> data(bytes->begin(), bytes->end());
    data.push_back(0);

    std::string name = ".str.reloc." + std::to_string(string_entity_counter_++);
    cir::TypeId type = builder_.array_type(builder_.char_type(), data.size());
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                               name,
                                               type,
                                               {},
                                               loc,
                                               cir::StorageDuration::Static,
                                               cir::MemorySpace::Default,
                                               {});
    cir::Entity& record = file_.entity_mut(entity);
    record.is_definition = true;
    record.linkage = cir::LinkageKind::Internal;
    record.object_origin = cir::EntityObjectOrigin::StringLiteral;
    record.has_static_initializer = true;
    record.static_initializer_bytes = std::move(data);
    string_literal_entities_[key] = entity;
    return entity;
}

std::optional<std::vector<uint8_t>> Session::static_initializer_bytes(cir::TypeId type,
                                                                      ExprResult initializer,
                                                                      SrcLoc loc,
                                                                      std::vector<cir::StaticInitializerRelocation>* relocations) {
    std::optional<size_t> size = size_of_type(type, loc);
    if (!size.has_value()) {
        return std::nullopt;
    }

    if (is_reference_type(type) && !initializer.value.valid()) {
        initializer = bind_to_reference(std::move(initializer), type, loc);
        if (initializer.has_error) {
            return std::nullopt;
        }
    }
    if (initializer.category == ValueCategory::OverloadDesignator) {
        initializer = convert_overload_designator_to_target(
            std::move(initializer), type, loc);
        if (initializer.has_error) {
            return std::nullopt;
        }
    } else if (initializer.category == ValueCategory::FunctionDesignator) {
        initializer = convert_function_designator_to_target(std::move(initializer),
                                                            type,
                                                            loc);
        if (initializer.has_error) {
            return std::nullopt;
        }
    }
    if (initializer.category == ValueCategory::MemberPointerDesignator &&
        member_pointer_payload(file_, type)) {
        initializer =
            convert_member_pointer_designator_to_target(std::move(initializer),
                                                        type,
                                                        loc);
        if (initializer.has_error) {
            return std::nullopt;
        }
    }
    if (std::optional<std::vector<uint8_t>> string_bytes =
            string_literal_initializer_bytes(type, initializer, loc)) {
        return string_bytes;
    }
    std::vector<uint8_t> bytes(*size, 0);

    if (initializer.category != ValueCategory::InitList &&
        initializer.init_list != nullptr &&
        is_aggregate_type(file_.resolved_type(type))) {
        initializer.category = ValueCategory::InitList;
    }

    if (initializer.category == ValueCategory::InitList) {
        if (!initializer.init_list) {
            return bytes;
        }
        if (initializer.init_list->elements.empty() &&
            !aggregate_has_default_member_initializer(type)) {
            return write_static_zero(bytes, 0, type, loc)
                ? std::optional<std::vector<uint8_t>>(std::move(bytes))
                : std::nullopt;
        }

        std::vector<InitAssignment> assignments;
        collect_init_assignments(type,
                                 initializer.init_list->elements,
                                 assignments,
                                 {},
                                 initializer.init_list->syntax,
                                 initializer.init_list->loc);

        cir::TypeId resolved = file_.resolved_type(type);
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::Record) {
            if (const cir::RecordFacts* facts =
                    file_.record_facts_for_type(resolved);
                facts && !facts->fields.empty() &&
                facts->fields.back().is_flexible_array_member) {
                const size_t fam_index = facts->fields.size() - 1;
                const cir::RecordFieldFact& fam = facts->fields.back();
                std::optional<size_t> element_size = size_of_type(
                    array_element_type(file_, file_.resolved_type(fam.type.type)),
                    loc);
                size_t max_elements = 0;
                for (const InitAssignment& assignment : assignments) {
                    for (const InitPath& path : assignment.paths) {
                        if (path.indices.size() >= 2 &&
                            path.indices[0] == fam_index) {
                            max_elements =
                                std::max(max_elements, path.indices[1] + 1);
                        }
                    }
                }
                if (max_elements > 0 && element_size.has_value()) {
                    bytes.resize(std::max(bytes.size(),
                                          fam.offset +
                                              max_elements * *element_size),
                                 0);
                }
            }
        }

        bool ok = true;
        auto convert_static_assignment =
            [&](ExprResult value,
                cir::TypeId target_type,
                SrcLoc assignment_loc) -> std::optional<ExprResult> {

                if (!is_aggregate_type(target_type)) {
                    value = convert_to(std::move(value),
                                       target_type,
                                       UseContext::Init,
                                       assignment_loc);
                }
                if (value.has_error || expr_is_dependent(value)) {
                    return std::nullopt;
                }
                return value;
            };
        std::vector<bool> written_top;
        std::optional<cir::RecordFacts> stable_record_facts;
        if (const cir::RecordFacts* facts =
                file_.record_facts_for_type(file_.resolved_type(type))) {
            stable_record_facts = *facts;
            written_top.resize(facts->fields.size(), false);
        }
        for (const InitAssignment& assignment : assignments) {
            if (assignment.paths.empty()) {
                continue;
            }
            std::optional<ExprResult> assignment_value =
                convert_static_assignment(assignment.value,
                                          assignment.paths.front().target_type,
                                          assignment.loc);
            if (!assignment_value.has_value()) {
                ok = false;
                continue;
            }
            for (const InitPath& path : assignment.paths) {
                if (!path.indices.empty() &&
                    path.indices.front() < written_top.size()) {
                    written_top[path.indices.front()] = true;
                }
                ok = write_static_path(bytes,
                                       type,
                                       path.indices,
                                       *assignment_value,
                                       assignment.loc,
                                       relocations) && ok;
            }
        }
        if (!written_top.empty()) {
            const cir::RecordFacts* facts = stable_record_facts
                ? &*stable_record_facts
                : nullptr;
            bool union_has_explicit =
                facts && facts->kind == cir::RecordKind::Union &&
                std::any_of(written_top.begin(), written_top.end(),
                            [](bool written) { return written; });
            bool union_dmi_used = false;
            for (size_t field_index = 0;
                 facts && field_index < facts->fields.size();
                 ++field_index) {
                const cir::RecordFieldFact& field = facts->fields[field_index];
                if (written_top[field_index] ||
                    (facts->kind == cir::RecordKind::Union &&
                     (union_has_explicit || union_dmi_used))) {
                    continue;
                }
                ExprResult omitted;
                SrcLoc field_loc = field.default_member_initializer_loc;
                if (field_loc.isInvalid()) {
                    field_loc = loc;
                }
                if (field.has_default_member_initializer &&
                    default_member_initializer_replay_callback_) {
                    omitted = default_member_initializer_replay_callback_(
                        field.entity, {}, field_loc);
                } else if (aggregate_has_default_member_initializer(
                               field.type.type)) {
                    omitted = collect_init_list_expr({}, field_loc);
                } else {
                    continue;
                }
                std::optional<ExprResult> omitted_value =
                    convert_static_assignment(std::move(omitted),
                                              field.type.type,
                                              field_loc);
                if (!omitted_value.has_value()) {
                    ok = false;
                    continue;
                }
                ok = write_static_path(bytes,
                                       type,
                                       {field_index},
                                       *omitted_value,
                                       field_loc,
                                       relocations) && ok;
                union_dmi_used =
                    union_dmi_used ||
                    facts->kind == cir::RecordKind::Union;
            }
        }
        if (ok && relocations) {
            mark_static_initializer_relocations_required(*relocations, loc);
        }
        return ok ? std::optional<std::vector<uint8_t>>(std::move(bytes)) : std::nullopt;
    }

    if (!initializer.value.valid() && initializer.place.valid()) {
        cir::TypeId resolved = file_.resolved_type(type);
        if (file_.valid(resolved)) {
            cir::TypeKind kind = file_.type(resolved).kind;
            if (kind == cir::TypeKind::Builtin ||
                kind == cir::TypeKind::Enum ||
                kind == cir::TypeKind::BitInt ||
                kind == cir::TypeKind::Complex) {
                initializer =
                    require_value(std::move(initializer),
                                  UseContext::RValue,
                                  loc);
            }
        }
    }

    if (!write_static_value(bytes, 0, type, initializer, loc, relocations)) {
        return std::nullopt;
    }
    if (relocations) {
        mark_static_initializer_relocations_required(*relocations, loc);
    }
    return bytes;
}

bool Session::write_static_const_value(std::vector<uint8_t>& bytes,
                                       size_t offset,
                                       cir::TypeId type,
                                       const ConstValue& value,
                                       SrcLoc loc,
                                       std::vector<cir::StaticInitializerRelocation>*
                                           relocations) {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return false;
    }
    switch (value.kind) {
        case ConstValueKind::Integer: {
            std::optional<size_t> size = size_of_type(resolved, loc);
            if (!size.has_value() || *size > 16 ||
                offset + *size > bytes.size()) {
                return false;
            }
            unsigned __int128 raw = value.int_value.to_unsigned_u128();
            abi::write_scalar_bits(bytes.data() + offset, *size,
                                   static_cast<uint64_t>(raw),
                                   static_cast<uint64_t>(raw >> 64),
                                   file_.target_info().endianness);
            return true;
        }
        case ConstValueKind::Boolean: {
            std::optional<int64_t> scalar = value.try_as_int64();
            std::optional<size_t> size = size_of_type(resolved, loc);
            if (!scalar.has_value() || !size.has_value() ||
                offset + *size > bytes.size()) {
                return false;
            }
            write_integer_bytes(file_, bytes, offset, *size, *scalar);
            return true;
        }
        case ConstValueKind::Floating: {
            std::optional<size_t> size = size_of_type(resolved, loc);
            if (!size.has_value() || *size > 16 ||
                offset + *size > bytes.size() ||
                !value.float_value.value.canonical()) {
                return false;
            }
            abi::write_scalar_bits(bytes.data() + offset,
                                   *size,
                                   value.float_value.value.low_bits,
                                   value.float_value.value.high_bits,
                                   file_.target_info().endianness);
            return true;
        }
        case ConstValueKind::Null:
            if (file_.type(resolved).kind == cir::TypeKind::MemberPointer) {
                return write_member_pointer_static_value(
                    bytes, offset, resolved, {}, 0, true, loc, relocations);
            }

            return true;
        case ConstValueKind::Address: {
            if (!relocations) {
                return false;
            }
            cir::EntityId target = value.address_value.entity;
            if (!target.valid() && value.address_value.string_literal.valid()) {
                target = string_literal_entity(
                    value.address_value.string_literal, loc);
            }
            if (!target.valid()) {
                return false;
            }
            relocations->push_back(cir::StaticInitializerRelocation{
                offset, target, value.address_value.byte_offset});
            return true;
        }
        case ConstValueKind::MemberPointer:
            return write_member_pointer_static_value(
                bytes, offset, resolved,
                value.member_pointer_value.method_entity,
                value.member_pointer_value.byte_offset,
                false, loc, relocations);
        case ConstValueKind::Complex: {
            cir::TypeId element = complex_element_type(resolved);
            std::optional<size_t> element_size = size_of_type(element, loc);
            if (!element_size.has_value()) {
                return false;
            }
            if (is_integer_type(element)) {
                cir::IntegerTypeShape shape =
                    cir::integer_shape_for_type(file_, element);
                ConstIntValue real;
                ConstIntValue imag;
                if (value.complex_value.has_integer_components) {
                    real = value.complex_value.integer_real.cast(
                        shape.bit_width, shape.is_unsigned);
                    imag = value.complex_value.integer_imag.cast(
                        shape.bit_width, shape.is_unsigned);
                } else {
                    auto converted_real = floating::to_integer(
                        value.complex_value.real, shape.bit_width,
                        !shape.is_unsigned);
                    auto converted_imag = floating::to_integer(
                        value.complex_value.imag, shape.bit_width,
                        !shape.is_unsigned);
                    if (!converted_real || !converted_imag) {
                        return false;
                    }
                    real = ConstIntValue::from_bits128(
                        *converted_real, shape.bit_width, shape.is_unsigned);
                    imag = ConstIntValue::from_bits128(
                        *converted_imag, shape.bit_width, shape.is_unsigned);
                }
                return write_static_const_value(
                           bytes, offset, element,
                           ConstValue::integer(real), loc, relocations) &&
                       write_static_const_value(
                           bytes, offset + *element_size, element,
                           ConstValue::integer(imag), loc, relocations);
            }
            if (value.complex_value.has_integer_components) {
                return false;
            }
            cir::FloatingSemantics semantics =
                floating::semantics_for_type(file_, element);
            auto real = floating::convert(value.complex_value.real, semantics);
            auto imag = floating::convert(value.complex_value.imag, semantics);
            if (!real || !imag) {
                return false;
            }
            return write_static_const_value(
                       bytes, offset, element,
                       ConstValue::floating(*real),
                       loc, relocations) &&
                   write_static_const_value(
                       bytes, offset + *element_size, element,
                       ConstValue::floating(*imag),
                       loc, relocations);
        }
        case ConstValueKind::Object: {
            if (!value.object_value) {
                return false;
            }
            const ConstObjectValue& object = *value.object_value;
            if (file_.type(resolved).kind == cir::TypeKind::Array) {
                cir::TypeId element = array_element_type(file_, resolved);
                std::optional<size_t> stride = size_of_type(element, loc);
                if (!stride.has_value()) {
                    return false;
                }
                for (size_t i = 0; i < object.elements.size(); ++i) {
                    if (!write_static_const_value(bytes,
                                                  offset + i * *stride,
                                                  element,
                                                  object.elements[i],
                                                  loc,
                                                  relocations)) {
                        return false;
                    }
                }
                return true;
            }
            const cir::RecordFacts* facts = file_.record_facts_for_type(resolved);
            if (!facts) {
                return false;
            }
            bool sparse_union =
                facts->kind == cir::RecordKind::Union &&
                object.active_union_member.valid() &&
                object.elements.size() == 1;
            size_t element_index = 0;
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (sparse_union &&
                    field.entity != object.active_union_member) {
                    continue;
                }
                if (element_index >= object.elements.size()) {
                    return false;
                }
                const ConstValue& element = object.elements[element_index++];
                if (field.is_bitfield) {
                    std::optional<int64_t> scalar = element.try_as_int64();
                    uint32_t storage_bits =
                        field.storage_size == 0 ? 32 : field.storage_size;
                    uint32_t width = cir::bitfield_value_width(file_, field);
                    size_t storage_bytes = (storage_bits + 7) / 8;
                    size_t storage_offset = offset + field.offset;
                    if (!scalar.has_value() || width == 0 || width > 64 ||
                        storage_bits > 64 ||
                        storage_offset + storage_bytes > bytes.size()) {
                        return false;
                    }
                    uint64_t storage = abi::read_scalar_bits(
                        bytes.data() + storage_offset, storage_bytes,
                        file_.target_info().endianness).low;
                    uint64_t mask = width == 64
                        ? ~uint64_t{0}
                        : ((uint64_t{1} << width) - 1);
                    uint64_t shifted_mask = mask << field.bit_offset;
                    storage = (storage & ~shifted_mask) |
                        ((static_cast<uint64_t>(*scalar) & mask)
                         << field.bit_offset);
                    abi::write_scalar_bits(
                        bytes.data() + storage_offset, storage_bytes,
                        storage, 0, file_.target_info().endianness);
                    continue;
                }
                if (!write_static_const_value(bytes,
                                              offset + field.offset,
                                              field.type.type,
                                              element,
                                              loc,
                                              relocations)) {
                    return false;
                }
            }
            return element_index == object.elements.size();
        }
        default:
            return false;
    }
}

bool Session::try_publish_constant_construction(
    DeclResult& started,
    const std::vector<ExprResult>& arguments,
    ConstructorInitializationKind init_kind,
    bool value_initialize,
    SrcLoc loc) {
    if (!lang_opts_.is_cxx_mode() || !started.entity.valid() ||
        !file_.valid(started.entity) ||
        (!file_.entity(started.entity).decl_flags.is_constexpr &&
         !file_.entity(started.entity).decl_flags.is_constinit)) {
        return false;
    }

    SpeculativeParseGuard probe = speculative_parse();

    std::vector<ExprResult> argument_copies;
    argument_copies.reserve(arguments.size());
    for (const ExprResult& argument : arguments) {
        argument_copies.push_back(clone_initializer_for_probe(argument));
    }
    ConstructorCallMaterialization materialized =
        materialize_constructor_call(started.type, std::move(argument_copies),
                                     loc, init_kind);
    if (!materialized.constructor.valid() || materialized.has_error) {
        return false;
    }
    // Constant evaluation must demand every delegating definition immediately
    // because the ODR-use fixpoint is too late for transitive evaluation.
    std::unordered_set<uint64_t> demanded_constructors;
    cir::EntityId demanded = materialized.constructor;
    while (demanded.valid() && file_.valid(demanded) &&
           demanded_constructors.insert(
               static_cast<uint64_t>(demanded.index)).second) {
        if (request_class_member_instantiation(
                demanded,
                cir::InstantiationDemandKind::ConstantEvaluation,
                loc) != InstantiationDemandResult::Satisfied) {
            return false;
        }
        const cir::RecordMethodFact* demanded_fact =
            file_.method_fact(demanded);
        if (!demanded_fact || !demanded_fact->constructor_delegation ||
            !demanded_fact->constructor_delegation->resolved()) {
            break;
        }
        demanded =
            demanded_fact->constructor_delegation->target_constructor;
    }

    std::string temp_name = ".constexpr.object." +
        std::to_string(compound_literal_counter_++);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             started.type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("constexpr.object.eval");
    cir::InstId place = builder_.local_place(temp, started.type, loc);
    if (value_initialize) {
        builder_.zero_object(place, loc);
    }
    emit_construct_in_place(place,
                            structor_complete_variant(materialized.constructor),
                            materialized.argument_values,
                            loc);
    cir::InstId loaded = builder_.lvalue_to_rvalue(place, loc);
    cir::Fragment eval_fragment = finish_fragment_block(block, previous);
    eval_fragment = chain(std::move(materialized.argument_fragment),
                          std::move(eval_fragment),
                          loc);

    LangOptions consteval_options = lang_opts_;
    consteval_options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(consteval_options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_core_constant_expression();
    request.target_type = started.type;
    request.loc = loc;
    request.required = false;

    ConstEvalResult result = engine.evaluate_fragment(
        eval_fragment, cir::ValueRef(loaded), request);
    if (result.status != ConstEvalStatus::Constant ||
        !result.value.has_value()) {
        return false;
    }

    std::optional<size_t> size = size_of_type(started.type, loc);
    if (!size.has_value()) {
        return false;
    }
    std::vector<uint8_t> bytes(*size, 0);
    std::vector<cir::StaticInitializerRelocation> relocations;
    if (!write_static_const_value(bytes, 0, started.type, *result.value,
                                  loc, &relocations)) {
        return false;
    }
    std::string state_error;
    std::optional<cir::ConstantStateFact> state =
        constant_state_from_value(file_, started.type, *result.value,
                                  &state_error);
    if (!state.has_value()) {
        return false;
    }
    cir::Entity& variable = file_.entity_mut(started.entity);
    variable.has_static_initializer = true;
    variable.static_initializer_bytes = std::move(bytes);
    variable.static_initializer_relocations = std::move(relocations);
    variable.constant_state = file_.add_constant_state(std::move(*state));
    probe.commit();
    return true;
}

ExprResult Session::fold_immediate_constructor_invocation(
    ExprResult object,
    cir::InstId destination,
    cir::EntityId constructor,
    SrcLoc loc) {
    if (object.has_error || !object.value.valid() ||
        !destination.valid() || !file_.valid(destination) ||
        !constructor.valid() || !file_.valid(constructor) ||
        !file_.entity(constructor).decl_flags.is_consteval) {
        return object;
    }

    cir::InstKind destination_kind = file_.inst(destination).kind;
    if (destination_kind != cir::InstKind::LocalPlace &&
        destination_kind != cir::InstKind::GlobalPlace) {
        return object;
    }

    LangOptions options = lang_opts_;
    options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_immediate_function();
    request.target_type = object.type;
    request.loc = loc;
    request.required = true;
    ConstEvalResult evaluated = engine.evaluate_fragment(
        object.fragment, cir::ValueRef(object.value), request);
    if (evaluated.status != ConstEvalStatus::Constant ||
        !evaluated.value.has_value()) {

        return object;
    }

    std::optional<size_t> size = size_of_type(object.type, loc);
    if (!size.has_value()) {
        return object;
    }
    std::vector<uint8_t> bytes(*size, 0);
    std::vector<cir::StaticInitializerRelocation> relocations;
    if (!write_static_const_value(bytes, 0, object.type, *evaluated.value,
                                  loc, &relocations)) {
        return object;
    }
    std::string state_error;
    std::optional<cir::ConstantStateFact> state =
        constant_state_from_value(file_, object.type, *evaluated.value,
                                  &state_error);
    if (!state.has_value()) {
        return object;
    }

    std::string name = ".immediate.object." +
        std::to_string(compound_literal_counter_++);
    cir::EntityId backing = builder_.add_entity(
        cir::EntityKind::Variable, name, object.type, {}, loc,
        cir::StorageDuration::Static, cir::MemorySpace::Default, {});
    {
        cir::Entity& record = file_.entity_mut(backing);
        record.is_definition = true;
        record.linkage = cir::LinkageKind::Internal;
        record.qualifiers = cir::QualConst;
        record.has_static_initializer = true;
        record.static_initializer_bytes = std::move(bytes);
        record.static_initializer_relocations = std::move(relocations);
        record.constant_state = file_.add_constant_state(std::move(*state));
    }
    mark_static_initializer_relocations_required(
        file_.entity(backing).static_initializer_relocations, loc);

    cir::BlockId destination_block{};
    bool destination_block_has_construction = false;
    for (cir::BlockId candidate : object.fragment.blocks) {
        if (!file_.valid(candidate)) {
            continue;
        }
        const cir::Block& candidate_block = file_.block(candidate);
        if (std::find(candidate_block.instructions.begin(),
                      candidate_block.instructions.end(),
                      destination) != candidate_block.instructions.end()) {
            destination_block = candidate;
            destination_block_has_construction =
                std::any_of(candidate_block.instructions.begin(),
                            candidate_block.instructions.end(),
                            [&](cir::InstId instruction) {
                                if (!file_.valid(instruction) ||
                                    file_.inst(instruction).kind !=
                                        cir::InstKind::ConstructInPlace) {
                                    return false;
                                }
                                std::vector<cir::Operand> operands =
                                    file_.operands(
                                        file_.inst(instruction).operands);
                                if (operands.empty()) {
                                    return false;
                                }
                                const auto* place =
                                    std::get_if<cir::ValueRef>(
                                        &operands.front().data);
                                return place && place->inst == destination;
                            });
            break;
        }
    }
    bool preserve_destination_block =
        destination_block.valid() && !destination_block_has_construction;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.immediate.constructor");
    cir::InstId target = preserve_destination_block
        ? destination
        : rematerialize_entity_place(destination, loc);
    cir::InstId source = builder_.global_place(backing, loc);
    cir::InstId value = builder_.lvalue_to_rvalue(source, loc);
    builder_.store(target, value, loc);
    cir::InstId loaded = builder_.lvalue_to_rvalue(target, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);
    if (preserve_destination_block) {
        builder_.branch_from(destination_block, fragment.entry, {}, loc);
        fragment.blocks.insert(fragment.blocks.begin(), destination_block);
        fragment.entry = destination_block;
    }

    object.fragment = std::move(fragment);
    object.value = loaded;
    object.category = ValueCategory::PrValue;
    return object;
}

bool Session::try_publish_constant_initializer(
    cir::EntityId entity_id,
    cir::TypeId type,
    const ExprResult& initializer,
    SrcLoc loc,
    bool* diagnosed_error,
    bool require_static_image) {
    if (!lang_opts_.is_cxx_mode() || !entity_id.valid() ||
        !file_.valid(entity_id) || initializer.has_error ||
        expr_is_dependent(initializer) ||
        (!file_.entity(entity_id).decl_flags.is_constexpr &&
         !file_.entity(entity_id).decl_flags.is_constinit)) {
        return false;
    }

    ExprResult candidate = clone_initializer_for_probe(initializer);
    std::optional<SpeculativeParseGuard> probe;
    auto begin_probe = [&]() {
        if (!probe.has_value()) {
            probe.emplace(speculative_parse());
        }
    };
    if (!candidate.value.valid() &&
        candidate.category == ValueCategory::InitList &&
        is_aggregate_type(type)) {
        begin_probe();
        candidate = collect_initialized_prvalue(type, std::move(candidate), loc);
        for (cir::LifetimeId lifetime : candidate.materialized_lifetimes) {
            retire_lifetime(lifetime);
        }
        candidate.materialized_lifetimes.clear();
    }
    if (!candidate.value.valid() && candidate.place.valid()) {
        begin_probe();

        if (is_reference_type(type)) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("constexpr.reference.bind");
            candidate.value = builder_.addr_of(candidate.place, loc);
            candidate.fragment = chain(std::move(candidate.fragment),
                                       finish_fragment_block(block, previous),
                                       loc);
            candidate.category = ValueCategory::PrValue;
        } else {
            candidate = require_value(std::move(candidate), UseContext::RValue,
                                      loc);
        }
    }
    if (!candidate.value.valid() || candidate.has_error) {
        return false;
    }

    LangOptions options = lang_opts_;
    options.enable_consteval_engine = true;
    ConstEvalEngine engine(make_consteval_context(options));
    ConstEvalRequest request;
    request.mode = ConstEvalMode::cpp_core_constant_expression();
    request.target_type = type;
    request.loc = loc;
    request.required = true;
    ConstEvalResult result = engine.evaluate_fragment(
        candidate.fragment, cir::ValueRef(candidate.value), request);
    if (probe.has_value()) {
        probe->rollback();
    }
    if (result.status != ConstEvalStatus::Constant ||
        !result.value.has_value()) {

        if (diagnosed_error && result.status == ConstEvalStatus::Error &&
            !result.diagnostics.empty()) {
            const ConstEvalDiagnostic& diag = result.diagnostics.front();
            report_error(diag.message, diag.loc.isInvalid() ? loc : diag.loc);
            *diagnosed_error = true;
        }
        return false;
    }

    ConstantStateAddressPolicy address_is_durable =
        [this, entity_id](cir::EntityId target) {
            if (!target.valid() || !file_.valid(target)) {
                return false;
            }
            cir::StorageDuration duration =
                file_.entity(target).storage_duration;
            if (duration == cir::StorageDuration::Static ||
                duration == cir::StorageDuration::Thread) {
                return true;
            }
            cir::EntityId enclosing = current_function_entity();
            return enclosing.valid() &&
                   file_.entity(target).owning_function == enclosing &&
                   file_.entity(entity_id).storage_duration ==
                       cir::StorageDuration::Automatic;
        };
    std::string state_error;
    std::optional<cir::ConstantStateFact> state =
        constant_state_from_value(file_, type, *result.value, &state_error,
                                  &address_is_durable);
    std::optional<size_t> size = size_of_type(type, loc);
    if (!state.has_value() || !size.has_value()) {
        return false;
    }
    if (!require_static_image) {

        cir::ConstantStateId state_id =
            file_.add_constant_state(std::move(*state));
        file_.entity_mut(entity_id).constant_state = state_id;
        return true;
    }
    std::vector<uint8_t> bytes(*size, 0);
    std::vector<cir::StaticInitializerRelocation> relocations;
    if (!write_static_const_value(bytes, 0, type, *result.value, loc,
                                  &relocations)) {
        return false;
    }
    cir::ConstantStateId state_id =
        file_.add_constant_state(std::move(*state));
    cir::Entity& entity = file_.entity_mut(entity_id);
    entity.constant_state = state_id;
    entity.has_static_initializer = true;
    entity.static_initializer_bytes = std::move(bytes);
    entity.static_initializer_relocations = std::move(relocations);
    return true;
}

cir::EntityId Session::union_active_member_from_initializer(
    cir::TypeId type,
    const ExprResult& initializer) const {
    cir::TypeId resolved = file_.resolved_type(type);
    const cir::RecordFacts* facts = file_.record_facts_for_type(resolved);
    if (!facts || facts->kind != cir::RecordKind::Union ||
        !initializer.init_list || initializer.init_list->elements.empty()) {
        return {};
    }
    const InitElementInput& first = initializer.init_list->elements.front();
    if (!first.designators.empty() &&
        first.designators.front().kind == InitDesignatorKind::Field) {
        std::string_view selected = first.designators.front().field_name;
        for (const cir::RecordFieldFact& field : facts->fields) {
            if (field.name.valid() && file_.name(field.name) == selected) {
                return field.entity;
            }
        }
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (!field.is_virtual_base_storage &&
            !field.is_flexible_array_member) {
            return field.entity;
        }
    }
    return {};
}

void Session::publish_constant_state_from_static_initializer(
    cir::EntityId entity_id,
    cir::EntityId active_union_member) {
    if (!entity_id.valid() || !file_.valid(entity_id)) {
        return;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if ((!entity.decl_flags.is_constexpr &&
         !entity.decl_flags.is_constinit) ||
        !entity.has_static_initializer || entity.constant_state.valid()) {
        return;
    }
    std::optional<cir::ConstantStateFact> state =
        constant_state_from_static_image(
            file_, entity.type, entity.static_initializer_bytes, 0,
            entity.static_initializer_relocations, active_union_member);
    if (state.has_value()) {
        cir::ConstantStateId state_id =
            file_.add_constant_state(std::move(*state));
        file_.entity_mut(entity_id).constant_state = state_id;
    }
}

void Session::mark_static_initializer_relocations_required(
    const std::vector<cir::StaticInitializerRelocation>& relocations,
    SrcLoc loc) {
    for (const cir::StaticInitializerRelocation& relocation : relocations) {
        if (!relocation.entity.valid() || !file_.valid(relocation.entity)) {
            continue;
        }
        if (file_.entity(relocation.entity).kind == cir::EntityKind::Method) {
            mark_record_method_required(relocation.entity, loc);
        }
    }
}

bool Session::write_member_pointer_static_value(
    std::vector<uint8_t>& bytes,
    size_t offset,
    cir::TypeId type,
    cir::EntityId member,
    int64_t data_member_offset,
    bool is_null,
    SrcLoc loc,
    std::vector<cir::StaticInitializerRelocation>* relocations) {
    type = file_.resolved_type(type);
    std::optional<size_t> size = size_of_type(type, loc);
    if (!file_.valid(type) || file_.type(type).kind != cir::TypeKind::MemberPointer ||
        !size.has_value() || offset + *size > bytes.size()) {
        report_error("member pointer static initializer has invalid target type",
                     loc);
        return false;
    }

    bool points_to_function = file_.member_pointer_points_to_function(type);
    if (is_null) {
        write_integer_bytes(file_, bytes, offset, *size, points_to_function ? 0 : -1);
        return true;
    }

    if (!points_to_function) {
        if (member.valid()) {
            const cir::RecordFieldFact* field = file_.field_fact(member);
            if (!field || field->is_bitfield) {
                report_error(
                    "data member pointer static initializer requires a non-bit-field member",
                    loc);
                return false;
            }
            data_member_offset = static_cast<int64_t>(field->offset);
            const cir::Entity& member_entity = file_.entity(member);
            if (member_entity.declaring_record.valid() &&
                member_entity.declaring_record != member_entity.parent) {
                if (const cir::RecordFacts* owner =
                        file_.record_facts(member_entity.declaring_record)) {
                    for (const cir::VariantMemberFact& variant :
                         owner->variant_members) {
                        if (variant.member != member) {
                            continue;
                        }
                        data_member_offset = 0;
                        for (cir::EntityId step : variant.path) {
                            if (const cir::RecordFieldFact* path_field =
                                    file_.field_fact(step)) {
                                data_member_offset += static_cast<int64_t>(
                                    path_field->offset);
                            }
                        }
                        break;
                    }
                }
            }
        }
        write_integer_bytes(file_, bytes, offset, *size, data_member_offset);
        return true;
    }

    const cir::RecordMethodFact* method = file_.method_fact(member);
    if (!method || method->is_static) {
        report_error(
            "member function pointer static initializer requires a non-static method",
            loc);
        return false;
    }

    size_t pointer_size =
        static_cast<size_t>(std::max(1, (file_.target_info().pointer_width + 7) / 8));
    write_integer_bytes(file_, bytes, offset, *size, 0);
    if (method->is_virtual) {
        if (method->vtable_slot < 0) {
            report_error(
                "virtual member function pointer static initializer is missing a vtable slot",
                loc);
            return false;
        }
        write_integer_bytes(
            file_,
            bytes,
            offset,
            std::min(pointer_size, *size),
            1 + static_cast<int64_t>(pointer_size) *
                    static_cast<int64_t>(method->vtable_slot));
    } else {
        if (!relocations) {
            report_error("static initializer relocation has no destination image",
                         loc);
            return false;
        }
        relocations->push_back(cir::StaticInitializerRelocation{
            offset,
            member,
            0,
        });
    }
    if (offset + pointer_size < bytes.size()) {
        write_integer_bytes(file_, bytes,
                            offset + pointer_size,
                            std::min(pointer_size,
                                     bytes.size() - offset - pointer_size),
                            0);
    }
    return true;
}

cir::EntityId Session::materialize_template_parameter_object(
    cir::TypeId type,
    const TemplateArgument& argument,
    std::string_view parameter_name,
    SrcLoc loc) {
    std::string identity = template_argument_identity_key(argument);
    auto existing = tstate().template_parameter_object_cache_.find(identity);
    if (existing != tstate().template_parameter_object_cache_.end()) {
        return existing->second;
    }

    std::vector<cir::StaticInitializerRelocation> relocations;
    std::optional<std::vector<uint8_t>> bytes =
        template_argument_static_initializer_bytes(type,
                                                   argument,
                                                   loc,
                                                   &relocations);
    if (!bytes.has_value()) {
        return {};
    }

    std::string name = ".nttp.object." +
                       std::to_string(compound_literal_counter_++);
    if (!parameter_name.empty()) {
        name += ".";
        name += parameter_name;
    }

    cir::EntityId object = builder_.add_entity(cir::EntityKind::Variable,
                                               name,
                                               type,
                                               {},
                                               loc,
                                               cir::StorageDuration::Static,
                                               cir::MemorySpace::Default,
                                               {});
    cir::Entity& record = file_.entity_mut(object);
    record.is_definition = true;
    record.linkage = file_.template_argument_references_internal_entity(argument)
        ? cir::LinkageKind::Internal
        : cir::LinkageKind::LinkOnceODR;
    record.object_origin = cir::EntityObjectOrigin::TemplateParameterObject;
    record.qualifiers = cir::QualConst;
    record.has_static_initializer = true;
    record.static_initializer_bytes = std::move(*bytes);
    record.static_initializer_relocations = std::move(relocations);
    record.has_constant_value = true;
    record.constant_value_kind = argument.value_kind;
    record.constant_null_kind = argument.null_kind;
    record.constant_integer_value = argument.integer_value;
    record.constant_floating_value = argument.floating_value;
    record.constant_entity = argument.value_entity;
    record.constant_closure_identity = argument.closure_identity;
    record.constant_byte_offset = argument.value_byte_offset;
    record.constant_value_elements = argument.value_elements;
    tstate().template_parameter_object_cache_.emplace(std::move(identity), object);
    tstate().template_parameter_object_records_.push_back(
        {argument, object});
    return object;
}

std::optional<std::vector<uint8_t>>
Session::template_argument_static_initializer_bytes(
    cir::TypeId type,
    const TemplateArgument& argument,
    SrcLoc loc,
    std::vector<cir::StaticInitializerRelocation>* relocations) {
    std::optional<size_t> size = size_of_type(type, loc);
    if (!size.has_value()) {
        return std::nullopt;
    }
    std::vector<uint8_t> bytes(*size, 0);
    if (!write_template_argument_static_value(bytes,
                                              0,
                                              type,
                                              argument,
                                              loc,
                                              relocations)) {
        return std::nullopt;
    }
    if (relocations) {
        mark_static_initializer_relocations_required(*relocations, loc);
    }
    return bytes;
}

bool Session::write_template_argument_static_value(
    std::vector<uint8_t>& bytes,
    size_t offset,
    cir::TypeId type,
    const TemplateArgument& argument,
    SrcLoc loc,
    std::vector<cir::StaticInitializerRelocation>* relocations) {
    type = file_.resolved_type(type);
    std::optional<size_t> size = size_of_type(type, loc);
    if (!file_.valid(type) || !size.has_value() ||
        offset + *size > bytes.size()) {
        report_error("template parameter object initializer writes outside object bounds",
                     loc);
        return false;
    }

    const cir::Type& node = file_.type(type);
    switch (node.kind) {
        case cir::TypeKind::Array: {
            if (argument.value_kind != cir::TemplateValueKind::StructuralObject) {
                report_error("template parameter object array subobject has invalid value",
                             loc);
                return false;
            }
            const auto* array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(type));
            if (!array || !array->size.has_value()) {
                report_error("template parameter object has incomplete array type",
                             loc);
                return false;
            }
            if (argument.value_elements.size() != *array->size) {
                report_error("template parameter object array value has invalid size",
                             loc);
                return false;
            }
            std::optional<size_t> element_size =
                size_of_type(array->element_type.type, loc);
            if (!element_size.has_value()) {
                return false;
            }
            bool ok = true;
            for (size_t index = 0; index < *array->size; ++index) {
                ok = write_template_argument_static_value(
                         bytes,
                         offset + index * *element_size,
                         array->element_type.type,
                         argument.value_elements[index],
                         loc,
                         relocations) &&
                     ok;
            }
            return ok;
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts = file_.record_facts_for_type(type);
            if (facts && facts->is_lambda_closure) {
                if (argument.value_kind != cir::TemplateValueKind::Closure ||
                    facts->lambda_has_capture ||
                    facts->closure_identity != argument.closure_identity ||
                    !argument.value_elements.empty()) {
                    report_error(
                        "template parameter closure object has invalid identity",
                        loc);
                    return false;
                }
                return true;
            }
            if (argument.value_kind != cir::TemplateValueKind::StructuralObject) {
                report_error("template parameter object class subobject has invalid value",
                             loc);
                return false;
            }
            if (!facts || facts->is_incomplete) {
                report_error("template parameter object has incomplete class type",
                             loc);
                return false;
            }
            bool ok = true;
            size_t element_index = 0;
            // A union stores one value, not one per field: `value_elements`
            // holds just the active member and `value_entity` names it.  The
            // surrounding bytes were already zero-filled by
            // template_argument_static_initializer_bytes, so writing only the
            // active member reproduces the layout clang emits (active member
            // at its offset, the rest padding).  Same shape that
            // write_static_const_value already consumes for constant unions.
            bool sparse_union = facts->kind == cir::RecordKind::Union &&
                                argument.value_entity.valid() &&
                                argument.value_elements.size() == 1;
            if (facts->kind == cir::RecordKind::Union &&
                argument.value_elements.empty()) {
                // Value-initialized union with no active member: nothing to
                // write, and no field should be consumed.
                return true;
            }
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage ||
                    field.is_flexible_array_member) {
                    continue;
                }
                if (sparse_union && field.entity != argument.value_entity) {
                    continue;
                }
                if (field.is_bitfield) {
                    report_error(
                        "template parameter object bit-field subobjects are not supported yet",
                        loc);
                    ok = false;
                    continue;
                }
                if (element_index >= argument.value_elements.size()) {
                    report_error("template parameter object class value has invalid size",
                                 loc);
                    return false;
                }
                ok = write_template_argument_static_value(
                         bytes,
                         offset + static_cast<size_t>(field.offset),
                         field.type.type,
                         argument.value_elements[element_index],
                         loc,
                         relocations) &&
                     ok;
                ++element_index;
            }
            if (element_index != argument.value_elements.size()) {
                report_error("template parameter object class value has invalid size",
                             loc);
                return false;
            }
            return ok;
        }
        case cir::TypeKind::Enum: {
            const auto* enum_payload =
                std::get_if<cir::EnumTypePayload>(&file_.type_payload(type));
            cir::TypeId underlying =
                enum_payload && enum_payload->underlying_type.valid()
                    ? enum_payload->underlying_type.type
                    : builder_.int_type();
            return write_template_argument_static_value(bytes,
                                                        offset,
                                                        underlying,
                                                        argument,
                                                        loc,
                                                        relocations);
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {
            bool is_reference = node.kind == cir::TypeKind::LValueReference ||
                                node.kind == cir::TypeKind::RValueReference;
            if (argument.value_kind == cir::TemplateValueKind::Null &&
                !is_reference) {
                write_integer_bytes(file_, bytes, offset, *size, 0);
                return true;
            }
            if (argument.value_kind == cir::TemplateValueKind::Address &&
                argument.value_entity.valid() &&
                file_.valid(argument.value_entity)) {
                if (!relocations) {
                    report_error(
                        "template parameter object pointer initializer has no relocation image",
                        loc);
                    return false;
                }
                relocations->push_back(cir::StaticInitializerRelocation{
                    offset,
                    argument.value_entity,
                    argument.value_byte_offset,
                });
                write_integer_bytes(file_, bytes, offset, *size, 0);
                return true;
            }
            report_error(
                is_reference
                    ? "template parameter object reference subobject must name an object"
                    : "template parameter object pointer subobject must name an object or be null",
                loc);
            return false;
        }
        case cir::TypeKind::MemberPointer:
            if (argument.value_kind == cir::TemplateValueKind::Null &&
                (argument.null_kind == cir::TemplateNullKind::MemberPointer ||
                 argument.null_kind == cir::TemplateNullKind::Nullptr)) {
                return write_member_pointer_static_value(bytes,
                                                         offset,
                                                         type,
                                                         {},
                                                         0,
                                                         true,
                                                         loc,
                                                         relocations);
            }
            if (argument.value_kind == cir::TemplateValueKind::MemberPointer) {
                return write_member_pointer_static_value(bytes,
                                                         offset,
                                                         type,
                                                         argument.value_entity,
                                                         argument.value_byte_offset,
                                                         false,
                                                         loc,
                                                         relocations);
            }
            report_error("template parameter object member-pointer subobject has invalid value",
                         loc);
            return false;
        default:
            break;
    }

    if (node.kind == cir::TypeKind::Builtin) {
        const auto* builtin =
            std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(type));
        if (builtin && builtin->kind == cir::BuiltinTypeKind::NullPtr) {
            if (argument.value_kind != cir::TemplateValueKind::Null ||
                argument.null_kind != cir::TemplateNullKind::Nullptr) {
                report_error("template parameter object nullptr_t subobject has invalid value",
                             loc);
                return false;
            }
            write_integer_bytes(file_, bytes, offset, *size, 0);
            return true;
        }
        if (builtin && builtin->kind == cir::BuiltinTypeKind::Bool) {
            if (argument.value_kind != cir::TemplateValueKind::Boolean &&
                argument.value_kind != cir::TemplateValueKind::Integer) {
                report_error("template parameter object bool subobject has invalid value",
                             loc);
                return false;
            }
            write_integer_bytes(file_, bytes,
                                offset,
                                *size,
                                argument.integer_value.is_zero() ? 0 : 1);
            return true;
        }
    }

    if (cir::is_integer_like_type(file_, type)) {
        if (argument.value_kind != cir::TemplateValueKind::Integer &&
            argument.value_kind != cir::TemplateValueKind::Boolean) {
            report_error("template parameter object integer subobject has invalid value",
                         loc);
            return false;
        }
        write_integer_bytes(file_, bytes, offset, *size,
                            argument.integer_value);
        return true;
    }

    if (cir::is_floating_type(file_, type)) {
        cir::FloatingSemantics semantics =
            floating::semantics_for_type(file_, type);
        floating::FloatResult value;
        if (argument.value_kind == cir::TemplateValueKind::Floating) {
            value = floating::convert(argument.floating_value, semantics);
        } else {
            value.error = floating::FloatError::InvalidEncoding;
        }
        if (!value || !value->canonical() || *size > 16) {
            report_error(
                "template parameter object floating subobject has invalid value",
                loc);
            return false;
        }
        abi::write_scalar_bits(bytes.data() + offset,
                               *size,
                               value->low_bits,
                               value->high_bits,
                               file_.target_info().endianness);
        return true;
    }

    report_error("unsupported template parameter object subobject type", loc);
    return false;
}

bool Session::write_static_zero(std::vector<uint8_t>& bytes,
                                size_t offset,
                                cir::TypeId type,
                                SrcLoc loc) {
    std::optional<size_t> size = size_of_type(type, loc);
    if (!size.has_value() || offset + *size > bytes.size()) {
        report_error("static initializer writes outside object bounds", loc);
        return false;
    }
    std::fill(bytes.begin() + static_cast<std::ptrdiff_t>(offset),
              bytes.begin() + static_cast<std::ptrdiff_t>(offset + *size),
              0);
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return true;
    }
    switch (file_.type(resolved).kind) {
        case cir::TypeKind::MemberPointer:
            return write_member_pointer_static_value(bytes,
                                                     offset,
                                                     resolved,
                                                     {},
                                                     0,
                                                     true,
                                                     loc);
        case cir::TypeKind::Array: {
            const auto* array =
                std::get_if<cir::ArrayTypePayload>(&file_.type_payload(resolved));
            if (!array || !array->size.has_value()) {
                return false;
            }
            std::optional<size_t> element_size =
                size_of_type(array->element_type.type, loc);
            if (!element_size.has_value()) {
                return false;
            }
            bool ok = true;
            for (size_t index = 0; index < *array->size; ++index) {
                ok = write_static_zero(bytes,
                                       offset + index * *element_size,
                                       array->element_type.type,
                                       loc) && ok;
            }
            return ok;
        }
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts = file_.record_facts_for_type(resolved);
            if (!facts || facts->is_incomplete) {
                return false;
            }
            bool ok = true;
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_flexible_array_member || field.is_bitfield ||
                    !field.type.type.valid()) {
                    continue;
                }
                ok = write_static_zero(bytes,
                                       offset + static_cast<size_t>(field.offset),
                                       field.type.type,
                                       loc) && ok;
            }
            return ok;
        }
        default:
            break;
    }
    return true;
}

bool Session::write_static_value(std::vector<uint8_t>& bytes,
                                 size_t offset,
                                 cir::TypeId type,
                                 const ExprResult& value,
                                 SrcLoc loc,
                                 std::vector<cir::StaticInitializerRelocation>* relocations) {
    type = file_.resolved_type(type);
    if (!file_.valid(type)) {
        report_error("static initializer has invalid target type", loc);
        return false;
    }

    if (relocations != nullptr && !relocations->empty()) {
        if (std::optional<size_t> value_size = size_of_type(type, loc)) {
            const size_t clear_begin = offset;
            const size_t clear_end = offset + *value_size;
            relocations->erase(
                std::remove_if(relocations->begin(), relocations->end(),
                    [&](const cir::StaticInitializerRelocation& r) {
                        return r.offset >= clear_begin && r.offset < clear_end;
                    }),
                relocations->end());
        }
    }

    if (value.category == ValueCategory::InitList ||
        (value.init_list != nullptr && is_aggregate_type(type))) {
        if (!value.init_list ||
            (value.init_list->elements.empty() &&
             !aggregate_has_default_member_initializer(type))) {
            return write_static_zero(bytes, offset, type, loc);
        }

        ExprResult copy = value;
        copy.init_list = clone_init_list_value(*value.init_list);
        std::vector<cir::StaticInitializerRelocation> nested_relocations;
        std::optional<std::vector<uint8_t>> nested =
            static_initializer_bytes(type,
                                     std::move(copy),
                                     loc,
                                     relocations ? &nested_relocations : nullptr);
        if (!nested.has_value()) {
            return false;
        }
        if (offset + nested->size() > bytes.size()) {
            report_error("static initializer writes outside object bounds", loc);
            return false;
        }
        std::copy(nested->begin(), nested->end(), bytes.begin() + static_cast<std::ptrdiff_t>(offset));
        if (relocations) {
            for (cir::StaticInitializerRelocation relocation : nested_relocations) {
                relocation.offset += offset;
                relocations->push_back(relocation);
            }
        }
        return true;
    }

    if (std::optional<std::vector<uint8_t>> string_bytes =
            string_literal_initializer_bytes(type, value, loc)) {
        if (offset + string_bytes->size() > bytes.size()) {
            report_error("static initializer writes outside object bounds", loc);
            return false;
        }
        std::copy(string_bytes->begin(), string_bytes->end(),
                  bytes.begin() + static_cast<std::ptrdiff_t>(offset));
        return true;
    }

    if (is_aggregate_type(type)) {

        if (value.entity.valid()) {
            const cir::Entity& source = file_.entity(value.entity);
            if (source.has_static_initializer &&
                type_equal(source.type, type)) {
                const std::vector<uint8_t>& image = source.static_initializer_bytes;
                if (offset + image.size() > bytes.size()) {
                    report_error("static initializer writes outside object bounds", loc);
                    return false;
                }
                std::copy(image.begin(), image.end(),
                          bytes.begin() + static_cast<std::ptrdiff_t>(offset));
                if (!source.static_initializer_relocations.empty()) {
                    if (!relocations) {
                        report_error("static initializer relocation has no destination image",
                                     loc);
                        return false;
                    }
                    for (cir::StaticInitializerRelocation relocation :
                         source.static_initializer_relocations) {
                        relocation.offset += offset;
                        relocations->push_back(relocation);
                    }
                }
                return true;
            }
        }
        report_error("aggregate global initializer must use an initializer list", loc);
        return false;
    }

    std::optional<size_t> size = size_of_type(type, loc);
    if (!size.has_value() || offset + *size > bytes.size()) {
        report_error("static initializer writes outside object bounds", loc);
        return false;
    }

    auto entity_operand = [&](cir::InstId inst, size_t index) -> cir::EntityId {
        if (!file_.valid(inst)) {
            return {};
        }
        std::vector<cir::Operand> operands = file_.operands(file_.inst(inst).operands);
        if (index >= operands.size()) {
            return {};
        }
        if (const auto* entity = std::get_if<cir::EntityId>(&operands[index].data)) {
            return *entity;
        }
        return {};
    };

    auto integer_literal_value = [&](cir::InstId inst) -> std::optional<int64_t> {
        if (!file_.valid(inst) || file_.inst(inst).kind != cir::InstKind::IntegerLiteral) {
            return std::nullopt;
        }
        const auto* literal =
            std::get_if<cir::LiteralPayload>(&file_.payload(file_.inst(inst).payload_index));
        const auto* literal_value = literal
            ? std::get_if<cir::IntegerValue>(&literal->value)
            : nullptr;
        if (!literal_value) {
            return std::nullopt;
        }
        return literal_value->try_as_int64();
    };

    auto place_relocation =
        [&](auto&& self,
            cir::InstId place,
            cir::EntityId& entity,
            int64_t& addend) -> bool {
            if (!file_.valid(place)) {
                return false;
            }
            const cir::Inst& inst = file_.inst(place);
            switch (inst.kind) {
                case cir::InstKind::GlobalPlace:
                    entity = entity_operand(place, 0);
                    return entity.valid();
                case cir::InstKind::StringLiteral:
                    entity = string_literal_entity(place, loc);
                    return entity.valid();
                case cir::InstKind::FieldAddr: {
                    std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
                    if (values.empty() || !self(self, values[0].inst, entity, addend)) {
                        return false;
                    }
                    cir::EntityId field_entity = entity_operand(place, 1);
                    const cir::RecordFieldFact* field = file_.field_fact(field_entity);
                    if (!field || field->is_bitfield) {
                        return false;
                    }
                    addend += static_cast<int64_t>(field->offset);
                    return true;
                }
                case cir::InstKind::ArrayElementPlace: {
                    std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
                    if (values.size() < 2 ||
                        !self(self, values[0].inst, entity, addend)) {
                        return false;
                    }
                    std::optional<int64_t> index = integer_literal_value(values[1].inst);
                    if (!index.has_value()) {

                        ExprResult index_expr;
                        index_expr.value = values[1].inst;
                        index_expr.fragment = value.fragment;
                        int64_t folded = 0;
                        if (try_evaluate_integer_constant(index_expr, folded)) {
                            index = folded;
                        }
                    }
                    if (!index.has_value()) {
                        return false;
                    }
                    cir::TypeId base_result = file_.inst(values[0].inst).result_type;
                    cir::TypeId base_object = file_.place_object_type(base_result);
                    cir::TypeId element = array_element_type(file_, base_object);
                    std::optional<size_t> element_size = size_of_type(element, loc);
                    if (!element_size.has_value()) {
                        return false;
                    }
                    addend += *index * static_cast<int64_t>(*element_size);
                    return true;
                }
                default:
                    return false;
            }
        };

    auto relocation_for_value =
        [&](auto&& self, const ExprResult& expr)
            -> std::optional<cir::StaticInitializerRelocation> {
            cir::StaticInitializerRelocation relocation;
            relocation.offset = offset;
            if (expr.category == ValueCategory::FunctionDesignator && expr.entity.valid()) {
                relocation.entity = expr.entity;
                return relocation;
            }
            if (!expr.value.valid() && expr.place.valid() && file_.valid(expr.place)) {

                cir::EntityId entity;
                int64_t addend = 0;
                if (place_relocation(place_relocation, expr.place, entity, addend)) {
                    relocation.entity = entity;
                    relocation.addend = addend;
                    return relocation;
                }
                return std::nullopt;
            }
            if (!expr.value.valid() || !file_.valid(expr.value)) {
                return std::nullopt;
            }
            const cir::Inst& inst = file_.inst(expr.value);
            if (inst.kind == cir::InstKind::FunctionToPointer) {
                relocation.entity = entity_operand(expr.value, 0);
                if (relocation.entity.valid()) {
                    return relocation;
                }
            }
            if (inst.kind == cir::InstKind::AddrOf) {
                std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
                if (values.empty()) {
                    return std::nullopt;
                }
                cir::EntityId entity;
                int64_t addend = 0;
                if (place_relocation(place_relocation, values[0].inst, entity, addend)) {
                    relocation.entity = entity;
                    relocation.addend = addend;
                    return relocation;
                }
            }
            if (inst.kind == cir::InstKind::LabelAddress) {

                const auto* label = std::get_if<cir::LabelAddressPayload>(
                    &file_.payload(inst.payload_index));
                if (label && label->target.valid() && current_function_.valid() &&
                    file_.valid(current_function_)) {
                    relocation.entity = file_.function(current_function_).entity;
                    relocation.block = label->target;
                    if (relocation.entity.valid()) {
                        return relocation;
                    }
                }
            }
            if (inst.kind == cir::InstKind::Cast) {
                std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
                if (!values.empty()) {
                    ExprResult inner = expr;
                    inner.value = values[0].inst;
                    return self(self, inner);
                }
            }
            return std::nullopt;
        };

    auto label_target_block = [&](cir::InstId id) -> cir::BlockId {
        while (id.valid() && file_.valid(id)) {
            const cir::Inst& in = file_.inst(id);
            if (in.kind == cir::InstKind::LabelAddress) {
                const auto* label = std::get_if<cir::LabelAddressPayload>(
                    &file_.payload(in.payload_index));
                return (label && label->target.valid()) ? label->target
                                                         : cir::BlockId{};
            }
            if (in.kind == cir::InstKind::Cast ||
                in.kind == cir::InstKind::LValueToRValue) {
                std::vector<cir::ValueRef> ops = file_.value_operands(in.operands);
                if (ops.empty()) {
                    return cir::BlockId{};
                }
                id = ops[0].inst;
                continue;
            }
            return cir::BlockId{};
        }
        return cir::BlockId{};
    };

    auto label_difference_relocation =
        [&](const ExprResult& expr)
            -> std::optional<cir::StaticInitializerRelocation> {
        if (!expr.value.valid() || !file_.valid(expr.value) ||
            !current_function_.valid() || !file_.valid(current_function_)) {
            return std::nullopt;
        }

        cir::InstId id = expr.value;
        while (id.valid() && file_.valid(id) &&
               file_.inst(id).kind == cir::InstKind::Cast) {
            std::vector<cir::ValueRef> ops =
                file_.value_operands(file_.inst(id).operands);
            if (ops.empty()) {
                break;
            }
            id = ops[0].inst;
        }
        if (!id.valid() || !file_.valid(id)) {
            return std::nullopt;
        }
        const cir::Inst& inst = file_.inst(id);
        if (inst.kind != cir::InstKind::BinaryOp) {
            return std::nullopt;
        }
        const auto* desc = std::get_if<cir::BinaryOpDescriptor>(
            &file_.payload(inst.payload_index));
        if (!desc || desc->op != cir::BinaryOpKind::Sub) {
            return std::nullopt;
        }
        std::vector<cir::ValueRef> operands = file_.value_operands(inst.operands);
        if (operands.size() != 2) {
            return std::nullopt;
        }
        cir::BlockId to = label_target_block(operands[0].inst);
        cir::BlockId from = label_target_block(operands[1].inst);
        if (!to.valid() || !from.valid()) {
            return std::nullopt;
        }
        cir::StaticInitializerRelocation relocation;
        relocation.offset = offset;
        relocation.entity = file_.function(current_function_).entity;
        relocation.block = to;
        relocation.subtract_block = from;
        if (!relocation.entity.valid()) {
            return std::nullopt;
        }
        return relocation;
    };

    std::vector<ConstEvalDiagnostic> engine_diagnostics;
    auto eval_const_value = [&]() -> std::optional<ConstValue> {
        if (!value.value.valid()) {
            return std::nullopt;
        }
        LangOptions consteval_options = lang_opts_;
        consteval_options.enable_consteval_engine = true;
        ConstEvalEngine engine(make_consteval_context(consteval_options));
        ConstEvalRequest request;
        request.mode = ConstEvalMode::c_static_initializer();
        request.target_type = type;
        request.loc = loc;
        request.required = true;
        ConstEvalResult result =
            engine.evaluate_fragment(value.fragment, cir::ValueRef(value.value), request);
        if (result.status == ConstEvalStatus::Constant && result.value.has_value()) {
            return result.value;
        }
        if (result.status == ConstEvalStatus::Error && !result.diagnostics.empty()) {
            engine_diagnostics = result.diagnostics;
        }
        return std::nullopt;
    };

    auto report_initializer_error = [&](std::string_view fallback) {
        if (!engine_diagnostics.empty()) {
            report_error(engine_diagnostics.front().message,
                         engine_diagnostics.front().loc);
            return;
        }
        report_error(std::string(fallback), loc);
    };

    auto write_const_int = [&](ConstIntValue int_value) {

        unsigned __int128 raw = int_value.is_unsigned
            ? int_value.to_unsigned_u128()
            : static_cast<unsigned __int128>(int_value.to_signed_i128());
        uint8_t fill =
            (!int_value.is_unsigned && int_value.to_signed_i128() < 0) ? 0xff : 0x00;
        if (offset >= bytes.size()) {
            return;
        }
        abi::write_scalar_bits(bytes.data() + offset,
                               std::min(*size, bytes.size() - offset),
                               static_cast<uint64_t>(raw),
                               static_cast<uint64_t>(raw >> 64),
                               file_.target_info().endianness,
                               fill);
    };

    cir::TypeKind kind = file_.type(type).kind;
    if (kind == cir::TypeKind::Record) {

        std::optional<ConstValue> constant = eval_const_value();
        if (constant.has_value() &&
            constant->kind == ConstValueKind::Object &&
            write_static_const_value(bytes,
                                     offset,
                                     type,
                                     *constant,
                                     loc,
                                     relocations)) {
            return true;
        }
        report_initializer_error(
            "global class initializer is not a supported constant");
        return false;
    }
    if (kind == cir::TypeKind::MemberPointer) {
        if (value.category == ValueCategory::MemberPointerDesignator &&
            value.entity.valid()) {
            return write_member_pointer_static_value(bytes,
                                                     offset,
                                                     type,
                                                     value.entity,
                                                     0,
                                                     false,
                                                     loc,
                                                     relocations);
        }
        if (value.value.valid() &&
            file_.inst(value.value).kind == cir::InstKind::MemberPointerValue) {
            cir::EntityId member = entity_operand(value.value, 0);
            return write_member_pointer_static_value(bytes,
                                                     offset,
                                                     type,
                                                     member,
                                                     0,
                                                     false,
                                                     loc,
                                                     relocations);
        }
        std::optional<ConstValue> constant = eval_const_value();
        if (constant.has_value() && constant->kind == ConstValueKind::Null &&
            (constant->null_kind == ConstNullKind::Nullptr ||
             constant->null_kind == ConstNullKind::MemberPointer)) {
            return write_member_pointer_static_value(bytes,
                                                     offset,
                                                     type,
                                                     {},
                                                     0,
                                                     true,
                                                     loc,
                                                     relocations);
        }
        if (constant.has_value() &&
            constant->kind == ConstValueKind::MemberPointer) {
            return write_member_pointer_static_value(
                bytes,
                offset,
                type,
                constant->member_pointer_value.method_entity,
                constant->member_pointer_value.byte_offset,
                false,
                loc,
                relocations);
        }
        report_error("global member pointer initializer is not a supported constant",
                     loc);
        return false;
    }
    if (kind == cir::TypeKind::Pointer || kind == cir::TypeKind::BlockPointer ||
        kind == cir::TypeKind::LValueReference ||
        kind == cir::TypeKind::RValueReference) {
        bool is_reference = kind == cir::TypeKind::LValueReference ||
                            kind == cir::TypeKind::RValueReference;
        if (std::optional<cir::StaticInitializerRelocation> relocation =
                relocation_for_value(relocation_for_value, value)) {
            if (relocations) {
                relocations->push_back(*relocation);
            } else {
                report_error("static initializer relocation has no destination image", loc);
                return false;
            }
            write_integer_bytes(file_, bytes, offset, *size, 0);
            return true;
        }
        std::optional<ConstValue> constant = eval_const_value();
        if (constant.has_value() &&
            (constant->kind == ConstValueKind::Null ||
             (constant->kind == ConstValueKind::Integer &&
              constant->int_value.is_zero()))) {
            write_integer_bytes(file_, bytes, offset, *size, 0);
            return true;
        }
        if (constant.has_value() && constant->kind == ConstValueKind::Integer) {
            write_const_int(constant->int_value);
            return true;
        }
        if (constant.has_value() && constant->kind == ConstValueKind::Address &&
            !constant->address_value.entity.valid() &&
            !constant->address_value.string_literal.valid() &&
            constant->address_value.allocation_id == 0) {

            write_integer_bytes(
                file_, bytes, offset, *size,
                static_cast<uint64_t>(constant->address_value.byte_offset));
            return true;
        }
        if (constant.has_value() && constant->kind == ConstValueKind::Address &&
            relocations) {

            cir::StaticInitializerRelocation relocation;
            relocation.offset = offset;
            relocation.addend = constant->address_value.byte_offset;
            if (constant->address_value.entity.valid()) {
                cir::StorageDuration duration =
                    file_.entity(constant->address_value.entity).storage_duration;
                if (duration == cir::StorageDuration::Automatic ||
                    duration == cir::StorageDuration::Parameter) {
                    report_error(
                        is_reference
                            ? "reference subobject must not bind to a temporary object"
                            : "address of an automatic object is not a constant expression",
                        loc);
                    return false;
                }
                relocation.entity = constant->address_value.entity;
            } else if (constant->address_value.string_literal.valid()) {
                relocation.entity =
                    string_literal_entity(constant->address_value.string_literal,
                                          loc);
            }
            if (relocation.entity.valid()) {
                relocations->push_back(relocation);
                write_integer_bytes(file_, bytes, offset, *size, 0);
                return true;
            }
        }
        report_initializer_error("global pointer initializer is not a supported constant");
        return false;
    }

    if (kind == cir::TypeKind::Enum) {
        const auto* enum_payload =
            std::get_if<cir::EnumTypePayload>(&file_.type_payload(type));
        cir::TypeId underlying = enum_payload && enum_payload->underlying_type.valid()
            ? enum_payload->underlying_type.type
            : builder_.int_type();
        return write_static_value(bytes, offset, underlying, value, loc, relocations);
    }

    if (kind == cir::TypeKind::Complex) {
        std::optional<ConstValue> constant = eval_const_value();
        const auto* complex_payload =
            std::get_if<cir::ComplexTypePayload>(&file_.type_payload(type));
        std::optional<size_t> element_size = complex_payload
            ? cir::size_of_type(file_, complex_payload->element_type.type)
            : std::nullopt;
        if (!constant.has_value() || !element_size.has_value()) {
            report_error("complex global initializer is not constant", loc);
            return false;
        }
        cir::TypeId element_type = complex_payload
            ? complex_payload->element_type.type
            : cir::TypeId{};
        if (complex_payload && is_integer_type(element_type)) {
            cir::IntegerTypeShape shape =
                cir::integer_shape_for_type(file_, element_type);
            auto convert_component = [&](const ConstValue& component)
                -> std::optional<ConstIntValue> {
                if (component.kind == ConstValueKind::Integer) {
                    return component.int_value.cast(
                        shape.bit_width, shape.is_unsigned);
                }
                if (component.kind == ConstValueKind::Floating) {
                    auto converted = floating::to_integer(
                        component.float_value.value, shape.bit_width,
                        !shape.is_unsigned);
                    if (converted) {
                        return ConstIntValue::from_bits128(
                            *converted, shape.bit_width, shape.is_unsigned);
                    }
                }
                return std::nullopt;
            };
            std::optional<ConstIntValue> real;
            std::optional<ConstIntValue> imag;
            if (constant->kind == ConstValueKind::Complex) {
                if (constant->complex_value.has_integer_components) {
                    real = constant->complex_value.integer_real.cast(
                        shape.bit_width, shape.is_unsigned);
                    imag = constant->complex_value.integer_imag.cast(
                        shape.bit_width, shape.is_unsigned);
                } else {
                    auto converted_real = floating::to_integer(
                        constant->complex_value.real, shape.bit_width,
                        !shape.is_unsigned);
                    auto converted_imag = floating::to_integer(
                        constant->complex_value.imag, shape.bit_width,
                        !shape.is_unsigned);
                    if (converted_real && converted_imag) {
                        real = ConstIntValue::from_bits128(
                            *converted_real, shape.bit_width,
                            shape.is_unsigned);
                        imag = ConstIntValue::from_bits128(
                            *converted_imag, shape.bit_width,
                            shape.is_unsigned);
                    }
                }
            } else {
                real = convert_component(*constant);
                imag = ConstIntValue::from_unsigned(0, shape.bit_width)
                    .cast(shape.bit_width, shape.is_unsigned);
            }
            if (!real || !imag) {
                report_error(
                    "integer complex initializer cannot be represented", loc);
                return false;
            }
            write_integer_bytes(file_, bytes, offset, *element_size,
                                static_cast<uint64_t>(
                                    real->to_unsigned_u128()));
            write_integer_bytes(file_, bytes, offset + *element_size,
                                *element_size, static_cast<uint64_t>(
                                    imag->to_unsigned_u128()));
            return true;
        }
        cir::FloatingSemantics semantics =
            floating::semantics_for_type(file_, element_type);
        cir::FloatingValue real;
        cir::FloatingValue imag;
        if (constant->kind == ConstValueKind::Complex) {
            floating::FloatResult converted_real;
            floating::FloatResult converted_imag;
            if (constant->complex_value.has_integer_components) {
                const ConstIntValue& source_real =
                    constant->complex_value.integer_real;
                const ConstIntValue& source_imag =
                    constant->complex_value.integer_imag;
                converted_real = floating::from_integer(
                    source_real.to_unsigned_u128(), source_real.bit_width,
                    !source_real.is_unsigned, semantics);
                converted_imag = floating::from_integer(
                    source_imag.to_unsigned_u128(), source_imag.bit_width,
                    !source_imag.is_unsigned, semantics);
            } else {
                converted_real = floating::convert(
                    constant->complex_value.real, semantics);
                converted_imag = floating::convert(
                    constant->complex_value.imag, semantics);
            }
            if (!converted_real || !converted_imag) {
                report_error("complex global initializer has invalid components", loc);
                return false;
            }
            real = *converted_real;
            imag = *converted_imag;
        } else if (constant->kind == ConstValueKind::Floating) {
            auto converted =
                floating::convert(constant->float_value.value, semantics);
            if (!converted) {
                report_error("complex global initializer cannot be represented", loc);
                return false;
            }
            real = *converted;
            imag = floating::zero(semantics);
        } else if (constant->kind == ConstValueKind::Integer) {
            auto converted = floating::from_integer(
                constant->int_value.to_unsigned_u128(),
                constant->int_value.bit_width,
                !constant->int_value.is_unsigned,
                semantics);
            if (!converted) {
                report_error("complex global initializer cannot be represented", loc);
                return false;
            }
            real = *converted;
            imag = floating::zero(semantics);
        } else {
            report_error("complex global initializer is not constant", loc);
            return false;
        }
        abi::write_scalar_bits(bytes.data() + offset,
                                   *element_size,
                                   real.low_bits,
                                   real.high_bits,
                                   file_.target_info().endianness);
        abi::write_scalar_bits(bytes.data() + offset + *element_size,
                                   *element_size,
                                   imag.low_bits,
                                   imag.high_bits,
                                   file_.target_info().endianness);
        return true;
    }

    if (kind == cir::TypeKind::BitInt) {
        std::optional<ConstValue> constant = eval_const_value();
        if (constant.has_value() && constant->kind == ConstValueKind::Integer) {
            write_const_int(constant->int_value);
            return true;
        }
        if (constant.has_value() && constant->kind == ConstValueKind::Boolean) {
            write_integer_bytes(file_, bytes, offset, *size, constant->bool_value ? 1 : 0);
            return true;
        }
        report_initializer_error("global initializer is not constant");
        return false;
    }

    if (kind != cir::TypeKind::Builtin) {
        report_error("unsupported global initializer target type", loc);
        return false;
    }

    const auto* builtin = std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(type));
    if (!builtin) {
        return false;
    }
    std::optional<ConstValue> constant = eval_const_value();
    if (!constant.has_value()) {

        if (std::optional<cir::StaticInitializerRelocation> diff =
                label_difference_relocation(value)) {
            if (!relocations) {
                report_error("static initializer relocation has no destination image", loc);
                return false;
            }
            relocations->push_back(*diff);
            write_integer_bytes(file_, bytes, offset, *size, 0);
            return true;
        }
        report_initializer_error("global initializer is not constant");
        return false;
    }
    switch (builtin->kind) {
        case cir::BuiltinTypeKind::NullPtr:
            if (constant->kind == ConstValueKind::Null &&
                constant->null_kind == ConstNullKind::Nullptr) {
                write_integer_bytes(file_, bytes, offset, *size, 0);
                return true;
            }
            if (constant->kind == ConstValueKind::Integer &&
                constant->int_value.is_zero()) {
                write_integer_bytes(file_, bytes, offset, *size, 0);
                return true;
            }
            report_error("nullptr_t global initializer is not constant", loc);
            return false;
        case cir::BuiltinTypeKind::Float:
        case cir::BuiltinTypeKind::Double:
        case cir::BuiltinTypeKind::LongDouble: {
            cir::FloatingSemantics semantics =
                floating::semantics_for_type(file_, type);
            floating::FloatResult fp;
            if (constant->kind == ConstValueKind::Floating) {
                fp = floating::convert(constant->float_value.value, semantics);
            } else if (constant->kind == ConstValueKind::Integer) {
                fp = floating::from_integer(
                    constant->int_value.to_unsigned_u128(),
                    constant->int_value.bit_width,
                    !constant->int_value.is_unsigned,
                    semantics);
            } else if (constant->kind == ConstValueKind::Boolean) {
                fp = floating::from_integer(
                    constant->bool_value ? 1 : 0, 1, false, semantics);
            } else {
                report_error("floating-point global initializer is not constant", loc);
                return false;
            }
            if (!fp || *size > 16 || offset + *size > bytes.size()) {
                report_error("floating-point global initializer cannot be represented", loc);
                return false;
            }
            abi::write_scalar_bits(bytes.data() + offset,
                                   *size,
                                   fp->low_bits,
                                   fp->high_bits,
                                   file_.target_info().endianness);
            return true;
        }
        case cir::BuiltinTypeKind::Float16: {
            report_error("_Float16 global initializer is not supported", loc);
            return false;
        }
        case cir::BuiltinTypeKind::Void:
        case cir::BuiltinTypeKind::Other:
            report_error("unsupported global initializer target type", loc);
            return false;
        default:
            break;
    }

    if (constant->kind == ConstValueKind::Integer) {
        write_const_int(constant->int_value);
        return true;
    }
    if (constant->kind == ConstValueKind::Boolean) {
        write_integer_bytes(file_, bytes, offset, *size, constant->bool_value ? 1 : 0);
        return true;
    }
    if (constant->kind == ConstValueKind::Floating) {
        cir::IntegerTypeShape shape =
            cir::integer_shape_for_type(file_, type);
        auto converted = floating::to_integer(
            constant->float_value.value,
            shape.bit_width,
            !shape.is_unsigned);
        if (!converted) {
            report_initializer_error(
                "floating initializer is not representable as an integer");
            return false;
        }
        ConstIntValue int_value = ConstIntValue::from_bits128(
            *converted, shape.bit_width, shape.is_unsigned);
        write_const_int(int_value);
        return true;
    }

    if (constant->kind == ConstValueKind::Address &&
        !constant->address_value.entity.valid() &&
        !constant->address_value.string_literal.valid() &&
        constant->address_value.allocation_id == 0) {
        write_integer_bytes(
            file_, bytes, offset, *size,
            static_cast<uint64_t>(constant->address_value.byte_offset));
        return true;
    }

    if (constant->kind == ConstValueKind::Address && relocations &&
        *size >= static_cast<size_t>(
                     std::max(1, (file_.target_info().pointer_width + 7) / 8))) {
        cir::StaticInitializerRelocation relocation;
        relocation.offset = offset;
        relocation.addend = constant->address_value.byte_offset;
        if (constant->address_value.entity.valid()) {
            cir::StorageDuration duration =
                file_.entity(constant->address_value.entity).storage_duration;
            if (duration == cir::StorageDuration::Automatic ||
                duration == cir::StorageDuration::Parameter) {
                report_error("address of an automatic object is not a constant expression",
                             loc);
                return false;
            }
            relocation.entity = constant->address_value.entity;
        } else if (constant->address_value.string_literal.valid()) {
            relocation.entity =
                string_literal_entity(constant->address_value.string_literal, loc);
        }
        if (relocation.entity.valid()) {
            relocations->push_back(relocation);
            write_integer_bytes(file_, bytes, offset, *size, 0);
            return true;
        }
    }
    report_initializer_error("global initializer is not constant");
    return false;
}

bool Session::write_static_path(std::vector<uint8_t>& bytes,
                                cir::TypeId base_type,
                                const std::vector<size_t>& path,
                                const ExprResult& value,
                                SrcLoc loc,
                                std::vector<cir::StaticInitializerRelocation>* relocations) {
    cir::TypeId type = file_.resolved_type(base_type);
    size_t offset = 0;
    for (size_t path_index = 0; path_index < path.size(); ++path_index) {
        size_t index = path[path_index];
        if (!file_.valid(type)) {
            report_error("static initializer path has invalid type", loc);
            return false;
        }
        const cir::Type& resolved = file_.type(type);
        if (resolved.kind == cir::TypeKind::Array) {
            cir::TypeId element_type = array_element_type(file_, type);
            std::optional<size_t> element_size = size_of_type(element_type, loc);
            std::optional<size_t> known_size = array_size(file_, type);
            if (!element_size.has_value()) {
                return false;
            }
            if (known_size.has_value() && index >= *known_size) {
                report_error("array initializer index is out of bounds", loc);
                return false;
            }
            offset += index * *element_size;
            type = file_.resolved_type(element_type);
            continue;
        }

        if (resolved.kind == cir::TypeKind::Record) {
            const cir::RecordFacts* facts = file_.record_facts_for_type(type);
            if (!facts || index >= facts->fields.size()) {
                report_error("static initializer path references an invalid record field", loc);
                return false;
            }
            const cir::RecordFieldFact& field = facts->fields[index];
            if (field.is_bitfield) {
                if (path_index + 1 != path.size()) {
                    report_error("static initializer path reaches inside a bit-field", loc);
                    return false;
                }
                int64_t int_value = 0;
                if (!eval_integer_constant(value, int_value, loc)) {
                    report_error("bit-field initializer is not constant", loc);
                    return false;
                }
                uint32_t storage_bits = field.storage_size == 0 ? 32 : field.storage_size;
                uint32_t width = cir::bitfield_value_width(file_, field);
                if (width == 0 || width > storage_bits || storage_bits > 64) {
                    return true;
                }
                size_t storage_offset = offset + field.offset;
                size_t storage_bytes = (storage_bits + 7) / 8;
                if (storage_offset + storage_bytes > bytes.size()) {
                    report_error("static initializer writes outside object bounds", loc);
                    return false;
                }

                EndiannessKind order = file_.target_info().endianness;
                uint64_t storage = abi::read_scalar_bits(
                    bytes.data() + storage_offset, storage_bytes, order).low;
                uint64_t value_mask = width == 64
                    ? std::numeric_limits<uint64_t>::max()
                    : ((uint64_t{1} << width) - 1);
                uint64_t field_mask = value_mask << field.bit_offset;
                storage &= ~field_mask;
                storage |= (static_cast<uint64_t>(int_value) & value_mask)
                           << field.bit_offset;
                abi::write_scalar_bits(bytes.data() + storage_offset,
                                       storage_bytes, storage, 0, order);
                return true;
            }
            offset += field.offset;
            type = file_.resolved_type(field.type.type);
            continue;
        }

        if (resolved.kind == cir::TypeKind::Vector) {
            cir::TypeId element_type = vector_element_type(file_, type);
            std::optional<size_t> element_size = size_of_type(element_type, loc);
            uint32_t known_size = file_.vector_element_count(type);
            if (!element_size.has_value()) {
                return false;
            }
            if (known_size != 0 && index >= known_size) {
                report_error("vector initializer index is out of bounds", loc);
                return false;
            }
            offset += index * *element_size;
            type = file_.resolved_type(element_type);
            continue;
        }

        report_error("static initializer path reaches a non-aggregate type", loc);
        return false;
    }
    return write_static_value(bytes, offset, type, value, loc, relocations);
}

} // namespace aburi::collect
