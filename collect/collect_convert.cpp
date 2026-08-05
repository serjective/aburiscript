#include "collect.h"
#include "collect_template_state.h"

#include "../cir/layout.h"
#include "../numeric_utils.h"

#include <algorithm>
#include <limits>
#include <string>
#include <string_view>
#include <variant>

namespace aburi::collect {

namespace {

cir::BuiltinTypeKind builtin_kind_for_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::Builtin) {
        return cir::BuiltinTypeKind::Other;
    }
    const auto* builtin = std::get_if<cir::BuiltinTypePayload>(&file.type_payload(type));
    return builtin ? builtin->kind : cir::BuiltinTypeKind::Other;
}

const cir::BitIntTypePayload* bit_int_payload(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::BitInt) {
        return nullptr;
    }
    return std::get_if<cir::BitIntTypePayload>(&file.type_payload(type));
}

int integer_rank(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Bool:
            return 1;
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
            return 2;
        case cir::BuiltinTypeKind::Short:
        case cir::BuiltinTypeKind::UShort:
        case cir::BuiltinTypeKind::WChar:
        case cir::BuiltinTypeKind::Char16:
            return 3;
        case cir::BuiltinTypeKind::Int:
        case cir::BuiltinTypeKind::UInt:
        case cir::BuiltinTypeKind::Char32:
            return 4;
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::ULong:
        case cir::BuiltinTypeKind::USize:
            return 5;
        case cir::BuiltinTypeKind::LongLong:
        case cir::BuiltinTypeKind::ULongLong:
            return 6;
        case cir::BuiltinTypeKind::Int128:
        case cir::BuiltinTypeKind::UInt128:
            return 7;
        default:
            return 0;
    }
}

int floating_rank(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Float16:
            return 1;
        case cir::BuiltinTypeKind::Float:
            return 2;
        case cir::BuiltinTypeKind::Double:
            return 3;
        case cir::BuiltinTypeKind::LongDouble:
            return 4;
        default:
            return 0;
    }
}

cir::TypeId floating_type_for_rank(cir::File& file, int rank) {
    if (rank >= 4) {
        return file.builtin_type(cir::BuiltinTypeKind::LongDouble);
    }
    if (rank == 2) {
        return file.builtin_type(cir::BuiltinTypeKind::Float);
    }
    if (rank == 1) {
        return file.builtin_type(cir::BuiltinTypeKind::Float16);
    }
    return file.builtin_type(cir::BuiltinTypeKind::Double);
}

bool is_signed_integer_domain(cir::OperatorValueDomain domain) {
    return domain == cir::OperatorValueDomain::SignedInteger ||
           domain == cir::OperatorValueDomain::Bool;
}

bool is_unsigned_integer_domain(cir::OperatorValueDomain domain) {
    return domain == cir::OperatorValueDomain::UnsignedInteger;
}

uint64_t max_signed_for_bits(uint16_t bits) {
    if (bits == 0) {
        return 0;
    }
    if (bits >= 64) {
        return static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
    }
    return (uint64_t{1} << (bits - 1)) - 1;
}

uint64_t max_unsigned_for_bits(uint16_t bits) {
    if (bits >= 64) {
        return std::numeric_limits<uint64_t>::max();
    }
    return (uint64_t{1} << bits) - 1;
}

const cir::FunctionTypePayload* function_payload(const cir::File& file,
                                                 cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Function) {
        return nullptr;
    }
    return std::get_if<cir::FunctionTypePayload>(&file.type_payload(resolved));
}

bool type_ref_matches_address_target(const cir::File& file,
                                     cir::TypeRef lhs,
                                     cir::TypeRef rhs) {
    lhs.type = file.resolved_type(lhs.type);
    rhs.type = file.resolved_type(rhs.type);
    return lhs.type == rhs.type &&
           lhs.qualifiers == rhs.qualifiers &&
           lhs.memory_space == rhs.memory_space;
}

bool function_exception_spec_matches_address_target(
    cir::FunctionExceptionSpecKind function,
    cir::FunctionExceptionSpecKind target) {
    return function == target ||
           (function == cir::FunctionExceptionSpecKind::NonThrowing &&
            target == cir::FunctionExceptionSpecKind::PotentiallyThrowing);
}

bool function_type_matches_address_target(const cir::File& file,
                                          cir::TypeId function_type,
                                          cir::TypeId target_function_type) {
    const cir::FunctionTypePayload* function =
        function_payload(file, function_type);
    const cir::FunctionTypePayload* target =
        function_payload(file, target_function_type);
    if (!function || !target ||
        function->parameters.size() != target->parameters.size() ||
        function->is_variadic != target->is_variadic ||
        function->has_prototype != target->has_prototype ||
        function->member_ref_qualifier != target->member_ref_qualifier ||
        function->member_is_const != target->member_is_const ||
        function->member_is_volatile != target->member_is_volatile ||
        !function_exception_spec_matches_address_target(
            function->exception_spec.kind, target->exception_spec.kind) ||
        function->calling_convention != target->calling_convention ||
        !type_ref_matches_address_target(file,
                                         function->return_type,
                                         target->return_type)) {
        return false;
    }
    for (size_t i = 0; i < function->parameters.size(); ++i) {

        cir::TypeRef function_parameter = function->parameters[i];
        cir::TypeRef target_parameter = target->parameters[i];
        function_parameter.qualifiers = cir::QualNone;
        target_parameter.qualifiers = cir::QualNone;
        if (!type_ref_matches_address_target(file,
                                             function_parameter,
                                             target_parameter)) {
            return false;
        }
    }
    return true;
}

bool integer_literal_fits(const cir::File& file,
                          cir::BuiltinTypeKind kind,
                          uint64_t value) {
    cir::TypeId type = const_cast<cir::File&>(file).builtin_type(kind);
    cir::IntegerTypeShape shape = cir::integer_shape_for_type(file, type);
    if (shape.bit_width == 0) {
        return false;
    }
    if (shape.is_unsigned) {
        return value <= max_unsigned_for_bits(shape.bit_width);
    }
    return value <= max_signed_for_bits(shape.bit_width);
}

cir::TypeId first_fitting_integer_literal_type(
    cir::File& file,
    uint64_t value,
    std::initializer_list<cir::BuiltinTypeKind> candidates) {
    for (cir::BuiltinTypeKind candidate : candidates) {
        if (integer_literal_fits(file, candidate, value)) {
            return file.builtin_type(candidate);
        }
    }
    return {};
}

int long_suffix_count_from_token(TokenType token_type) {
    switch (token_type) {
        case TokenType::LONG_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
            return 1;
        case TokenType::LONG_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
            return 2;
        default:
            return 0;
    }
}

bool unsigned_suffix_from_token(TokenType token_type) {
    switch (token_type) {
        case TokenType::UNSIGNED_INTEGER_CONST:
        case TokenType::UNSIGNED_LONG_CONST:
        case TokenType::UNSIGNED_LONG_LONG_CONST:
        case TokenType::UNSIGNED_BITINT_CONST:
            return true;
        default:
            return false;
    }
}

bool bitint_suffix_from_token(TokenType token_type) {
    return token_type == TokenType::BITINT_CONST ||
           token_type == TokenType::UNSIGNED_BITINT_CONST;
}

bool is_member_pointer_type(const cir::File& file, cir::TypeId type) {
    type = file.resolved_type(type);
    return file.valid(type) && file.type(type).kind == cir::TypeKind::MemberPointer;
}

const cir::MemberPointerTypePayload* member_pointer_payload(
    const cir::File& file,
    cir::TypeId type) {
    type = file.resolved_type(type);
    if (!file.valid(type) || file.type(type).kind != cir::TypeKind::MemberPointer) {
        return nullptr;
    }
    return std::get_if<cir::MemberPointerTypePayload>(&file.type_payload(type));
}

} // namespace

cir::TypeId Session::integer_literal_type(TokenType token_type,
                                          std::string_view spelling,
                                          uint64_t value) {
    bool has_unsigned = unsigned_suffix_from_token(token_type);
    int long_count = long_suffix_count_from_token(token_type);
    bool has_bitint = bitint_suffix_from_token(token_type);
    bool is_decimal = true;
    if (auto parsed = parse_integer_literal_info(spelling)) {
        has_unsigned = has_unsigned || parsed->has_unsigned_suffix;
        long_count = std::max(long_count, parsed->long_suffix_count);
        has_bitint = has_bitint || parsed->has_bitint_suffix;
        is_decimal = parsed->is_decimal();
    }

    if (has_bitint) {

        uint16_t value_bits = 0;
        for (uint64_t probe = value; probe != 0; probe >>= 1) {
            ++value_bits;
        }
        if (has_unsigned) {
            return file_.bit_int_type(std::max<uint16_t>(1, value_bits), true);
        }
        return file_.bit_int_type(std::max<uint16_t>(2, value_bits + 1), false);
    }

    if (has_unsigned) {
        if (long_count >= 2) {
            return file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
        }
        if (long_count == 1) {
            return file_.builtin_type(cir::BuiltinTypeKind::ULong);
        }
        cir::TypeId type = first_fitting_integer_literal_type(
            file_,
            value,
            {cir::BuiltinTypeKind::UInt,
             cir::BuiltinTypeKind::ULong,
             cir::BuiltinTypeKind::ULongLong});
        return type.valid() ? type : file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
    }

    if (long_count >= 2) {
        cir::TypeId type = first_fitting_integer_literal_type(
            file_,
            value,
            is_decimal
                ? std::initializer_list<cir::BuiltinTypeKind>{
                      cir::BuiltinTypeKind::LongLong}
                : std::initializer_list<cir::BuiltinTypeKind>{
                      cir::BuiltinTypeKind::LongLong,
                      cir::BuiltinTypeKind::ULongLong});
        return type.valid() ? type : file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
    }

    if (long_count == 1) {
        cir::TypeId type = first_fitting_integer_literal_type(
            file_,
            value,
            is_decimal
                ? std::initializer_list<cir::BuiltinTypeKind>{
                      cir::BuiltinTypeKind::Long,
                      cir::BuiltinTypeKind::LongLong}
                : std::initializer_list<cir::BuiltinTypeKind>{
                      cir::BuiltinTypeKind::Long,
                      cir::BuiltinTypeKind::ULong,
                      cir::BuiltinTypeKind::LongLong,
                      cir::BuiltinTypeKind::ULongLong});
        return type.valid() ? type : file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
    }

    cir::TypeId type = first_fitting_integer_literal_type(
        file_,
        value,
        is_decimal
            ? std::initializer_list<cir::BuiltinTypeKind>{
                  cir::BuiltinTypeKind::Int,
                  cir::BuiltinTypeKind::Long,
                  cir::BuiltinTypeKind::LongLong}
            : std::initializer_list<cir::BuiltinTypeKind>{
                  cir::BuiltinTypeKind::Int,
                  cir::BuiltinTypeKind::UInt,
                  cir::BuiltinTypeKind::Long,
                  cir::BuiltinTypeKind::ULong,
                  cir::BuiltinTypeKind::LongLong,
                  cir::BuiltinTypeKind::ULongLong});
    return type.valid() ? type : file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
}

bool Session::is_bool_type(cir::TypeId type) const {
    return builtin_kind_for_type(file_, type) == cir::BuiltinTypeKind::Bool;
}

bool Session::is_nullptr_type(cir::TypeId type) const {
    return builtin_kind_for_type(file_, type) == cir::BuiltinTypeKind::NullPtr;
}

bool Session::is_integer_type(cir::TypeId type) const {
    if (lang_opts_.is_cxx_mode() && is_scoped_enum_type(type)) {
        return false;
    }
    return cir::is_integer_like_type(file_, type);
}

bool Session::is_scoped_enum_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type) || file_.type(type).kind != cir::TypeKind::Enum) {
        return false;
    }
    const auto* payload =
        std::get_if<cir::EnumTypePayload>(&file_.type_payload(type));
    return payload && payload->is_scoped;
}

bool Session::is_floating_type(cir::TypeId type) const {
    return cir::is_floating_type(file_, type);
}

bool Session::is_complex_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    return file_.valid(type) && file_.type(type).kind == cir::TypeKind::Complex;
}

bool Session::is_arithmetic_type(cir::TypeId type) const {
    return is_integer_type(type) || is_floating_type(type) || is_complex_type(type);
}

bool Session::is_pointer_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    return file_.valid(type) &&
           (file_.type(type).kind == cir::TypeKind::Pointer ||
            file_.type(type).kind == cir::TypeKind::BlockPointer);
}

bool Session::is_vector_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    return file_.valid(type) && file_.type(type).kind == cir::TypeKind::Vector;
}

bool Session::is_scalar_type(cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    bool member_pointer = lang_opts_.is_cxx_mode() && file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::MemberPointer;
    return is_arithmetic_type(type) || is_pointer_type(type) ||
        member_pointer;
}

bool Session::type_equal(cir::TypeId lhs, cir::TypeId rhs) const {
    lhs = file_.resolved_type(lhs);
    rhs = file_.resolved_type(rhs);
    return lhs.valid() && rhs.valid() && lhs == rhs;
}

namespace {

cir::TypeRef resolve_for_compatibility(const cir::File& file, cir::TypeRef ref) {
    uint8_t qualifiers = ref.qualifiers;
    cir::TypeId id = ref.type;
    while (file.valid(id) && file.type(id).kind == cir::TypeKind::Typedef) {
        const auto& payload =
            std::get<cir::TypedefTypePayload>(file.type_payload(id));
        qualifiers |= payload.underlying_type.qualifiers;
        id = payload.underlying_type.type;
    }
    return cir::TypeRef{file.resolved_type(id), qualifiers, ref.memory_space};
}

bool same_type_identity_impl(const cir::File& file,
                             cir::TypeRef lhs,
                             cir::TypeRef rhs) {
    lhs = resolve_for_compatibility(file, lhs);
    rhs = resolve_for_compatibility(file, rhs);
    if (!file.valid(lhs.type) || !file.valid(rhs.type) ||
        lhs.memory_space != rhs.memory_space) {
        return false;
    }

    bool lhs_array = file.type(lhs.type).kind == cir::TypeKind::Array;
    bool rhs_array = file.type(rhs.type).kind == cir::TypeKind::Array;
    if (!lhs_array || !rhs_array) {
        return lhs.type == rhs.type && lhs.qualifiers == rhs.qualifiers;
    }

    constexpr uint8_t cv_mask = cir::QualConst | cir::QualVolatile;
    if ((lhs.qualifiers & ~cv_mask) != (rhs.qualifiers & ~cv_mask)) {
        return false;
    }
    const auto& lhs_payload =
        std::get<cir::ArrayTypePayload>(file.type_payload(lhs.type));
    const auto& rhs_payload =
        std::get<cir::ArrayTypePayload>(file.type_payload(rhs.type));
    if (lhs_payload.size_kind != rhs_payload.size_kind) {
        return false;
    }
    if (lhs_payload.size_kind == cir::ArraySizeKind::Constant &&
        lhs_payload.size != rhs_payload.size) {
        return false;
    }
    if ((lhs_payload.size_kind == cir::ArraySizeKind::Variable ||
         lhs_payload.size_expr_is_dependent ||
         rhs_payload.size_expr_is_dependent) &&
        lhs.type != rhs.type) {
        return false;
    }

    cir::TypeRef lhs_element = lhs_payload.element_type;
    cir::TypeRef rhs_element = rhs_payload.element_type;
    lhs_element.qualifiers = static_cast<uint8_t>(
        lhs_element.qualifiers | (lhs.qualifiers & cv_mask));
    rhs_element.qualifiers = static_cast<uint8_t>(
        rhs_element.qualifiers | (rhs.qualifiers & cv_mask));
    return same_type_identity_impl(file, lhs_element, rhs_element);
}

} // namespace

bool Session::same_type_identity(cir::TypeRef lhs, cir::TypeRef rhs) const {
    return same_type_identity_impl(file_, lhs, rhs);
}

bool Session::types_compatible(cir::TypeRef lhs, cir::TypeRef rhs,
                               bool ignore_top_qualifiers) const {
    lhs = resolve_for_compatibility(file_, lhs);
    rhs = resolve_for_compatibility(file_, rhs);
    if (!file_.valid(lhs.type) || !file_.valid(rhs.type)) {
        return false;
    }
    if (!ignore_top_qualifiers && lhs.qualifiers != rhs.qualifiers) {
        return false;
    }
    if (lhs.type == rhs.type) {
        return true;
    }

    const cir::Type& lhs_type = file_.type(lhs.type);
    const cir::Type& rhs_type = file_.type(rhs.type);

    if (lhs_type.kind == cir::TypeKind::Enum ||
        rhs_type.kind == cir::TypeKind::Enum) {
        if (lhs_type.kind == rhs_type.kind) {

            const auto* lp =
                std::get_if<cir::EnumTypePayload>(&file_.type_payload(lhs.type));
            const auto* rp =
                std::get_if<cir::EnumTypePayload>(&file_.type_payload(rhs.type));
            if (lp && rp && lp->entity.valid() && lp->entity == rp->entity) {
                return true;
            }
            return false;
        }
        if (lang_opts_.is_cxx_mode()) {
            return false;
        }
        cir::TypeId enum_id =
            lhs_type.kind == cir::TypeKind::Enum ? lhs.type : rhs.type;
        cir::TypeId other =
            lhs_type.kind == cir::TypeKind::Enum ? rhs.type : lhs.type;
        const auto* payload =
            std::get_if<cir::EnumTypePayload>(&file_.type_payload(enum_id));
        cir::TypeId underlying = payload && payload->underlying_type.valid()
            ? file_.resolved_type(payload->underlying_type.type)
            : const_cast<Session*>(this)->builder_.int_type();
        return type_equal(underlying, other);
    }

    if (lhs_type.kind != rhs_type.kind) {
        return false;
    }

    switch (lhs_type.kind) {
        case cir::TypeKind::Pointer: {
            const auto& lp =
                std::get<cir::PointerTypePayload>(file_.type_payload(lhs.type));
            const auto& rp =
                std::get<cir::PointerTypePayload>(file_.type_payload(rhs.type));
            return types_compatible(lp.pointee, rp.pointee);
        }
        case cir::TypeKind::Array: {
            const auto& la =
                std::get<cir::ArrayTypePayload>(file_.type_payload(lhs.type));
            const auto& ra =
                std::get<cir::ArrayTypePayload>(file_.type_payload(rhs.type));

            if (!types_compatible(la.element_type, ra.element_type,
                                  ignore_top_qualifiers)) {
                return false;
            }
            if (la.size_kind == cir::ArraySizeKind::Constant &&
                ra.size_kind == cir::ArraySizeKind::Constant) {
                return la.size == ra.size;
            }
            return true;
        }
        case cir::TypeKind::Function: {
            const auto& lf =
                std::get<cir::FunctionTypePayload>(file_.type_payload(lhs.type));
            const auto& rf =
                std::get<cir::FunctionTypePayload>(file_.type_payload(rhs.type));
            if (!types_compatible(lf.return_type, rf.return_type)) {
                return false;
            }
            if (!lf.has_prototype || !rf.has_prototype) {
                return true;
            }
            if (lf.is_variadic != rf.is_variadic ||
                lf.parameters.size() != rf.parameters.size()) {
                return false;
            }
            for (size_t i = 0; i < lf.parameters.size(); ++i) {

                cir::TypeRef l = lf.parameters[i];
                cir::TypeRef r = rf.parameters[i];
                l.qualifiers = cir::QualNone;
                r.qualifiers = cir::QualNone;
                if (!types_compatible(l, r) &&
                    !transparent_union_accepts(l, r) &&
                    !transparent_union_accepts(r, l)) {
                    return false;
                }
            }
            return true;
        }
        default:

            return false;
    }
}

bool Session::transparent_union_accepts(cir::TypeRef union_ref,
                                        cir::TypeRef other) const {
    cir::TypeId union_type = file_.resolved_type(union_ref.type);
    if (!file_.valid(union_type) ||
        file_.type(union_type).kind != cir::TypeKind::Record) {
        return false;
    }
    const cir::RecordFacts* facts = file_.record_facts_for_type(union_type);
    if (!facts || !facts->is_transparent_union) {
        return false;
    }
    other.qualifiers = cir::QualNone;
    for (const cir::RecordFieldFact& field : facts->fields) {
        cir::TypeRef member = field.type;
        member.qualifiers = cir::QualNone;
        if (types_compatible(member, other)) {
            return true;
        }
    }
    return false;
}

ExprResult Session::wrap_in_transparent_union(ExprResult member_value,
                                              cir::TypeId union_type,
                                              const cir::RecordFieldFact& field,
                                              SrcLoc loc) {
    std::string temp_name =
        ".transparent.union.tmp." + std::to_string(compound_literal_counter_++);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             union_type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.transparent.union");
    cir::InstId union_place = builder_.local_place(temp, union_type, loc);
    cir::InstId member_place =
        builder_.field_addr(union_place, field.entity, field.type.type, loc);
    builder_.store(member_place, member_value.value, loc);
    cir::InstId loaded = builder_.lvalue_to_rvalue(union_place, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(member_value.fragment), std::move(fragment), loc);
    result.value = loaded;
    result.type = union_type;
    result.category = ValueCategory::PrValue;
    return result;
}

cir::TypeId Session::unsigned_counterpart(cir::TypeId type) const {
    switch (builtin_kind_for_type(file_, type)) {
        case cir::BuiltinTypeKind::Bool:
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::UChar);
        case cir::BuiltinTypeKind::Char8:
            return type;
        case cir::BuiltinTypeKind::Short:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::UShort);
        case cir::BuiltinTypeKind::Int:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::UInt);
        case cir::BuiltinTypeKind::Long:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::ULong);
        case cir::BuiltinTypeKind::LongLong:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::ULongLong);
        case cir::BuiltinTypeKind::Int128:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::UInt128);
        case cir::BuiltinTypeKind::WChar:
        case cir::BuiltinTypeKind::Char32:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::UInt);
        case cir::BuiltinTypeKind::Char16:
            return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::UShort);
        default: {
            if (const cir::BitIntTypePayload* bit_int = bit_int_payload(file_, type)) {
                return const_cast<Session*>(this)->file_.bit_int_type(bit_int->bits, true);
            }
            return file_.resolved_type(type);
        }
    }
}

cir::TypeId Session::integer_promotion_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type) || !is_integer_type(type)) {
        return type;
    }

    if (file_.type(type).kind == cir::TypeKind::Enum) {
        const auto* enum_payload = std::get_if<cir::EnumTypePayload>(&file_.type_payload(type));
        if (enum_payload && enum_payload->underlying_type.valid()) {
            type = file_.resolved_type(enum_payload->underlying_type.type);
        } else {
            return const_cast<Session*>(this)->builder_.int_type();
        }
    }

    cir::BuiltinTypeKind kind = builtin_kind_for_type(file_, type);
    Session* self = const_cast<Session*>(this);
    auto can_represent_all_values =
        [&](cir::TypeId candidate, cir::TypeId source) {
            cir::IntegerTypeShape candidate_shape =
                cir::integer_shape_for_type(file_, candidate);
            cir::IntegerTypeShape source_shape =
                cir::integer_shape_for_type(file_, source);
            if (source_shape.is_unsigned) {
                return candidate_shape.is_unsigned
                    ? candidate_shape.bit_width >= source_shape.bit_width
                    : candidate_shape.bit_width > source_shape.bit_width;
            }
            return !candidate_shape.is_unsigned &&
                   candidate_shape.bit_width >= source_shape.bit_width;
        };

    if (kind == cir::BuiltinTypeKind::Char8 ||
        kind == cir::BuiltinTypeKind::Char16 ||
        kind == cir::BuiltinTypeKind::Char32 ||
        kind == cir::BuiltinTypeKind::WChar) {
        constexpr cir::BuiltinTypeKind candidates[] = {
            cir::BuiltinTypeKind::Int,
            cir::BuiltinTypeKind::UInt,
            cir::BuiltinTypeKind::Long,
            cir::BuiltinTypeKind::ULong,
            cir::BuiltinTypeKind::LongLong,
            cir::BuiltinTypeKind::ULongLong,
        };
        for (cir::BuiltinTypeKind candidate_kind : candidates) {
            cir::TypeId candidate = self->file_.builtin_type(candidate_kind);
            if (can_represent_all_values(candidate, type)) {
                return candidate;
            }
        }

        return type;
    }

    int rank = integer_rank(kind);
    int int_rank = integer_rank(cir::BuiltinTypeKind::Int);
    if (rank > 0 && rank < int_rank) {
        cir::TypeId int_type = self->builder_.int_type();
        return can_represent_all_values(int_type, type)
            ? int_type
            : self->file_.builtin_type(cir::BuiltinTypeKind::UInt);
    }
    return type;
}

cir::TypeId Session::bitfield_promoted_type(cir::TypeId declared_type,
                                            uint32_t bit_width) const {
    Session* self = const_cast<Session*>(this);
    cir::TypeId resolved = file_.resolved_type(declared_type);
    if (bit_width == 0 || !file_.valid(resolved) || !is_integer_type(resolved)) {
        return declared_type;
    }
    cir::IntegerTypeShape shape = cir::integer_shape_for_type(file_, resolved);
    cir::TypeId int_type = self->builder_.int_type();
    uint32_t int_bits = cir::integer_shape_for_type(file_, int_type).bit_width;
    if (!shape.is_unsigned) {

        return bit_width <= int_bits ? int_type : declared_type;
    }

    if (bit_width < int_bits) {
        return int_type;
    }
    if (bit_width == int_bits) {
        return self->file_.builtin_type(cir::BuiltinTypeKind::UInt);
    }
    return declared_type;
}

cir::TypeId Session::default_argument_promotion_type(cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type)) {
        return type;
    }
    if (builtin_kind_for_type(file_, type) == cir::BuiltinTypeKind::Float) {
        return const_cast<Session*>(this)->file_.builtin_type(cir::BuiltinTypeKind::Double);
    }
    if (is_integer_type(type)) {
        return integer_promotion_type(type);
    }
    return type;
}

cir::TypeId Session::usual_arithmetic_conversion_type(cir::TypeId lhs,
                                                      cir::TypeId rhs) const {
    lhs = file_.resolved_type(lhs);
    rhs = file_.resolved_type(rhs);
    if (!file_.valid(lhs) || !file_.valid(rhs)) {
        return lhs.valid() ? lhs : rhs;
    }
    if (!is_arithmetic_type(lhs) || !is_arithmetic_type(rhs)) {
        return {};
    }

    if (is_complex_type(lhs) || is_complex_type(rhs)) {

        Session* self = const_cast<Session*>(this);
        cir::TypeId lhs_element =
            is_complex_type(lhs) ? complex_element_type(lhs) : lhs;
        cir::TypeId rhs_element =
            is_complex_type(rhs) ? complex_element_type(rhs) : rhs;
        cir::TypeId element =
            usual_arithmetic_conversion_type(lhs_element, rhs_element);
        if (!element.valid()) {
            element = self->file_.builtin_type(cir::BuiltinTypeKind::Double);
        }
        return self->complex_type(self->file_.type_ref(element));
    }

    cir::BuiltinTypeKind lhs_builtin = builtin_kind_for_type(file_, lhs);
    cir::BuiltinTypeKind rhs_builtin = builtin_kind_for_type(file_, rhs);
    int lhs_float_rank = floating_rank(lhs_builtin);
    int rhs_float_rank = floating_rank(rhs_builtin);
    if (lhs_float_rank || rhs_float_rank) {
        return floating_type_for_rank(const_cast<Session*>(this)->file_,
                                      lhs_float_rank > rhs_float_rank
                                          ? lhs_float_rank
                                          : rhs_float_rank);
    }

    lhs = integer_promotion_type(lhs);
    rhs = integer_promotion_type(rhs);
    if (type_equal(lhs, rhs)) {
        return file_.resolved_type(lhs);
    }

    const cir::BitIntTypePayload* lhs_bit_int = bit_int_payload(file_, lhs);
    const cir::BitIntTypePayload* rhs_bit_int = bit_int_payload(file_, rhs);
    if (lhs_bit_int || rhs_bit_int) {

        cir::IntegerTypeShape lhs_bits = cir::integer_shape_for_type(file_, lhs);
        cir::IntegerTypeShape rhs_bits = cir::integer_shape_for_type(file_, rhs);
        bool lhs_higher = lhs_bits.bit_width != rhs_bits.bit_width
            ? lhs_bits.bit_width > rhs_bits.bit_width
            : lhs_bit_int == nullptr;
        cir::TypeId higher = lhs_higher ? lhs : rhs;
        cir::IntegerTypeShape higher_bits = lhs_higher ? lhs_bits : rhs_bits;
        cir::IntegerTypeShape lower_bits = lhs_higher ? rhs_bits : lhs_bits;
        if (higher_bits.is_unsigned == lower_bits.is_unsigned ||
            higher_bits.is_unsigned) {
            return file_.resolved_type(higher);
        }

        if (higher_bits.bit_width > lower_bits.bit_width) {
            return file_.resolved_type(higher);
        }
        return unsigned_counterpart(higher);
    }

    cir::OperatorValueDomain lhs_domain = file_.operator_value_domain(file_.type_ref(lhs));
    cir::OperatorValueDomain rhs_domain = file_.operator_value_domain(file_.type_ref(rhs));
    bool lhs_signed = is_signed_integer_domain(lhs_domain);
    bool rhs_signed = is_signed_integer_domain(rhs_domain);
    bool lhs_unsigned = is_unsigned_integer_domain(lhs_domain);
    bool rhs_unsigned = is_unsigned_integer_domain(rhs_domain);
    int lhs_rank = integer_rank(builtin_kind_for_type(file_, lhs));
    int rhs_rank = integer_rank(builtin_kind_for_type(file_, rhs));
    cir::IntegerTypeShape lhs_shape = cir::integer_shape_for_type(file_, lhs);
    cir::IntegerTypeShape rhs_shape = cir::integer_shape_for_type(file_, rhs);

    if (lhs_signed == rhs_signed) {
        return lhs_rank < rhs_rank ? rhs : lhs;
    }
    if (lhs_unsigned && lhs_rank >= rhs_rank) {
        return lhs;
    }
    if (rhs_unsigned && rhs_rank >= lhs_rank) {
        return rhs;
    }
    if (lhs_signed && lhs_shape.bit_width > rhs_shape.bit_width) {
        return lhs;
    }
    if (rhs_signed && rhs_shape.bit_width > lhs_shape.bit_width) {
        return rhs;
    }
    return lhs_signed ? unsigned_counterpart(lhs) : unsigned_counterpart(rhs);
}

ExprResult Session::cast_if_needed(ExprResult expr,
                                   cir::TypeId type,
                                   std::string_view cast_kind,
                                   SrcLoc loc) {
    if (!type.valid() || !expr.value.valid() || type_equal(expr.type, type)) {
        return expr;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.cast");
    cir::InstId cast = builder_.cast(type, expr.value, cast_kind, loc);
    cir::Fragment cast_fragment = finish_fragment_block(block, previous);
    expr.fragment = chain(std::move(expr.fragment), std::move(cast_fragment), loc);
    expr.value = cast;
    expr.type = type;
    expr.category = ValueCategory::PrValue;
    if (expr.template_value_expr.valid()) {
        cir::TemplateValueExprNode node;
        node.kind = cir::TemplateValueExprKind::Cast;
        node.lhs = expr.template_value_expr.root;
        node.type = type;
        node.result_type = file_.type_ref(type);
        expr.template_value_expr.nodes.push_back(node);
        expr.template_value_expr.root = static_cast<uint32_t>(
            expr.template_value_expr.nodes.size() - 1);
    }
    return expr;
}

ExprResult Session::convert_to_arithmetic_type(ExprResult expr,
                                               cir::TypeId type,
                                               SrcLoc loc) {
    if (!type.valid()) {
        return expr;
    }
    return cast_if_needed(std::move(expr), type, "arith", loc);
}

ExprResult Session::convert_to_condition(ExprResult expr, SrcLoc loc) {
    if (expr.has_error) {
        return expr;
    }
    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId source_type = file_.resolved_type(expr.type);
        if (file_.valid(source_type) &&
            file_.type(source_type).kind == cir::TypeKind::Record) {
            if (expr.category == ValueCategory::PrValue && expr.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(expr),
                                               /*is_arrow=*/false, loc);
                expr = std::move(materialized.base_place);
            }
            UserConversionSequence sequence =
                resolve_initialization_user_conversion(
                    expr, builder_.bool_type(),
                    UserConversionContext::ContextualBool, loc);
            if (sequence.kind == UserConversionSequence::Kind::Ambiguous) {
                report_error("contextual conversion to bool is ambiguous", loc);
                report_overload_ambiguity_notes(sequence.ambiguity, loc);
                expr.has_error = true;
                return expr;
            }
            if (sequence.kind ==
                UserConversionSequence::Kind::ConversionFunction) {
                return apply_user_conversion_sequence(
                    std::move(expr), builder_.bool_type(), sequence, loc);
            }
            report_error("condition requires a contextually convertible "
                         "expression of type bool", loc);
            expr.has_error = true;
            return expr;
        }
    }
    diagnose_if_not_scalar(expr.type, loc, "condition");
    if (is_nullptr_type(expr.type)) {
        return convert_nullptr_to_bool(std::move(expr),
                                       builder_.bool_type(),
                                       "condition",
                                       loc);
    }
    return cast_if_needed(std::move(expr), builder_.bool_type(), "condition", loc);
}

ExprResult Session::convert_nullptr_to_bool(ExprResult expr,
                                            cir::TypeId target_type,
                                            std::string_view reason,
                                            SrcLoc loc) {
    ExprResult converted = make_boolean_literal(false, "false", loc);
    converted.fragment =
        chain(std::move(expr.fragment), std::move(converted.fragment), loc);
    converted.has_error = expr.has_error || converted.has_error;
    return cast_if_needed(std::move(converted),
                          target_type.valid() ? target_type : builder_.bool_type(),
                          reason,
                          loc);
}

ExprResult Session::apply_default_argument_promotion(ExprResult expr, SrcLoc loc) {
    cir::TypeId promoted = default_argument_promotion_type(expr.type);
    if (!promoted.valid() || type_equal(expr.type, promoted)) {
        return expr;
    }
    return cast_if_needed(std::move(expr), promoted, "default-argument-promotion", loc);
}

bool Session::entity_is_function_template_specialization(
    cir::EntityId entity) const {
    if (!entity.valid() || !file_.valid(entity)) {
        return false;
    }
    const cir::TemplateSpecializationFact* fact =
        file_.template_specialization(entity);
    if (!fact || !fact->template_entity.valid() ||
        !fact->pattern_type.valid()) {
        return false;
    }
    const TemplateInfo* info = template_info(fact->template_entity);
    return info && !info->is_class_template && !info->is_alias_template &&
           !info->is_variable_template && !info->is_concept;
}

std::shared_ptr<const OverloadDesignator>
Session::canonical_overload_designator(const ExprResult& expression,
                                       bool address_of_written) const {
    if (expression.overload_designator) {
        if (!address_of_written ||
            expression.overload_designator->address_of_written) {
            return expression.overload_designator;
        }
        OverloadDesignator updated = *expression.overload_designator;
        updated.address_of_written = true;
        updated.address_operand_parenthesized =
            !expression.unparenthesized_id_or_member;
        return std::make_shared<const OverloadDesignator>(std::move(updated));
    }

    std::vector<cir::EntityId> entities = expression.candidates;
    if (entities.empty() && expression.entity.valid()) {
        entities.push_back(expression.entity);
    }
    if (entities.empty()) {
        return {};
    }

    OverloadDesignator designator;
    designator.member_candidate_object_paths =
        expression.member_candidate_object_paths;
    designator.qualified_member_owner = expression.qualified_member_owner;
    designator.lookup_generation = lookup_generation_;
    designator.qualified_name = expression.qualified_name;
    designator.address_of_written = address_of_written;
    designator.address_operand_parenthesized =
        address_of_written && !expression.unparenthesized_id_or_member;
    designator.has_explicit_template_arguments =
        expression.has_explicit_template_arguments;
    designator.explicit_template_arguments =
        expression.explicit_template_arguments;
    designator.candidate_explicit_template_arguments =
        expression.candidate_explicit_template_arguments;
    designator.candidates.reserve(entities.size());
    for (cir::EntityId entity : entities) {
        OverloadDesignatorCandidate candidate;
        candidate.entity = entity;
        if (expression.category == ValueCategory::MemberPointerDesignator) {
            candidate.address_category =
                OverloadAddressCategory::MemberPointer;
        } else if (entity.valid() && file_.valid(entity)) {
            const cir::RecordMethodFact* method = file_.method_fact(entity);
            if (method && !method->is_static) {
                candidate.address_category =
                    OverloadAddressCategory::MemberPointer;
            }
        }
        designator.candidates.push_back(candidate);
    }
    return std::make_shared<const OverloadDesignator>(std::move(designator));
}

void Session::apply_function_template_address_eliminations(
    std::vector<cir::EntityId>& selected) {
    if (selected.size() < 2) {
        return;
    }

    std::vector<cir::EntityId> non_templates;
    for (cir::EntityId candidate : selected) {
        if (!entity_is_function_template_specialization(candidate)) {
            non_templates.push_back(candidate);
        }
    }
    bool selected_non_templates = !non_templates.empty();
    if (selected_non_templates) {
        selected = std::move(non_templates);
    }

    std::vector<bool> constraint_eliminated(selected.size(), false);
    for (size_t i = 0; i < selected.size(); ++i) {
        const cir::RecordMethodFact* less = file_.method_fact(selected[i]);
        if (!less) {
            continue;
        }
        for (size_t j = 0; j < selected.size(); ++j) {
            if (i == j || constraint_eliminated[i]) {
                continue;
            }
            const cir::RecordMethodFact* more = file_.method_fact(selected[j]);
            bool constrained_over_unconstrained =
                more &&
                more->associated_constraint_fingerprint != 0 &&
                less->associated_constraint_fingerprint == 0 &&
                function_signatures_match(more->type.type,
                                          less->type.type);
            bool explicitly_subsumes =
                more && less->associated_constraint_fingerprint != 0 &&
                std::find(more->more_constrained_than.begin(),
                          more->more_constrained_than.end(),
                          less->associated_constraint_fingerprint) !=
                    more->more_constrained_than.end();
            if (constrained_over_unconstrained || explicitly_subsumes) {
                constraint_eliminated[i] = true;
            }
        }
    }
    if (std::find(constraint_eliminated.begin(),
                  constraint_eliminated.end(),
                  true) != constraint_eliminated.end()) {
        std::vector<cir::EntityId> kept;
        kept.reserve(selected.size());
        for (size_t i = 0; i < selected.size(); ++i) {
            if (!constraint_eliminated[i]) {
                kept.push_back(selected[i]);
            }
        }
        selected = std::move(kept);
    }
    if (selected_non_templates || selected.size() < 2) {
        return;
    }

    std::vector<bool> eliminated(selected.size(), false);
    for (size_t i = 0; i < selected.size(); ++i) {
        const cir::TemplateSpecializationFact* fact_i =
            file_.template_specialization(selected[i]);
        if (!fact_i || !fact_i->pattern_type.valid()) {
            continue;
        }
        for (size_t j = 0; j < selected.size(); ++j) {
            if (i == j || eliminated[i]) {
                continue;
            }
            const cir::TemplateSpecializationFact* fact_j =
                file_.template_specialization(selected[j]);
            if (!fact_j || !fact_j->pattern_type.valid() ||
                fact_i->template_entity == fact_j->template_entity) {
                continue;
            }
            if (compare_function_template_specializations(
                    selected[j],
                    selected[i],
                    FunctionTemplateOrderingContext::address()) ==
                FunctionTemplateSpecializationOrder::LhsMoreSpecialized) {
                eliminated[i] = true;
            }
        }
    }

    std::vector<cir::EntityId> kept;
    kept.reserve(selected.size());
    for (size_t i = 0; i < selected.size(); ++i) {
        if (!eliminated[i]) {
            kept.push_back(selected[i]);
        }
    }
    selected = std::move(kept);
}

std::vector<cir::EntityId> Session::instantiate_addressable_function_templates(
    const std::vector<cir::EntityId>& candidates,
    cir::TypeId target_function_type,
    SrcLoc loc,
    const std::vector<TemplateArgument>* explicit_arguments,
    const std::vector<CandidateExplicitTemplateArguments>*
        candidate_explicit_arguments) {
    std::vector<cir::EntityId> specializations;
    cir::TypeId target = file_.resolved_type(target_function_type);
    if (!tstate().function_template_instantiation_callback_ ||
        !file_.valid(target) ||
        file_.type(target).kind != cir::TypeKind::Function) {
        return specializations;
    }

    auto push_unique = [&](cir::EntityId entity) {
        if (!entity.valid() || !file_.valid(entity) ||
            std::find(specializations.begin(), specializations.end(), entity) !=
                specializations.end()) {
            return;
        }
        specializations.push_back(entity);
    };

    for (cir::EntityId candidate : candidates) {
        if (!candidate.valid() || !file_.valid(candidate)) {
            continue;
        }
        const TemplateInfo* info = template_info(candidate);
        if (!info || info->is_class_template || info->is_alias_template ||
            info->is_variable_template || info->is_concept) {
            continue;
        }
        const cir::Entity& entity = file_.entity(candidate);
        const cir::RecordMethodFact* method =
            entity.kind == cir::EntityKind::Method
                ? file_.method_fact(candidate)
                : nullptr;
        if (method &&
            (method->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Unsatisfied ||
             method->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Invalid)) {
            continue;
        }
        bool addressable_function =
            entity.kind == cir::EntityKind::Function ||
            (method && method->is_static);
        if (!addressable_function) {
            continue;
        }

        const std::vector<TemplateArgument>* candidate_arguments =
            explicit_arguments;
        if (candidate_explicit_arguments) {
            auto found = std::find_if(
                candidate_explicit_arguments->begin(),
                candidate_explicit_arguments->end(),
                [&](const CandidateExplicitTemplateArguments& entry) {
                    return entry.template_entity == candidate;
                });
            if (found != candidate_explicit_arguments->end()) {
                if (!found->viable) {
                    continue;
                }
                candidate_arguments = &found->arguments;
            }
        }
        std::vector<TemplateArgument> deduced;
        TemplateArgumentBindings deduced_bindings;
        if (!deduce_function_template_address_arguments(*info,
                                                        target,
                                                        deduced,
                                                        candidate_arguments,
                                                        nullptr,
                                                        loc,
                                                        TypePatternExceptionMatch::
                                                            PatternToArgumentFunctionPointerConversion,
                                                        TypePatternReturnMatch::
                                                            PlaceholderIsNonDeducedAtCurrentFunction,
                                                        &deduced_bindings)) {
            continue;
        }
        cir::EntityId specialization =
            tstate().function_template_instantiation_callback_(
                *info, deduced_bindings, loc);
        if (specialization.valid() && file_.valid(specialization)) {
            const cir::FunctionTypePayload* payload =
                function_payload(file_, file_.entity(specialization).type);
            if (payload && contains_auto_type(payload->return_type.type) &&
                !require_placeholder_result(
                    specialization,
                    cir::InstantiationDemandKind::OdrUse,
                    loc)) {
                specialization = {};
            }
        }
        if (specialization.valid() &&
            function_type_matches_address_target(
                file_, file_.entity(specialization).type, target)) {
            push_unique(specialization);
        }
    }
    return specializations;
}

bool Session::callable_is_deleted(cir::EntityId entity) const {
    if (!entity.valid() || !file_.valid(entity)) {
        return false;
    }
    if (file_.entity(entity).is_deleted) {
        return true;
    }
    if (const cir::RecordMethodFact* method = file_.method_fact(entity);
        method && method->is_deleted) {
        return true;
    }
    if (const cir::DefaultedComparisonFact* comparison =
            file_.defaulted_comparison_fact(entity);
        comparison && comparison->is_deleted) {
        return true;
    }
    return false;
}

cir::EntityId Session::select_addressable_function_target(
    const std::vector<cir::EntityId>& candidates,
    cir::TypeId target_function_type,
    SrcLoc loc,
    const std::vector<TemplateArgument>* explicit_arguments,
    const std::vector<CandidateExplicitTemplateArguments>*
        candidate_explicit_arguments,
    OverloadAmbiguityInfo* ambiguity_info,
    bool mark_odr_use) {
    if (ambiguity_info) {
        *ambiguity_info = {};
    }
    std::vector<cir::EntityId> expanded = candidates;
    std::vector<cir::EntityId> specializations =
        instantiate_addressable_function_templates(candidates,
                                                   target_function_type,
                                                   loc,
                                                   explicit_arguments,
                                                   candidate_explicit_arguments);
    expanded.insert(expanded.end(),
                    specializations.begin(),
                    specializations.end());

    std::vector<cir::EntityId> selected;
    for (cir::EntityId candidate : expanded) {
        if (!candidate.valid() || !file_.valid(candidate) ||
            template_info(candidate) != nullptr) {
            continue;
        }
        const cir::Entity& entity = file_.entity(candidate);
        const cir::RecordMethodFact* method =
            entity.kind == cir::EntityKind::Method
                ? file_.method_fact(candidate)
                : nullptr;
        if (method &&
            (method->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Unsatisfied ||
             method->constraint_satisfaction ==
                 cir::ConstraintSatisfactionKind::Invalid)) {
            continue;
        }
        bool addressable_function =
            entity.kind == cir::EntityKind::Function ||
            (method && method->is_static);
        if (addressable_function &&
            function_signatures_match(entity.type, target_function_type) &&
            !require_placeholder_result(
                candidate, cir::InstantiationDemandKind::OdrUse, loc)) {
            continue;
        }
        if (addressable_function &&
            function_type_matches_address_target(file_,
                                                 file_.entity(candidate).type,
                                                 target_function_type)) {
            selected.push_back(candidate);
        }
    }

    apply_function_template_address_eliminations(selected);
    if (selected.size() == 1) {
        if (mark_odr_use &&
            file_.template_specialization(selected.front()) &&
            !callable_is_deleted(selected.front())) {
            (void)request_function_instantiation(
                selected.front(), cir::InstantiationDemandKind::OdrUse, loc);
        }
        return selected.front();
    }
    if (ambiguity_info && selected.size() > 1) {
        describe_function_selection_ambiguity(selected, *ambiguity_info);
    }
    return {};
}

ExprResult Session::convert_function_designator_to_target(ExprResult expr,
                                                          cir::TypeId target_type,
                                                          SrcLoc loc) {
    if (expr.category != ValueCategory::FunctionDesignator &&
        expr.category != ValueCategory::OverloadDesignator) {
        return expr;
    }
    cir::TypeId target = file_.resolved_type(target_type);
    cir::TypeId target_function = is_reference_type(target)
        ? file_.reference_referred_type(target)
        : file_.pointer_pointee_type(target);
    target_function = file_.resolved_type(target_function);
    if (!file_.valid(target_function) ||
        file_.type(target_function).kind != cir::TypeKind::Function) {
        return require_value(std::move(expr), UseContext::RValue, loc);
    }

    std::shared_ptr<const OverloadDesignator> designator =
        canonical_overload_designator(expr);
    std::vector<cir::EntityId> candidates;
    if (designator) {
        for (const OverloadDesignatorCandidate& candidate :
             designator->candidates) {
            if (candidate.address_category ==
                OverloadAddressCategory::FunctionPointer) {
                candidates.push_back(candidate.entity);
            }
        }
    }
    OverloadAmbiguityInfo ambiguity_info;
    cir::EntityId selected =
        select_addressable_function_target(
            candidates,
            target_function,
            loc,
            !designator || designator->explicit_template_arguments.empty()
                ? nullptr
                : &designator->explicit_template_arguments,
            !designator
                ? nullptr
                : &designator
                       ->candidate_explicit_template_arguments,
            &ambiguity_info);
    if (selected.valid()) {
        const cir::Entity& selected_entity = file_.entity(selected);
        const cir::RecordMethodFact* selected_method =
            file_.method_fact(selected);
        if (callable_is_deleted(selected)) {
            report_error("cannot take the address of a deleted function", loc);
            expr.has_error = true;
        }
        const MemberCandidateObjectPaths* selected_lookup = designator
            ? member_candidate_paths_for_selected(
                  designator->member_candidate_object_paths, selected)
            : nullptr;
        if (selected_lookup) {
            if (!check_selected_member_candidate_access(
                    *selected_lookup, selected, loc,
                    designator->qualified_member_owner)) {
                expr.has_error = true;
            }
        } else if (selected_method &&
                   !member_access_allowed(selected_entity.parent,
                                          selected_method->declared_access)) {
            check_member_access(
                selected, selected_method->declared_access, loc);
            expr.has_error = true;
        }
        if (selected_entity.kind == cir::EntityKind::Method) {
            mark_record_method_required(selected, loc);
        }
        expr.entity = selected;
        expr.candidates.clear();
        expr.overload_designator.reset();
        expr.type = file_.entity(expr.entity).type;
        expr.category = ValueCategory::FunctionDesignator;
        return require_value(std::move(expr), UseContext::RValue, loc);
    }

    if (expr.category == ValueCategory::FunctionDesignator &&
        candidates.size() == 1 && candidates.front().valid() &&
        file_.valid(candidates.front()) &&
        template_info(candidates.front()) == nullptr) {
        expr.entity = candidates.front();
        expr.candidates.clear();
        expr.type = file_.entity(expr.entity).type;
        return require_value(std::move(expr), UseContext::RValue, loc);
    }

    report_error("cannot resolve overloaded function address", loc);
    report_overload_ambiguity_notes(ambiguity_info, loc);
    ExprResult result;
    result.has_error = true;
    result.type = builder_.unknown_type();
    result.category = ValueCategory::PrValue;
    result.fragment = std::move(expr.fragment);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.overload.error");
    result.value = builder_.error("overloaded function address", loc);
    cir::Fragment error_fragment = finish_fragment_block(block, previous);
    result.fragment = chain(std::move(result.fragment),
                            std::move(error_fragment),
                            loc);
    return result;
}

std::vector<cir::EntityId> Session::select_member_pointer_targets(
    const std::vector<cir::EntityId>& candidates,
    cir::TypeId target_type,
    SrcLoc loc,
    const std::vector<TemplateArgument>* explicit_arguments,
    const std::vector<CandidateExplicitTemplateArguments>*
        candidate_explicit_arguments,
    OverloadAmbiguityInfo* ambiguity_info) {
    if (ambiguity_info) {
        *ambiguity_info = {};
    }
    std::vector<cir::EntityId> selected;
    const cir::MemberPointerTypePayload* target =
        member_pointer_payload(file_, target_type);
    if (!target) {
        return selected;
    }

    cir::TypeId target_class = file_.resolved_type(target->class_type.type);
    cir::TypeId target_member = file_.resolved_type(target->member_type.type);
    if (!file_.valid(target_class) || !file_.valid(target_member)) {
        return selected;
    }

    auto push_unique = [&](cir::EntityId entity) {
        if (!entity.valid() || !file_.valid(entity) ||
            std::find(selected.begin(), selected.end(), entity) !=
                selected.end()) {
            return;
        }
        selected.push_back(entity);
    };

    auto candidate_matches = [&](cir::EntityId candidate) {
        if (!candidate.valid() || !file_.valid(candidate) ||
            template_info(candidate) != nullptr) {
            return false;
        }
        const cir::Entity& entity = file_.entity(candidate);
        cir::EntityId candidate_owner = entity.declaring_record.valid()
            ? entity.declaring_record
            : entity.parent;
        if (!candidate_owner.valid() || !file_.valid(candidate_owner) ||
            file_.entity(candidate_owner).kind != cir::EntityKind::Record) {
            return false;
        }
        cir::TypeId candidate_class =
            file_.resolved_type(file_.entity(candidate_owner).type);
        if (candidate_class != target_class) {
            DerivedToBasePathResult conversion =
                analyze_derived_to_base_path(target_class, candidate_class);
            if (conversion.kind != DerivedToBasePathKind::Unique) {
                return false;
            }
            for (cir::EntityId step : conversion.path) {
                const cir::RecordFieldFact* base = file_.field_fact(step);
                if (base && base->is_virtual_base_storage) {
                    return false;
                }
            }
        }
        if (entity.kind == cir::EntityKind::Field) {
            const cir::RecordFieldFact* field = file_.field_fact(candidate);
            if (!field || field->is_bitfield) {
                return false;
            }
            if (candidate_class != target_class) {
                return types_compatible(field->type,
                                        target->member_type);
            }
            cir::TypeId source_member_pointer =
                member_pointer_type(
                    file_.type_ref(candidate_class), field->type);
            QualificationConversionAnalysis qualification =
                analyze_qualification_conversion(
                    file_.type_ref(source_member_pointer),
                    file_.type_ref(target_type));
            return qualification.similar && qualification.allowed;
        }
        if (entity.kind == cir::EntityKind::Method) {
            const cir::RecordMethodFact* method = file_.method_fact(candidate);
            if (!method || method->is_static ||
                method->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Unsatisfied ||
                method->constraint_satisfaction ==
                    cir::ConstraintSatisfactionKind::Invalid) {
                return false;
            }
            if (function_signatures_match(method->type.type, target_member) &&
                !require_placeholder_result(
                    candidate, cir::InstantiationDemandKind::OdrUse, loc)) {
                return false;
            }
            method = file_.method_fact(candidate);
            if (!method) {
                return false;
            }
            cir::TypeId candidate_member =
                file_.resolved_type(method->type.type);
            if (candidate_member == target_member) {
                return true;
            }
            const auto* candidate_function =
                std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(candidate_member));
            const auto* target_function =
                std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(target_member));
            if (!candidate_function || !target_function ||
                !function_signatures_match(candidate_member, target_member) ||
                !types_compatible(candidate_function->return_type,
                                  target_function->return_type)) {
                return false;
            }

            return function_exception_spec_matches_address_target(
                candidate_function->exception_spec.kind,
                target_function->exception_spec.kind);
        }
        return false;
    };

    for (cir::EntityId candidate : candidates) {
        if (candidate_matches(candidate)) {
            push_unique(candidate);
        }
    }

    if (tstate().function_template_instantiation_callback_ &&
        file_.type(target_member).kind == cir::TypeKind::Function) {
        for (cir::EntityId candidate : candidates) {
            if (!candidate.valid() || !file_.valid(candidate)) {
                continue;
            }
            const TemplateInfo* info = template_info(candidate);
            if (!info || info->is_class_template || info->is_alias_template ||
                info->is_variable_template || info->is_concept) {
                continue;
            }
            const cir::Entity& entity = file_.entity(candidate);
            const cir::RecordMethodFact* method =
                entity.kind == cir::EntityKind::Method
                    ? file_.method_fact(candidate)
                    : nullptr;
            if (!method || method->is_static || !entity.parent.valid() ||
                !file_.valid(entity.parent) ||
                file_.resolved_type(file_.entity(entity.parent).type) !=
                    target_class) {
                continue;
            }

            std::vector<TemplateArgument> deduced;
            TemplateArgumentBindings deduced_bindings;
            const std::vector<TemplateArgument>* candidate_arguments =
                explicit_arguments;
            if (candidate_explicit_arguments) {
                auto found = std::find_if(
                    candidate_explicit_arguments->begin(),
                    candidate_explicit_arguments->end(),
                    [&](const CandidateExplicitTemplateArguments& entry) {
                        return entry.template_entity == candidate;
                    });
                if (found != candidate_explicit_arguments->end()) {
                    if (!found->viable) {
                        continue;
                    }
                    candidate_arguments = &found->arguments;
                }
            }
            if (!deduce_function_template_address_arguments(
                    *info,
                    target_member,
                    deduced,
                    candidate_arguments,
                    nullptr,
                    loc,
                    TypePatternExceptionMatch::
                        PatternToArgumentFunctionPointerConversion,
                    TypePatternReturnMatch::
                        PlaceholderIsNonDeducedAtCurrentFunction,
                    &deduced_bindings)) {
                continue;
            }
            cir::EntityId specialization =
                tstate().function_template_instantiation_callback_(
                    *info, deduced_bindings, loc);
            if (specialization.valid() && file_.valid(specialization)) {
                const cir::RecordMethodFact* specialization_method =
                    file_.method_fact(specialization);
                const cir::FunctionTypePayload* payload =
                    specialization_method
                        ? function_payload(file_,
                                           specialization_method->type.type)
                        : nullptr;
                if (payload &&
                    contains_auto_type(payload->return_type.type) &&
                    !require_placeholder_result(
                        specialization,
                        cir::InstantiationDemandKind::OdrUse,
                        loc)) {
                    specialization = {};
                }
            }
            if (candidate_matches(specialization)) {
                push_unique(specialization);
            }
        }
    }

    apply_function_template_address_eliminations(selected);
    if (selected.size() == 1 &&
        file_.template_specialization(selected.front())) {
        (void)request_function_instantiation(
            selected.front(), cir::InstantiationDemandKind::OdrUse, loc);
    }
    if (ambiguity_info && selected.size() > 1) {
        describe_function_selection_ambiguity(selected, *ambiguity_info);
    }
    return selected;
}

ExprResult Session::convert_member_pointer_designator_to_target(
    ExprResult expr,
    cir::TypeId target_type,
    SrcLoc loc) {
    if (expr.category != ValueCategory::MemberPointerDesignator &&
        expr.category != ValueCategory::OverloadDesignator) {
        return expr;
    }
    const cir::MemberPointerTypePayload* target =
        member_pointer_payload(file_, target_type);
    if (!target) {
        return expr;
    }

    auto fail = [&](std::string message,
                    const OverloadAmbiguityInfo* ambiguity_info = nullptr) {
        report_error(std::move(message), loc);
        if (ambiguity_info) {
            report_overload_ambiguity_notes(*ambiguity_info, loc);
        }
        ExprResult result;
        result.has_error = true;
        result.type = target_type.valid() ? target_type : builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        result.fragment = std::move(expr.fragment);
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.member_pointer.error");
        result.value = builder_.error("member pointer argument", loc);
        cir::Fragment error_fragment = finish_fragment_block(block, previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(error_fragment),
                                loc);
        return result;
    };

    if (!file_.valid(file_.resolved_type(target->class_type.type)) ||
        !file_.valid(file_.resolved_type(target->member_type.type))) {
        return fail("member pointer argument has invalid target type");
    }

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
    OverloadAmbiguityInfo ambiguity_info;
    std::vector<cir::EntityId> selected =
        select_member_pointer_targets(
            candidates,
            target_type,
            loc,
            !designator || designator->explicit_template_arguments.empty()
                ? nullptr
                : &designator->explicit_template_arguments,
            !designator
                ? nullptr
                : &designator
                       ->candidate_explicit_template_arguments,
            &ambiguity_info);
    if (selected.size() != 1) {
        return fail("cannot resolve member pointer argument",
                    selected.empty() ? nullptr : &ambiguity_info);
    }

    cir::EntityId member = selected.front();
    cir::RecordMemberAccess selected_access =
        cir::RecordMemberAccess::Public;
    const MemberCandidateObjectPaths* selected_lookup = designator
        ? member_candidate_paths_for_selected(
              designator->member_candidate_object_paths, member)
        : nullptr;
    if (const cir::RecordMethodFact* method = file_.method_fact(member)) {
        selected_access = method->declared_access;
        if (method->is_deleted) {
            report_error("cannot take the address of a deleted member function",
                         loc);
            expr.has_error = true;
        }
    } else if (const cir::RecordFieldFact* field = file_.field_fact(member)) {
        selected_access = file_.entity(member).declaring_record.valid()
            ? file_.entity(member).declared_member_access
            : field->declared_access;
    }
    if (selected_lookup) {
        selected_access = selected_lookup->declared_access;
        if (!check_selected_member_candidate_access(
                *selected_lookup, member, loc,
                designator->qualified_member_owner)) {
            expr.has_error = true;
        }
    } else {
        cir::EntityId selected_owner = file_.entity(member).parent;
        if (!member_access_allowed(selected_owner, selected_access)) {
            check_member_access(member, selected_access, loc);
            expr.has_error = true;
        }
    }
    if (selected_access == cir::RecordMemberAccess::Protected &&
        expr.qualified_member_owner.valid()) {
        cir::EntityId member_owner = file_.entity(member).parent;
        if (!protected_member_object_access_allowed(
                member_owner, expr.qualified_member_owner)) {
            report_error(
                "a protected member pointer must be formed through the "
                "granting class or one derived from it",
                loc);
            expr.has_error = true;
        }
    }
    cir::EntityId member_owner =
        file_.entity(member).declaring_record.valid()
            ? file_.entity(member).declaring_record
            : file_.entity(member).parent;
    cir::TypeId member_class =
        member_owner.valid() && file_.valid(member_owner)
            ? file_.resolved_type(file_.entity(member_owner).type)
            : cir::TypeId{};
    cir::TypeId target_class = file_.resolved_type(target->class_type.type);
    if (member_class.valid() && target_class.valid() &&
        member_class != target_class) {
        DerivedToBasePathResult conversion =
            analyze_derived_to_base_path(target_class, member_class);
        if (conversion.kind == DerivedToBasePathKind::Unique &&
            !check_base_path_access(conversion.path,
                                    target_class,
                                    member_class,
                                    loc)) {
            expr.has_error = true;
        }
    }
    if (file_.entity(member).kind == cir::EntityKind::Method) {
        mark_record_method_required(member, loc);
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.member_pointer_value");
    cir::TypeId source_type = target_type;
    if (file_.entity(member).kind == cir::EntityKind::Field) {
        const cir::RecordFieldFact* field = file_.field_fact(member);
        if (field && member_class.valid()) {
            source_type = member_pointer_type(file_.type_ref(member_class),
                                              field->type);
        }
    }
    if (file_.entity(member).kind == cir::EntityKind::Method) {
        const cir::RecordMethodFact* method = file_.method_fact(member);
        if (method) {
            source_type = member_pointer_type(
                                              file_.type_ref(member_class),
                                              method->type);
        }
    }
    cir::InstId value =
        builder_.member_pointer_value(member, source_type, loc);
    if (file_.resolved_type(source_type) !=
        file_.resolved_type(target_type)) {
        value = builder_.cast(target_type, value, "conversion", loc);
    }
    cir::Fragment fragment = finish_fragment_block(block, previous);
    expr.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
    expr.entity = member;
    expr.candidates.clear();
    expr.overload_designator.reset();
    expr.value = value;
    expr.place = {};
    expr.type = target_type;
    expr.category = ValueCategory::PrValue;
    return expr;
}

ExprResult Session::convert_overload_designator_to_target(ExprResult expr,
                                                          cir::TypeId target_type,
                                                          SrcLoc loc) {
    if (expr.category != ValueCategory::OverloadDesignator) {
        return expr;
    }
    cir::TypeId target = file_.resolved_type(target_type);
    if (is_member_pointer_type(file_, target)) {
        return convert_member_pointer_designator_to_target(std::move(expr),
                                                           target_type,
                                                           loc);
    }
    return convert_function_designator_to_target(std::move(expr),
                                                 target_type,
                                                 loc);
}

ExprResult Session::convert_call_argument_to_parameter(ExprResult expr,
                                                       cir::TypeId parameter_type,
                                                       SrcLoc loc) {
    if (expr.init_list && expr.category == ValueCategory::InitList) {
        return materialize_list_initialization(std::move(expr),
                                               parameter_type,
                                               UseContext::Assignment,
                                               loc);
    }
    if (expr.category == ValueCategory::OverloadDesignator) {
        expr = convert_overload_designator_to_target(std::move(expr),
                                                     parameter_type,
                                                     loc);
    } else if (expr.category == ValueCategory::FunctionDesignator) {
        expr = convert_function_designator_to_target(std::move(expr),
                                                     parameter_type,
                                                     loc);
    }
    if (expr.category == ValueCategory::MemberPointerDesignator &&
        is_member_pointer_type(file_, parameter_type)) {
        expr = convert_member_pointer_designator_to_target(std::move(expr),
                                                           parameter_type,
                                                           loc);
    }

    if (is_pointer_type(parameter_type)) {
        cir::TypeId source = file_.resolved_type(expr.type);
        if (file_.valid(source) &&
            file_.type(source).kind == cir::TypeKind::Array) {
            expr = require_value(std::move(expr), UseContext::RValue, loc);
        }
    }
    if (!parameter_type.valid() || type_equal(expr.type, parameter_type)) {
        return expr;
    }
    if (const cir::RecordFacts* union_facts =
            file_.record_facts_for_type(file_.resolved_type(parameter_type));
        union_facts && union_facts->is_transparent_union) {
        for (const cir::RecordFieldFact& field : union_facts->fields) {
            cir::TypeRef member = field.type;
            member.qualifiers = cir::QualNone;
            cir::TypeRef arg_ref = file_.type_ref(expr.type);
            arg_ref.qualifiers = cir::QualNone;
            bool matches = types_compatible(member, arg_ref);
            if (!matches && is_pointer_type(member.type) &&
                is_pointer_type(expr.type)) {
                matches = true;
            }
            if (!matches) {
                continue;
            }
            expr = convert_to(std::move(expr), member.type, UseContext::Assignment, loc);
            return wrap_in_transparent_union(std::move(expr),
                                             parameter_type,
                                             field,
                                             loc);
        }
    }

    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId target = file_.resolved_type(parameter_type);
        if (file_.valid(target) &&
            file_.type(target).kind == cir::TypeKind::Record) {
            return convert_to(std::move(expr), parameter_type,
                              UseContext::Assignment, loc);
        }
    }
    if (is_scalar_type(expr.type) && is_scalar_type(parameter_type)) {
        return convert_to(std::move(expr), parameter_type, UseContext::Assignment, loc);
    }
    if (lang_opts_.is_cxx_mode() &&
        is_member_pointer_type(file_, expr.type) &&
        (is_member_pointer_type(file_, parameter_type) ||
         is_bool_type(parameter_type))) {
        return convert_to(std::move(expr), parameter_type,
                          UseContext::Assignment, loc);
    }
    if (is_vector_type(expr.type) && is_vector_type(parameter_type)) {
        return convert_to(std::move(expr), parameter_type, UseContext::Assignment, loc);
    }
    if (is_nullptr_type(expr.type) &&
        (is_pointer_type(parameter_type) ||
         is_member_pointer_type(file_, parameter_type))) {
        return convert_to(std::move(expr), parameter_type, UseContext::Assignment, loc);
    }
    if (!lang_opts_.is_cxx_mode() && lang_opts_.is_c23_or_later() &&
        is_nullptr_type(expr.type) && is_bool_type(parameter_type)) {
        return convert_nullptr_to_bool(std::move(expr),
                                       parameter_type,
                                       "argument",
                                       loc);
    }

    if (lang_opts_.is_cxx_mode()) {
        bool generic_handled = false;
        expr = convert_generic_lambda_to_function_pointer(
            std::move(expr), parameter_type, &generic_handled, loc);
        if (generic_handled) {
            return expr;
        }
    }
    if (lang_opts_.is_cxx_mode()) {
        cir::TypeId source_resolved = file_.resolved_type(expr.type);
        cir::TypeId target_resolved = file_.resolved_type(parameter_type);
        if (file_.valid(source_resolved) && file_.valid(target_resolved) &&
            file_.type(source_resolved).kind == cir::TypeKind::Record &&
            file_.type(target_resolved).kind != cir::TypeKind::Record) {
            if (expr.category == ValueCategory::PrValue && expr.value.valid()) {
                MemberAccessBase materialized =
                    collect_member_access_base(std::move(expr),
                                               /*is_arrow=*/false,
                                               loc);
                expr = std::move(materialized.base_place);
            }
            bool ambiguous = false;
            cir::EntityId conversion =
                select_conversion_function(expr, parameter_type, &ambiguous, loc);
            if (conversion.valid()) {
                return call_conversion_function(std::move(expr),
                                                conversion,
                                                parameter_type,
                                                loc);
            }
            if (ambiguous) {
                report_error("conversion from '" + file_.format_type(expr.type) +
                                 "' to parameter of type '" +
                                 file_.format_type(parameter_type) +
                                 "' is ambiguous",
                             loc);
                expr.has_error = true;
                return expr;
            }
        }
    }
    report_error("cannot pass expression of type '" + file_.format_type(expr.type) +
                     "' to parameter of type '" + file_.format_type(parameter_type) + "'",
                 loc);
    expr.has_error = true;
    return expr;
}

ExprResult Session::initialize_default_argument(ExprResult argument,
                                                cir::TypeId parameter_type,
                                                SrcLoc loc) {
    if (is_dependent_type(parameter_type) ||
        type_contains_dependent_alias_specialization(parameter_type)) {
        return argument;
    }

    auto reclassify_concrete_replay =
        [&](auto&& self, ExprResult& expr) -> bool {
        if (expr.init_list) {
            for (InitElementInput& element : expr.init_list->elements) {
                self(self, element.value);
            }
            if (expr.category == ValueCategory::Dependent) {
                expr.category = ValueCategory::InitList;
            }
            return true;
        }
        if (expr.category != ValueCategory::Dependent &&
            (!expr.type.valid() || !is_dependent_type(expr.type))) {
            return true;
        }
        if (expr.value.valid() && file_.valid(expr.value)) {
            cir::TypeId value_type = file_.inst(expr.value).result_type;
            if (file_.valid(value_type) && !is_dependent_type(value_type)) {
                expr.type = value_type;
                expr.category = ValueCategory::PrValue;
                expr.value_dependent = false;
                return true;
            }
        }
        if (expr.place.valid() && file_.valid(expr.place)) {
            cir::TypeRef object_type =
                file_.place_object_ref(file_.inst(expr.place).result_type);
            if (object_type.type.valid() &&
                !is_dependent_type(object_type.type)) {
                expr.type = object_type.type;
                expr.category = ValueCategory::LValue;
                expr.value_dependent = false;
                return true;
            }
        }
        return false;
    };
    if (!reclassify_concrete_replay(reclassify_concrete_replay, argument)) {

        return argument;
    }

    if (is_reference_type(parameter_type)) {

        return argument;
    }
    return convert_call_argument_to_parameter(std::move(argument),
                                              parameter_type,
                                              loc);
}

bool Session::is_meta_info_type(cir::TypeId type) const {
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* payload =
        std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(resolved));
    return payload && payload->kind == cir::BuiltinTypeKind::MetaInfo;
}

void Session::diagnose_if_not_scalar(cir::TypeId type,
                                     SrcLoc loc,
                                     std::string_view context) {
    if (!file_.valid(type) || is_scalar_type(type) ||
        is_nullptr_type(type)) {
        return;
    }
    report_error(std::string(context) + " requires scalar operand", loc);
}

void Session::diagnose_if_not_arithmetic(cir::TypeId type,
                                         SrcLoc loc,
                                         std::string_view context) {
    if (!file_.valid(type) || is_arithmetic_type(type)) {
        return;
    }
    report_error(std::string(context) + " requires arithmetic operands", loc);
}

void Session::diagnose_if_not_integer(cir::TypeId type,
                                      SrcLoc loc,
                                      std::string_view context) {
    if (!file_.valid(type) || is_integer_type(type)) {
        return;
    }
    report_error(std::string(context) + " requires integer operands", loc);
}

cir::TypeId Session::binary_result_type(syntax::BinaryOperator op,
                                        cir::TypeId lhs,
                                        cir::TypeId rhs,
                                        SrcLoc loc) {
    cir::TypeId comparison_type =
        lang_opts_.is_cxx_mode() ? builder_.bool_type() : builder_.int_type();
    switch (op) {
        case syntax::BinaryOperator::Less:
        case syntax::BinaryOperator::LessEqual:
        case syntax::BinaryOperator::Greater:
        case syntax::BinaryOperator::GreaterEqual:
        case syntax::BinaryOperator::Equal:
        case syntax::BinaryOperator::NotEqual:
            if (is_arithmetic_type(lhs) && is_arithmetic_type(rhs)) {
                return comparison_type;
            }

            if (is_meta_info_type(lhs) && is_meta_info_type(rhs)) {
                if (op == syntax::BinaryOperator::Equal ||
                    op == syntax::BinaryOperator::NotEqual) {
                    return comparison_type;
                }
                report_error("only equality comparison is defined for "
                             "'std::meta::info'",
                             loc);
                return comparison_type;
            }
            report_error("comparison requires arithmetic operands", loc);
            return comparison_type;
        case syntax::BinaryOperator::LogicalAnd:
        case syntax::BinaryOperator::LogicalOr:
            return comparison_type;
        case syntax::BinaryOperator::Shl:
        case syntax::BinaryOperator::Shr:
            diagnose_if_not_integer(lhs, loc, "binary shift");
            diagnose_if_not_integer(rhs, loc, "binary shift");
            return integer_promotion_type(lhs);
        case syntax::BinaryOperator::Mod:
        case syntax::BinaryOperator::BitAnd:
        case syntax::BinaryOperator::BitOr:
        case syntax::BinaryOperator::BitXor:
            diagnose_if_not_integer(lhs, loc, "binary expression");
            diagnose_if_not_integer(rhs, loc, "binary expression");
            return usual_arithmetic_conversion_type(lhs, rhs);
        case syntax::BinaryOperator::Add:
        case syntax::BinaryOperator::Sub:
        case syntax::BinaryOperator::Mul:
        case syntax::BinaryOperator::Div:
            diagnose_if_not_arithmetic(lhs, loc, "binary expression");
            diagnose_if_not_arithmetic(rhs, loc, "binary expression");
            return usual_arithmetic_conversion_type(lhs, rhs);
        default:
            return builder_.int_type();
    }
}

bool Session::is_reference_type(cir::TypeId type) const {
    if (!file_.valid(type)) {
        return false;
    }
    cir::TypeId resolved = file_.resolved_type(type);
    if (!file_.valid(resolved)) {
        return false;
    }
    cir::TypeKind kind = file_.type(resolved).kind;
    return kind == cir::TypeKind::LValueReference ||
           kind == cir::TypeKind::RValueReference;
}

bool Session::array_type_has_const_element(cir::TypeId type) const {
    type = file_.resolved_type(type);
    if (!file_.valid(type) || file_.type(type).kind != cir::TypeKind::Array) {
        return false;
    }
    cir::TypeRef element = file_.array_element_ref(type);
    return (element.qualifiers & cir::QualConst) != 0 ||
           array_type_has_const_element(element.type);
}

ExprResult Session::deref_reference_lvalue(ExprResult expr, SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(expr.type);
    if (!is_reference_type(resolved)) {
        return expr;
    }
    cir::TypeRef referred = file_.reference_referred_ref(resolved);
    if (!expr.place.valid()) {
        // Deferred cross-function locals (notably lambda captures) do not
        // acquire their closure-field place until odr-use materialization.
        // Reference adjustment is nevertheless an expression-typing rule:
        // deduction and overload resolution must see the referred type, not
        // the declaration's reference storage type, before that place exists.
        expr.type = referred.type;
        expr.semantic_object_qualifiers = static_cast<uint8_t>(
            expr.semantic_object_qualifiers.value_or(0) |
            referred.qualifiers);
        return expr;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.ref");
    cir::InstId reference_value = builder_.lvalue_to_rvalue(expr.place, loc);
    cir::InstId place = builder_.deref(reference_value, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);
    expr.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
    expr.place = place;
    expr.value = {};
    expr.type = referred.type;
    expr.category = ValueCategory::LValue;
    return expr;
}

ExprResult Session::bind_to_reference(ExprResult expr,
                                      cir::TypeId reference_type,
                                      SrcLoc loc,
                                      UserConversionContext
                                          conversion_context) {
    expr = materialize_deferred_entity_place(
        std::move(expr), /*allow_non_odr_constant=*/false, loc);
    cir::TypeId resolved_reference = file_.resolved_type(reference_type);
    cir::TypeRef referred = file_.reference_referred_ref(resolved_reference);
    if (!referred.type.valid()) {
        expr.has_error = true;
        expr.type = reference_type;
        return expr;
    }
    bool is_rvalue_reference =
        file_.type(resolved_reference).kind == cir::TypeKind::RValueReference;
    bool const_lvalue_reference =
        !is_rvalue_reference &&
        ((referred.qualifiers & cir::QualConst) != 0 ||
         array_type_has_const_element(referred.type));

    if (expr_is_dependent(expr) || is_dependent_type(referred.type)) {
        return make_deferred_typed_expr(
            std::move(expr), reference_type, ValueCategory::PrValue, loc);
    }

    if (expr.has_error) {
        expr.type = reference_type;
        return expr;
    }
    if (expr.init_list || expr.category == ValueCategory::InitList) {
        cir::TypeId referred_resolved = file_.resolved_type(referred.type);
        bool can_bind_array_temporary =
            file_.valid(referred_resolved) &&
            file_.type(referred_resolved).kind == cir::TypeKind::Array &&
            (const_lvalue_reference ||
             array_type_has_const_element(referred_resolved) ||
             is_rvalue_reference);
        if (can_bind_array_temporary) {
            bool init_had_error = expr.has_error;
            cir::TypeId temporary_array_type = referred.type;
            const auto* referred_array =
                std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(referred_resolved));
            if (referred_array && !referred_array->size.has_value()) {
                temporary_array_type = file_.array_type(
                    referred_array->element_type,
                    cir::ArraySizeKind::Constant,
                    expr.init_list->elements.size());
            }
            std::string temp_name =
                ".ref.array.tmp." + std::to_string(compound_literal_counter_++);
            cir::EntityId temp = builder_.add_entity(
                cir::EntityKind::Variable,
                temp_name,
                temporary_array_type,
                {},
                loc,
                cir::StorageDuration::Automatic,
                cir::MemorySpace::Default,
                {});
            file_.entity_mut(temp).is_definition = true;
            file_.entity_mut(temp).qualifiers = referred.qualifiers;

            cir::BlockId previous = builder_.current_block();
            cir::BlockId place_block = begin_fragment_block("expr.ref.array.temp");
            cir::InstId temp_place =
                builder_.local_place(temp, temporary_array_type, loc);
            cir::Fragment place_fragment =
                finish_fragment_block(place_block, previous);
            cir::Fragment init_fragment =
                emit_initializer_for_place(temp_place,
                                           temporary_array_type,
                                           std::move(expr),
                                           loc);

            previous = builder_.current_block();
            cir::BlockId bind_block = begin_fragment_block("expr.ref.array.bind");
            cir::InstId address = builder_.addr_of(temp_place, loc);
            cir::InstId bound =
                builder_.cast(reference_type, address, "reference", loc);
            cir::Fragment bind_fragment =
                finish_fragment_block(bind_block, previous);

            ExprResult result;
            result.fragment = chain(std::move(place_fragment),
                                    std::move(init_fragment),
                                    loc);
            result.fragment = chain(std::move(result.fragment),
                                    std::move(bind_fragment),
                                    loc);
            result.value = bound;
            result.type = reference_type;
            result.category = ValueCategory::PrValue;
            result.reference_binds_to_temporary = true;
            if (cir::LifetimeId lifetime = register_destructor_cleanup(
                    temp, temporary_array_type, loc,
                    /*full_expression_temporary=*/true);
                lifetime.valid()) {
                result.materialized_lifetimes.push_back(lifetime);
            }
            result.has_error = init_had_error;
            return result;
        }
        if (expr.init_list->elements.size() == 1 &&
            expr.init_list->elements.front().designators.empty()) {
            ExprResult& candidate =
                expr.init_list->elements.front().value;
            ConversionRank direct_rank = conversion_rank(
                candidate, file_.type_ref(reference_type),
                candidate.semantic_object_qualifiers.value_or(0),
                /*detail=*/nullptr, /*allow_user_defined=*/true);
            if (direct_rank != ConversionRank::Bad) {
                ExprResult element = std::move(candidate);
                if (expr.init_list->syntax == InitListSyntax::Braced) {
                    element.has_error = diagnose_braced_narrowing(
                                            referred.type, element, loc) ||
                        element.has_error;
                }
                return bind_to_reference(
                    std::move(element), reference_type, loc);
            }
        }
        if (!const_lvalue_reference && !is_rvalue_reference) {
            report_error("non-const lvalue reference of type '" +
                             file_.format_type(reference_type) +
                             "' cannot bind to a list-initialized temporary",
                         loc);
            expr.has_error = true;
            expr.type = reference_type;
            return expr;
        }
        ExprResult temporary = materialize_list_initialization(
            std::move(expr), referred.type, UseContext::Init, loc);
        return bind_to_reference(std::move(temporary), reference_type, loc);
    }

    cir::TypeId referred_resolved = file_.resolved_type(referred.type);
    if ((expr.category == ValueCategory::FunctionDesignator ||
         expr.category == ValueCategory::OverloadDesignator) &&
        file_.valid(referred_resolved) &&
        file_.type(referred_resolved).kind == cir::TypeKind::Function) {
        std::shared_ptr<const OverloadDesignator> designator =
            canonical_overload_designator(expr);
        std::vector<cir::EntityId> candidates;
        if (designator) {
            for (const OverloadDesignatorCandidate& candidate :
                 designator->candidates) {
                if (candidate.address_category ==
                    OverloadAddressCategory::FunctionPointer) {
                    candidates.push_back(candidate.entity);
                }
            }
        }
        cir::EntityId selected =
            select_addressable_function_target(candidates,
                                               referred_resolved,
                                               loc,
                                               !designator ||
                                                       designator->explicit_template_arguments.empty()
                                                   ? nullptr
                                                   : &designator->explicit_template_arguments,
                                               !designator
                                                   ? nullptr
                                                   : &designator
                                                          ->candidate_explicit_template_arguments);
        if (!selected.valid()) {
            report_error("cannot resolve overloaded function reference", loc);
            expr.has_error = true;
            expr.type = reference_type;
            return expr;
        }
        if (callable_is_deleted(selected)) {
            report_error("cannot bind a reference to a deleted function", loc);
            expr.has_error = true;
        }

        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("expr.ref.function");
        cir::InstId pointer = builder_.function_to_pointer(selected, loc);
        cir::InstId bound =
            builder_.cast(reference_type, pointer, "reference", loc);
        cir::Fragment fragment = finish_fragment_block(block, previous);
        expr.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
        expr.entity = selected;
        expr.candidates.clear();
        expr.overload_designator.reset();
        expr.value = bound;
        expr.type = reference_type;
        expr.category = ValueCategory::PrValue;
        return expr;
    }

    bool glvalue_with_place =
        (expr.category == ValueCategory::LValue ||
         expr.category == ValueCategory::XValue) &&
        expr.place.valid();
    bool materialized_for_reference = false;

    if (!glvalue_with_place && expr.category == ValueCategory::PrValue &&
        expr.value.valid() && !expr.materialized_lifetimes.empty()) {
        cir::EntityId temporary = temporary_entity_of_value(expr.value);
        if (temporary.valid() && file_.valid(temporary)) {
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.ref.materialized");
            expr.place = builder_.local_place(temporary,
                                              file_.entity(temporary).type,
                                              loc);
            cir::Fragment place_fragment =
                finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment),
                                  std::move(place_fragment), loc);
            expr.value = {};
            expr.category = ValueCategory::XValue;
            glvalue_with_place = true;
            materialized_for_reference = true;
        }
    }
    if (glvalue_with_place && expr.designates_bitfield) {
        if (!const_lvalue_reference) {
            report_error("non-const reference cannot bind to bit-field", loc);
            expr.has_error = true;
            expr.type = reference_type;
            return expr;
        }

        expr = require_value(std::move(expr), UseContext::RValue, loc);
        glvalue_with_place = false;
    }
    if (glvalue_with_place) {
        cir::TypeRef object_ref = file_.type_ref(expr.type);
        const cir::Inst& place_inst = file_.inst(expr.place);
        if (place_inst.place_fact.valid()) {
            object_ref = file_.place_fact(place_inst.place_fact).object_type;
        }
        QualificationConversionAnalysis qualification =
            analyze_qualification_conversion(
                object_ref,
                referred,
                QualificationTargetKind::ReferenceCompatible);
        if (qualification.similar) {
            if (is_rvalue_reference) {
                if (expr.category == ValueCategory::LValue &&
                    (!file_.valid(referred_resolved) ||
                     file_.type(referred_resolved).kind !=
                         cir::TypeKind::Function)) {
                    report_error("rvalue reference of type '" +
                                     file_.format_type(reference_type) +
                                     "' cannot bind to an lvalue",
                                 loc);
                    expr.has_error = true;
                }
            } else if (expr.category == ValueCategory::XValue &&
                       !const_lvalue_reference) {
                report_error("non-const lvalue reference of type '" +
                                 file_.format_type(reference_type) +
                                 "' cannot bind to an xvalue",
                             loc);
                expr.has_error = true;
            }
            if (!qualification.allowed) {
                report_error("binding reference of type '" +
                                 file_.format_type(reference_type) +
                                 "' discards qualifiers",
                             loc);
                expr.has_error = true;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.ref.bind");
            cir::InstId address = builder_.addr_of(expr.place, loc);
            cir::InstId bound =
                builder_.cast(reference_type, address, "reference", loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
            expr.place = {};
            expr.value = bound;
            expr.type = reference_type;
            expr.category = ValueCategory::PrValue;
            expr.reference_binds_to_temporary =
                expr.reference_binds_to_temporary ||
                materialized_for_reference;
            return expr;
        }
    }

    if (!glvalue_with_place && expr.category == ValueCategory::PrValue &&
        expr.value.valid()) {
        DerivedToBasePathResult base_result =
            analyze_derived_to_base_path(expr.type, referred.type);
        if (base_result.kind == DerivedToBasePathKind::Ambiguous) {
            report_error("ambiguous conversion from derived class '" +
                             file_.format_type(expr.type) +
                             "' to base class '" +
                             file_.format_type(referred.type) + "'",
                         loc);
            expr.has_error = true;
            expr.type = reference_type;
            return expr;
        }
        if (base_result.kind == DerivedToBasePathKind::Unique) {
            MemberAccessBase materialized =
                collect_member_access_base(std::move(expr),
                                           /*is_arrow=*/false,
                                           loc);
            expr = std::move(materialized.base_place);
            glvalue_with_place = expr.place.valid();
        }
    }

    if (glvalue_with_place) {
        DerivedToBasePathResult base_result =
            analyze_derived_to_base_path(expr.type, referred.type);
        if (base_result.kind == DerivedToBasePathKind::Ambiguous) {
            report_error("ambiguous conversion from derived class '" +
                             file_.format_type(expr.type) +
                             "' to base class '" +
                             file_.format_type(referred.type) + "'",
                         loc);
            expr.has_error = true;
            expr.type = reference_type;
            return expr;
        }
        if (base_result.kind == DerivedToBasePathKind::Unique) {

            if (!check_base_path_access(base_result.path, expr.type,
                                        referred.type, loc)) {
                expr.has_error = true;
            }
            if (is_rvalue_reference) {
                if (expr.category == ValueCategory::LValue) {
                    report_error("rvalue reference of type '" +
                                     file_.format_type(reference_type) +
                                     "' cannot bind to an lvalue",
                                 loc);
                    expr.has_error = true;
                }
            } else if (expr.category == ValueCategory::XValue &&
                       !const_lvalue_reference) {
                report_error("non-const lvalue reference of type '" +
                                 file_.format_type(reference_type) +
                                 "' cannot bind to an xvalue",
                             loc);
                expr.has_error = true;
            }
            cir::BlockId previous = builder_.current_block();
            cir::BlockId block = begin_fragment_block("expr.ref.base");
            cir::InstId place =
                emit_subobject_path(expr.place, base_result.path, loc);
            cir::InstId address = builder_.addr_of(place, loc);
            cir::InstId bound =
                builder_.cast(reference_type, address, "reference", loc);
            cir::Fragment fragment = finish_fragment_block(block, previous);
            expr.fragment = chain(std::move(expr.fragment), std::move(fragment), loc);
            expr.place = {};
            expr.value = bound;
            expr.type = reference_type;
            expr.category = ValueCategory::PrValue;
            expr.reference_binds_to_temporary =
                expr.reference_binds_to_temporary ||
                materialized_for_reference;
            return expr;
        }
    }

    if (lang_opts_.is_cxx_mode()) {
        bool ambiguous = false;
        cir::EntityId conversion =
            select_conversion_function(expr, reference_type, &ambiguous, loc,
                                       conversion_context);
        if (conversion.valid()) {
            return call_conversion_function(std::move(expr),
                                            conversion,
                                            reference_type,
                                            loc);
        }
        if (ambiguous) {
            report_error("conversion from '" + file_.format_type(expr.type) +
                             "' to '" + file_.format_type(reference_type) +
                             "' is ambiguous",
                         loc);
            expr.has_error = true;
            expr.type = reference_type;
            return expr;
        }
    }

    if (!const_lvalue_reference && !is_rvalue_reference) {
        report_error("non-const lvalue reference of type '" +
                         file_.format_type(reference_type) +
                         "' cannot bind to a temporary of type '" +
                         file_.format_type(expr.type) + "'",
                     loc);
        expr.has_error = true;
        expr.type = reference_type;
        return expr;
    }

    ExprResult value = convert_to(std::move(expr), referred.type,
                                  UseContext::Init, loc);
    if (value.category == ValueCategory::PrValue && value.value.valid() &&
        !value.materialized_lifetimes.empty()) {

        return bind_to_reference(std::move(value), reference_type, loc,
                                 conversion_context);
    }
    std::string temp_name = ".ref.tmp." + std::to_string(compound_literal_counter_++);
    cir::EntityId temp = builder_.add_entity(cir::EntityKind::Variable,
                                             temp_name,
                                             referred.type,
                                             {},
                                             loc,
                                             cir::StorageDuration::Automatic,
                                             cir::MemorySpace::Default,
                                             {});
    file_.entity_mut(temp).is_definition = true;
    file_.entity_mut(temp).qualifiers = referred.qualifiers;

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("expr.ref.temp");
    cir::InstId temp_place = builder_.local_place(temp, referred.type, loc);
    builder_.store(temp_place, value.value, loc);
    cir::InstId address = builder_.addr_of(temp_place, loc);
    cir::InstId bound = builder_.cast(reference_type, address, "reference", loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = chain(std::move(value.fragment), std::move(fragment), loc);
    result.value = bound;
    result.type = reference_type;
    result.category = ValueCategory::PrValue;
    result.reference_binds_to_temporary = true;
    if (cir::LifetimeId lifetime = register_destructor_cleanup(
            temp, referred.type, loc,
            /*full_expression_temporary=*/true);
        lifetime.valid()) {
        result.materialized_lifetimes.push_back(lifetime);
    }
    result.has_error = value.has_error;
    return result;
}

} // namespace aburi::collect
