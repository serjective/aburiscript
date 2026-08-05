

#include "graph_serialize.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "file.h"
#include "graph_serialize_detail.h"

namespace aburi::cir {

namespace {

namespace detail = graph_detail;

constexpr uint32_t kModuleGraphMagic = 0x53524943u;

class GraphWriter {
public:
    static constexpr bool is_reader = false;

    explicit GraphWriter(serialize::ByteWriter& writer) : writer_(writer) {}

    bool ok() const { return true; }
    void fail() {}

    void u8(uint8_t& value) { detail::write_u8(writer_, value); }
    void u16(uint16_t& value) { detail::write_u16(writer_, value); }
    void u32(uint32_t& value) { detail::write_u32(writer_, value); }
    void u64(uint64_t& value) { detail::write_u64(writer_, value); }
    void i64(int64_t& value) { detail::write_i64(writer_, value); }
    void i32(int32_t& value) {
        detail::write_u32(writer_, static_cast<uint32_t>(value));
    }
    void int_value(int& value) {
        detail::write_u32(writer_, static_cast<uint32_t>(value));
    }
    void i8(int8_t& value) {
        detail::write_u8(writer_, static_cast<uint8_t>(value));
    }
    void chr(char& value) {
        detail::write_u8(writer_, static_cast<uint8_t>(value));
    }
    void size(size_t& value) {
        detail::write_u64(writer_, static_cast<uint64_t>(value));
    }
    void boolean(bool& value) { detail::write_u8(writer_, value ? 1 : 0); }
    void str(std::string& value) { detail::write_string(writer_, value); }
    template <typename E>
    void enum32(E& value) {
        detail::write_u32(writer_, static_cast<uint32_t>(value));
    }
    template <typename Tag>
    void id(Id<Tag>& value) {
        detail::write_id(writer_, value);
    }
    void srcloc(SrcLoc& value) { detail::write_srcloc(writer_, value); }
    void type_ref(TypeRef& value) { detail::write_type_ref(writer_, value); }
    void floating(FloatingValue& value) {
        detail::write_floating(writer_, value);
    }
    void value_expression(TemplateValueExpression& value) {
        detail::write_value_expression(writer_, value);
    }
    void template_argument(TemplateArgument& value) {
        detail::write_template_argument(writer_, value);
    }
    void long_double(long double& value) {

        char buffer[80];
        std::snprintf(buffer, sizeof buffer, "%La", value);
        detail::write_string(writer_, buffer);
    }
    template <typename T, typename Fn>
    void vector(std::vector<T>& values, Fn fn) {
        detail::write_u32(writer_, static_cast<uint32_t>(values.size()));
        for (T& value : values) {
            fn(*this, value);
        }
    }

private:
    serialize::ByteWriter& writer_;
};

class GraphReader {
public:
    static constexpr bool is_reader = true;

    explicit GraphReader(serialize::ByteReader& reader) : reader_(reader) {}

    bool ok() const { return ok_ && reader_.ok(); }
    void fail() { ok_ = false; }

    void u8(uint8_t& value) {
        if (!detail::read_u8(reader_, &value)) {
            fail();
        }
    }
    void u16(uint16_t& value) { value = reader_.u16(); }
    void u32(uint32_t& value) { value = reader_.u32(); }
    void u64(uint64_t& value) { value = reader_.u64(); }
    void i64(int64_t& value) { value = static_cast<int64_t>(reader_.u64()); }
    void i32(int32_t& value) { value = static_cast<int32_t>(reader_.u32()); }
    void int_value(int& value) { value = static_cast<int>(reader_.u32()); }
    void i8(int8_t& value) {
        uint8_t byte = 0;
        u8(byte);
        value = static_cast<int8_t>(byte);
    }
    void chr(char& value) {
        uint8_t byte = 0;
        u8(byte);
        value = static_cast<char>(byte);
    }
    void size(size_t& value) { value = static_cast<size_t>(reader_.u64()); }
    void boolean(bool& value) {
        uint8_t byte = 0;
        u8(byte);
        value = byte != 0;
    }
    void str(std::string& value) {
        if (!detail::read_string(reader_, &value)) {
            fail();
        }
    }
    template <typename E>
    void enum32(E& value) {
        value = static_cast<E>(reader_.u32());
    }
    template <typename Tag>
    void id(Id<Tag>& value) {
        if (!detail::read_id(reader_, &value)) {
            fail();
        }
    }
    void srcloc(SrcLoc& value) {
        if (!detail::read_srcloc(reader_, &value)) {
            fail();
        }
    }
    void type_ref(TypeRef& value) {
        if (!detail::read_type_ref(reader_, &value)) {
            fail();
        }
    }
    void floating(FloatingValue& value) {
        if (!detail::read_floating(reader_, &value)) {
            fail();
        }
    }
    void value_expression(TemplateValueExpression& value) {
        if (!detail::read_value_expression(reader_, &value)) {
            fail();
        }
    }
    void template_argument(TemplateArgument& value) {
        if (!detail::read_template_argument(reader_, &value)) {
            fail();
        }
    }
    void long_double(long double& value) {
        std::string text;
        if (!detail::read_string(reader_, &text)) {
            fail();
            return;
        }
        value = std::strtold(text.c_str(), nullptr);
    }
    template <typename T, typename Fn>
    void vector(std::vector<T>& values, Fn fn) {
        uint32_t count = reader_.u32();
        if (!ok() || count > detail::max_serialized_elements) {
            fail();
            return;
        }
        values.clear();
        for (uint32_t index = 0; index < count && ok(); ++index) {
            T value{};
            fn(*this, value);
            values.push_back(std::move(value));
        }
    }

private:
    serialize::ByteReader& reader_;
    bool ok_ = true;
};

template <typename Ar, typename T, typename Fn>
void io_optional(Ar& ar, std::optional<T>& value, Fn fn) {
    if constexpr (Ar::is_reader) {
        uint8_t present = 0;
        ar.u8(present);
        if (!ar.ok()) {
            return;
        }
        if (present != 0) {
            value.emplace();
            fn(ar, *value);
        } else {
            value.reset();
        }
    } else {
        uint8_t present = value.has_value() ? 1 : 0;
        ar.u8(present);
        if (value.has_value()) {
            fn(ar, *value);
        }
    }
}

template <typename V, size_t... Is>
void emplace_variant_alternative(V& value,
                                 size_t index,
                                 std::index_sequence<Is...>) {
    ((index == Is ? (value.template emplace<Is>(), void()) : void()), ...);
}

template <typename Ar, typename V, typename Fn>
void io_variant(Ar& ar, V& value, Fn fn) {
    uint32_t index = static_cast<uint32_t>(value.index());
    ar.u32(index);
    if constexpr (Ar::is_reader) {
        if (!ar.ok()) {
            return;
        }
        if (index >= std::variant_size_v<V>) {
            ar.fail();
            return;
        }
        emplace_variant_alternative(
            value, index, std::make_index_sequence<std::variant_size_v<V>>{});
    }
    std::visit([&](auto& alternative) { fn(ar, alternative); }, value);
}

template <typename Ar, typename V, typename Fn>
void io_u64_map(Ar& ar, std::unordered_map<uint64_t, V>& map, Fn fn) {
    if constexpr (Ar::is_reader) {
        uint32_t count = 0;
        ar.u32(count);
        if (!ar.ok() || count > detail::max_serialized_elements) {
            ar.fail();
            return;
        }
        map.clear();
        for (uint32_t index = 0; index < count && ar.ok(); ++index) {
            uint64_t key = 0;
            ar.u64(key);
            V value{};
            fn(ar, value);
            if (ar.ok()) {
                map.emplace(key, std::move(value));
            }
        }
    } else {
        std::vector<std::pair<uint64_t, V*>> entries;
        entries.reserve(map.size());
        for (auto& [key, value] : map) {
            entries.emplace_back(key, &value);
        }
        std::sort(entries.begin(), entries.end(),
                  [](const auto& lhs, const auto& rhs) {
                      return lhs.first < rhs.first;
                  });
        uint32_t count = static_cast<uint32_t>(entries.size());
        ar.u32(count);
        for (auto& [key, value] : entries) {
            uint64_t key_copy = key;
            ar.u64(key_copy);
            fn(ar, *value);
        }
    }
}

template <typename Ar, typename IdT>
void io_u64_id_multimap(Ar& ar, std::unordered_multimap<uint64_t, IdT>& map) {
    if constexpr (Ar::is_reader) {
        uint32_t count = 0;
        ar.u32(count);
        if (!ar.ok() || count > detail::max_serialized_elements) {
            ar.fail();
            return;
        }
        map.clear();
        for (uint32_t index = 0; index < count && ar.ok(); ++index) {
            uint64_t key = 0;
            ar.u64(key);
            IdT value{};
            ar.id(value);
            if (ar.ok()) {
                map.emplace(key, value);
            }
        }
    } else {
        std::vector<std::pair<uint64_t, IdT>> entries(map.begin(), map.end());
        std::sort(entries.begin(), entries.end(),
                  [](const auto& lhs, const auto& rhs) {
                      if (lhs.first != rhs.first) {
                          return lhs.first < rhs.first;
                      }
                      if (lhs.second.index != rhs.second.index) {
                          return lhs.second.index < rhs.second.index;
                      }
                      return lhs.second.generation < rhs.second.generation;
                  });
        uint32_t count = static_cast<uint32_t>(entries.size());
        ar.u32(count);
        for (auto& [key, value] : entries) {
            ar.u64(key);
            ar.id(value);
        }
    }
}

template <typename Ar>
void io_builtin_type_map(Ar& ar,
                         std::unordered_map<BuiltinTypeKind, TypeId>& map) {
    if constexpr (Ar::is_reader) {
        uint32_t count = 0;
        ar.u32(count);
        if (!ar.ok() || count > detail::max_serialized_elements) {
            ar.fail();
            return;
        }
        map.clear();
        for (uint32_t index = 0; index < count && ar.ok(); ++index) {
            BuiltinTypeKind kind = BuiltinTypeKind::Void;
            ar.enum32(kind);
            TypeId type{};
            ar.id(type);
            if (ar.ok()) {
                map.emplace(kind, type);
            }
        }
    } else {
        std::vector<std::pair<BuiltinTypeKind, TypeId>> entries(map.begin(),
                                                                map.end());
        std::sort(entries.begin(), entries.end(),
                  [](const auto& lhs, const auto& rhs) {
                      return static_cast<uint32_t>(lhs.first) <
                             static_cast<uint32_t>(rhs.first);
                  });
        uint32_t count = static_cast<uint32_t>(entries.size());
        ar.u32(count);
        for (auto& [kind, type] : entries) {
            ar.enum32(kind);
            ar.id(type);
        }
    }
}

template <typename Ar, typename V, typename Fn>
void io_string_map(Ar& ar, std::unordered_map<std::string, V>& map, Fn fn) {
    if constexpr (Ar::is_reader) {
        uint32_t count = 0;
        ar.u32(count);
        if (!ar.ok() || count > detail::max_serialized_elements) {
            ar.fail();
            return;
        }
        map.clear();
        for (uint32_t index = 0; index < count && ar.ok(); ++index) {
            std::string key;
            ar.str(key);
            V value{};
            fn(ar, value);
            if (ar.ok()) {
                map.emplace(std::move(key), std::move(value));
            }
        }
    } else {
        std::vector<std::pair<const std::string*, V*>> entries;
        entries.reserve(map.size());
        for (auto& [key, value] : map) {
            entries.emplace_back(&key, &value);
        }
        std::sort(entries.begin(), entries.end(),
                  [](const auto& lhs, const auto& rhs) {
                      return *lhs.first < *rhs.first;
                  });
        uint32_t count = static_cast<uint32_t>(entries.size());
        ar.u32(count);
        for (auto& [key, value] : entries) {
            std::string key_copy = *key;
            ar.str(key_copy);
            fn(ar, *value);
        }
    }
}

template <typename Ar>
void io_fields(Ar&, std::monostate&) {}

template <typename Ar, typename Tag>
void io_fields(Ar& ar, Id<Tag>& value) {
    ar.id(value);
}

template <typename Ar>
void io_fields(Ar& ar, ValueRef& value) {
    ar.id(value.inst);
}

template <typename Ar>
void io_fields(Ar& ar, TypeRef& value) {
    ar.type_ref(value);
}

template <typename Ar>
void io_fields(Ar& ar, int64_t& value) {
    ar.i64(value);
}

template <typename Ar>
void io_fields(Ar& ar, bool& value) {
    ar.boolean(value);
}

template <typename Ar>
void io_fields(Ar& ar, FloatingValue& value) {
    ar.floating(value);
}

template <typename Ar>
void io_fields(Ar& ar, IntegerValue& value) {
    ar.u64(value.low_bits);
    ar.u64(value.high_bits);
    ar.u16(value.bit_width);
    ar.boolean(value.is_unsigned);
}

template <typename Ar>
void io_fields(Ar& ar, std::vector<uint8_t>& value) {
    ar.vector(value, [](auto& a, auto& byte) { a.u8(byte); });
}

template <typename Ar>
void io_fields(Ar& ar, AttributeArg& value) {
    ar.enum32(value.kind);
    ar.str(value.value);
    ar.str(value.key);
    ar.i64(value.int_value);
    ar.long_double(value.float_value);
    ar.u32(value.dependent_value_param_index);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, ParsedAttribute& value) {
    ar.str(value.ns);
    ar.str(value.name);
    ar.vector(value.args, [](auto& a, auto& arg) { io_fields(a, arg); });
    ar.srcloc(value.loc);
    ar.enum32(value.syntax);
    ar.enum32(value.kind);
}

template <typename Ar>
void io_fields(Ar&, InvalidTypePayload&) {}

template <typename Ar>
void io_fields(Ar&, ErrorTypePayload&) {}

template <typename Ar>
void io_fields(Ar& ar, UnknownTypePayload& value) {
    ar.str(value.debug_name);
}

template <typename Ar>
void io_fields(Ar& ar, BuiltinTypePayload& value) {
    ar.enum32(value.kind);
    ar.str(value.spelling);
    ar.i64(value.width_override);
    ar.int_value(value.rank_override);
    ar.i8(value.unsigned_override);
}

template <typename Ar>
void io_fields(Ar& ar, PointerTypePayload& value) {
    ar.type_ref(value.pointee);
}

template <typename Ar>
void io_fields(Ar& ar, BlockPointerTypePayload& value) {
    ar.type_ref(value.pointee);
}

template <typename Ar>
void io_fields(Ar& ar, MemberPointerTypePayload& value) {
    ar.type_ref(value.class_type);
    ar.type_ref(value.member_type);
}

template <typename Ar>
void io_fields(Ar& ar, ReferenceTypePayload& value) {
    ar.type_ref(value.referred_type);
    ar.enum32(value.reference_kind);
}

template <typename Ar>
void io_fields(Ar& ar, ArrayTypePayload& value) {
    ar.type_ref(value.element_type);
    ar.enum32(value.size_kind);
    io_optional(ar, value.size, [](auto& a, auto& size) { a.size(size); });
    ar.id(value.size_expr);
    ar.boolean(value.size_expr_is_dependent);
    ar.u32(value.extent_param);
    ar.value_expression(value.dependent_size_expr);
}

template <typename Ar>
void io_fields(Ar& ar, FunctionExceptionSpec& value) {
    ar.enum32(value.kind);
    ar.value_expression(value.predicate);
}

template <typename Ar>
void io_fields(Ar& ar, FunctionTypePayload& value) {
    ar.type_ref(value.return_type);
    ar.vector(value.parameters,
              [](auto& a, auto& parameter) { a.type_ref(parameter); });
    ar.vector(value.parameter_pack_flags,
              [](auto& a, auto& flag) { a.u8(flag); });
    ar.boolean(value.is_variadic);
    ar.boolean(value.has_prototype);
    ar.enum32(value.member_ref_qualifier);
    ar.boolean(value.member_is_const);
    ar.boolean(value.member_is_volatile);
    io_fields(ar, value.exception_spec);
    ar.enum32(value.calling_convention);
}

template <typename Ar>
void io_fields(Ar& ar, RecordTypePayload& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.boolean(value.is_union);
    ar.boolean(value.is_incomplete);
}

template <typename Ar>
void io_fields(Ar& ar, EnumTypePayload& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.boolean(value.is_scoped);
    ar.boolean(value.is_incomplete);
    ar.boolean(value.has_fixed_underlying_type);
    ar.type_ref(value.underlying_type);
}

template <typename Ar>
void io_fields(Ar& ar, VectorTypePayload& value) {
    ar.type_ref(value.element_type);
    ar.u32(value.element_count);
    ar.u64(value.size_bytes);
}

template <typename Ar>
void io_fields(Ar& ar, ComplexTypePayload& value) {
    ar.type_ref(value.element_type);
}

template <typename Ar>
void io_fields(Ar& ar, BitIntTypePayload& value) {
    ar.u32(value.bits);
    ar.boolean(value.is_unsigned);
}

template <typename Ar>
void io_fields(Ar& ar, TypedefTypePayload& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.type_ref(value.underlying_type);
}

template <typename Ar>
void io_fields(Ar& ar, TypeParamTypePayload& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.u32(value.depth);
    ar.u32(value.index);
    ar.boolean(value.is_parameter_pack);
}

template <typename Ar>
void io_fields(Ar& ar, TemplateSpecializationTypePayload& value) {
    ar.id(value.template_name);
    ar.id(value.primary_template);
    ar.vector(value.arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
    ar.value_expression(value.splice_operand);
    ar.boolean(value.is_dependent);
    ar.boolean(value.is_class_template_placeholder);
}

template <typename Ar>
void io_fields(Ar& ar, AliasSpecializationTypePayload& value) {
    ar.id(value.template_name);
    ar.id(value.alias_template);
    ar.vector(value.arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
    ar.type_ref(value.associated_type);
}

template <typename Ar>
void io_fields(Ar& ar, DependentNameTypePayload& value) {
    ar.type_ref(value.qualifier_type);
    ar.id(value.member_name);
    ar.vector(value.template_arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
    ar.boolean(value.is_current_instantiation);
}

template <typename Ar>
void io_fields(Ar& ar, DependentTypePayload& value) {
    ar.id(value.debug_name);
}

template <typename Ar>
void io_fields(Ar&, PlaceholderTypePayload&) {}

template <typename Ar>
void io_fields(Ar& ar, AutoTypePayload& value) {
    ar.enum32(value.flavor);
}

template <typename Ar>
void io_fields(Ar& ar, TypeofExprTypePayload& value) {
    ar.id(value.expr);
}

template <typename Ar>
void io_fields(Ar& ar, DecltypeExprTypePayload& value) {
    ar.id(value.expr);
    ar.boolean(value.use_declared_type_rule);
    ar.enum32(value.operand_category);
    ar.type_ref(value.operand_type);
    ar.type_ref(value.dependent_value_qualifier);
    ar.id(value.dependent_value_name);
    ar.value_expression(value.operand_expression);
}

template <typename Ar>
void io_fields(Ar& ar, BuiltinTypeTransformTypePayload& value) {
    ar.enum32(value.transform_kind);
    ar.type_ref(value.operand_type);
}

template <typename Ar>
void io_fields(Ar& ar, BuiltinPackElementTypePayload& value) {
    ar.vector(value.arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
}

template <typename Ar>
void io_fields(Ar& ar, PackIndexTypePayload& value) {
    ar.type_ref(value.pack_type);
    ar.value_expression(value.index_expression);
    ar.vector(value.expansions,
              [](auto& a, auto& expansion) { a.type_ref(expansion); });
    ar.boolean(value.fully_substituted);
}

template <typename Ar>
void io_fields(Ar& ar, PlaceTypePayload& value) {
    ar.type_ref(value.object_type);
}

template <typename Ar>
void io_type_payload(Ar& ar, TypePayload& payload) {
    io_variant(ar, payload,
               [](auto& a, auto& alternative) { io_fields(a, alternative); });
}

template <typename Ar>
void io_fields(Ar& ar, Type& value) {
    ar.enum32(value.kind);
    ar.u32(value.payload_index);
    ar.id(value.canonical);
    ar.id(value.desugared);
    ar.id(value.resolved);
    ar.u32(value.dependency.flags);
    ar.id(value.debug_name);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, ConstantStateSubobject& value) {
    ar.id(value.entity);
    ar.u64(value.array_index);
    ar.boolean(value.is_array_element);
}

template <typename Ar>
void io_fields(Ar& ar, ConstantStateFact& value) {
    ar.enum32(value.kind);
    ar.enum32(value.lifetime);
    ar.type_ref(value.type);
    ar.boolean(value.initialized);
    io_fields(ar, value.integer_value);
    ar.boolean(value.boolean_value);
    ar.floating(value.floating_value);
    ar.floating(value.floating_real);
    ar.floating(value.floating_imag);
    io_fields(ar, value.complex_integer_real);
    io_fields(ar, value.complex_integer_imag);
    ar.boolean(value.complex_is_integer);
    ar.enum32(value.null_kind);
    ar.id(value.address_entity);
    ar.id(value.address_string_literal);
    ar.i64(value.address_byte_offset);
    ar.vector(value.address_subobjects,
              [](auto& a, auto& step) { io_fields(a, step); });
    ar.id(value.member_entity);
    ar.i64(value.member_byte_offset);
    ar.i32(value.member_virtual_slot);
    ar.boolean(value.member_is_function);
    ar.id(value.subobject_entity);
    ar.u64(value.subobject_index);
    ar.id(value.active_union_member);
    ar.id(value.closure_identity);
    ar.vector(value.elements,
              [](auto& a, auto& element) { io_fields(a, element); });
}

template <typename Ar>
void io_fields(Ar& ar, OperatorFunctionIdentity& value) {
    ar.enum32(value.kind);
    ar.enum32(value.spelling);
    ar.type_ref(value.conversion_type);
    ar.id(value.literal_suffix);
}

template <typename Ar>
void io_fields(Ar& ar, DeclSemanticFlags& value) {
    ar.boolean(value.is_constexpr);
    ar.boolean(value.is_consteval);
    ar.boolean(value.is_constinit);
    ar.boolean(value.is_inline);
    ar.boolean(value.is_thread_local);
    ar.boolean(value.is_register);
}

template <typename Ar>
void io_fields(Ar& ar, EntityAttributeFacts& value) {
    ar.vector(value.retained,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
    ar.size(value.requested_alignment);
    ar.str(value.section);
    ar.str(value.visibility);
    ar.str(value.asm_label);
    ar.boolean(value.is_named_register);
    ar.str(value.weakref_target);
    ar.str(value.alias_target);
    ar.str(value.ifunc_target);
    ar.str(value.deprecated_message);
    ar.vector(value.nonnull_params,
              [](auto& a, auto& parameter) { a.u32(parameter); });
    ar.int_value(value.constructor_priority);
    ar.int_value(value.destructor_priority);
    ar.boolean(value.is_weak);
    ar.boolean(value.is_common);
    ar.boolean(value.is_used);
    ar.boolean(value.is_unused);
    ar.boolean(value.is_deprecated);
    ar.boolean(value.is_nodiscard);
    ar.boolean(value.is_warn_unused_result);
    ar.boolean(value.is_noreturn);
    ar.boolean(value.is_gnu_inline);
    ar.boolean(value.is_noinline);
    ar.boolean(value.is_always_inline);
    ar.boolean(value.is_excluded_from_explicit_instantiation);
    ar.boolean(value.is_cold);
    ar.boolean(value.is_hot);
    ar.boolean(value.is_nothrow);
    ar.boolean(value.is_pure);
    ar.boolean(value.is_const_function);
    ar.boolean(value.is_malloc);
    ar.boolean(value.returns_nonnull);
    ar.boolean(value.nonnull_all_pointer_params);
    ar.boolean(value.has_format);
}

template <typename Ar>
void io_fields(Ar& ar, SymbolPolicy& value) {
    ar.enum32(value.name_linkage);
    ar.enum32(value.name_language);
    ar.enum32(value.type_language);
    ar.enum32(value.emission);
    ar.enum32(value.definition_emission);
    ar.enum32(value.visibility);
    ar.id(value.semantic_owner);
    ar.id(value.abi_owner);
    ar.id(value.comdat_key);
    ar.id(value.module_attachment);
    ar.enum32(value.generated_role);
    ar.boolean(value.imported_definition);
    ar.boolean(value.finalized);
}

template <typename Ar>
void io_fields(Ar& ar, StaticInitializerRelocation& value) {
    ar.size(value.offset);
    ar.id(value.entity);
    ar.i64(value.addend);
    ar.id(value.block);
    ar.id(value.subtract_block);
}

template <typename Ar>
void io_fields(Ar& ar, Entity& value) {
    ar.enum32(value.kind);
    ar.id(value.name);
    ar.id(value.unnamed_type_linkage_name);
    ar.u32(value.unnamed_type_ordinal);
    ar.id(value.type);
    ar.id(value.parent);
    io_fields(ar, value.operator_function);
    ar.id(value.declaring_record);
    ar.enum32(value.declared_member_access);
    ar.boolean(value.is_record_member);
    ar.boolean(value.is_static_member_function);
    ar.id(value.lexical_context);
    ar.id(value.semantic_context);
    ar.id(value.namespace_alias_target);
    ar.boolean(value.namespace_alias_is_dependent);
    ar.id(value.owning_function);
    ar.id(value.structured_binding_backing);
    ar.u32(value.structured_binding_index);
    ar.id(value.local_source_name);
    ar.id(value.local_enclosing_function);
    ar.u32(value.local_name_ordinal);
    ar.enum32(value.local_name_kind);
    ar.u32(value.local_component_ordinal);
    ar.enum32(value.storage_duration);
    ar.enum32(value.memory_space);
    ar.enum32(value.linkage);
    io_fields(ar, value.symbol_policy);
    ar.enum32(value.abi_identity);
    ar.id(value.abi_owner);
    ar.enum32(value.generated_symbol_role);
    ar.id(value.module_attachment);
    ar.id(value.origin_unit);
    ar.enum32(value.origin_fragment);
    ar.boolean(value.is_module_exported);
    ar.id(value.linkage_predecessor);
    ar.id(value.placeholder_result);
    ar.enum32(value.object_origin);
    ar.id(value.object_storage_alias);
    ar.id(value.object_storage_alias_place);
    ar.boolean(value.is_function_result_object);
    ar.boolean(value.is_exception_declaration);
    ar.boolean(value.is_parameter_argument_object);
    ar.u8(value.qualifiers);
    io_fields(ar, value.decl_flags);
    io_fields(ar, value.attr_facts);
    ar.boolean(value.is_definition);
    ar.boolean(value.has_deferred_definition);
    ar.boolean(value.is_deleted);
    ar.boolean(value.is_unnamed_record);
    ar.boolean(value.inline_definition_only);
    ar.boolean(value.declared_with_extern);
    ar.boolean(value.is_extern_c);
    ar.boolean(value.is_block_byref);
    ar.boolean(value.is_template_pattern);
    ar.boolean(value.result_type_only_definition);
    ar.boolean(value.suppressed_by_explicit_instantiation_declaration);
    ar.boolean(value.suppressed_as_unselected_template_candidate);
    ar.boolean(value.is_explicit_instantiation_definition);
    ar.boolean(value.is_explicit_template_specialization);
    ar.boolean(value.has_static_initializer);
    ar.boolean(value.has_initializer);
    ar.boolean(value.initializer_is_value_dependent);
    ar.vector(value.static_initializer_bytes,
              [](auto& a, auto& byte) { a.u8(byte); });
    ar.vector(value.static_initializer_relocations,
              [](auto& a, auto& relocation) { io_fields(a, relocation); });
    ar.boolean(value.has_constant_value);
    ar.enum32(value.constant_value_kind);
    ar.enum32(value.constant_null_kind);
    io_fields(ar, value.constant_integer_value);
    ar.floating(value.constant_floating_value);
    ar.id(value.constant_entity);
    ar.id(value.constant_closure_identity);
    ar.enum32(value.constant_meta_kind);
    ar.type_ref(value.constant_meta_type);
    ar.i64(value.constant_byte_offset);
    ar.vector(value.constant_value_elements,
              [](auto& a, auto& element) { a.template_argument(element); });
    ar.id(value.constant_state);
    ar.id(value.template_parameter_object);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, MemberUsingOrigin& value) {
    ar.id(value.entity);
    ar.id(value.importing_record);
    ar.id(value.nominated_record);
    ar.u32(value.using_fact_index);
    ar.enum32(value.declared_access);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, Binding& value) {
    ar.id(value.name);
    ar.id(value.context);
    ar.enum32(value.lookup_namespace);
    ar.vector(value.entities, [](auto& a, auto& entity) { a.id(entity); });
    ar.vector(value.entity_generations,
              [](auto& a, auto& generation) { a.u64(generation); });
    ar.vector(value.member_using_origins,
              [](auto& a, auto& origin) { io_fields(a, origin); });
    ar.type_ref(value.type);
    ar.id(value.place);
    ar.boolean(value.is_type_name);
    ar.boolean(value.is_template_name);
    ar.boolean(value.dependent_member_using);
    ar.boolean(value.is_definition);
    ar.boolean(value.has_block_scope_function_declaration);
    ar.u64(value.generation);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, DeclContext& value) {
    ar.enum32(value.kind);
    ar.id(value.owner);
    ar.id(value.parent);
    ar.vector(value.children, [](auto& a, auto& child) { a.id(child); });
    ar.vector(value.bindings, [](auto& a, auto& binding) { a.id(binding); });
    auto binding_entry = [](auto& a, auto& binding) { a.id(binding); };
    io_u64_map(ar, value.ordinary_latest_bindings, binding_entry);
    io_u64_map(ar, value.ordinary_value_bindings, binding_entry);
    io_u64_map(ar, value.ordinary_callable_bindings, binding_entry);
    io_u64_map(ar, value.ordinary_type_name_bindings, binding_entry);
    io_u64_map(ar, value.ordinary_template_name_bindings, binding_entry);
    io_u64_map(ar, value.ordinary_namespace_bindings, binding_entry);
    io_u64_map(ar, value.tag_bindings, binding_entry);
    io_u64_map(ar, value.label_bindings, binding_entry);
    ar.vector(value.using_directives,
              [](auto& a, auto& directive) { a.id(directive); });
    ar.vector(value.using_directive_origins,
              [](auto& a, auto& origin) { a.id(origin); });
    ar.boolean(value.is_inline_namespace);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, RecordDefinitionData& value) {
    ar.boolean(value.has_user_declared_constructor);
    ar.boolean(value.has_inherited_constructor);
    ar.boolean(value.has_default_constructor);
    ar.boolean(value.default_constructor_is_deleted);
    ar.boolean(value.has_copy_constructor);
    ar.boolean(value.has_move_constructor);
    ar.boolean(value.has_user_declared_copy_constructor);
    ar.boolean(value.has_user_declared_move_constructor);
    ar.boolean(value.has_copy_assignment);
    ar.boolean(value.has_move_assignment);
    ar.boolean(value.has_user_declared_copy_assignment);
    ar.boolean(value.has_user_declared_move_assignment);
    ar.boolean(value.has_user_declared_destructor);
    ar.boolean(value.has_deleted_destructor);
}

template <typename Ar>
void io_fields(Ar& ar, RecordFieldFact& value) {
    ar.id(value.name);
    ar.id(value.entity);
    ar.type_ref(value.type);
    ar.id(value.lambda_capture_source);
    ar.enum32(value.lambda_capture_kind);
    ar.enum32(value.declared_access);
    ar.size(value.offset);
    ar.size(value.forced_alignment);
    ar.size(value.storage_size_override);
    ar.size(value.storage_alignment_override);
    ar.boolean(value.is_bitfield);
    ar.boolean(value.is_flexible_array_member);
    ar.u32(value.bit_offset);
    ar.u32(value.bit_width);
    ar.value_expression(value.bit_width_expression);
    ar.boolean(value.bit_width_is_dependent);
    ar.u32(value.storage_size);
    ar.boolean(value.is_mutable);
    ar.boolean(value.is_anonymous_union_object);
    ar.boolean(value.is_base_subobject);
    ar.boolean(value.is_virtual_base_storage);
    ar.boolean(value.is_no_unique_address);
    ar.boolean(value.is_potentially_overlapping);
    ar.enum32(value.subobject_size);
    ar.boolean(value.has_default_member_initializer);
    ar.boolean(value.default_member_initializer_braced);
    ar.u32(value.default_member_initializer_begin);
    ar.u32(value.default_member_initializer_end);
    ar.srcloc(value.default_member_initializer_loc);
    ar.id(value.default_member_initializer_context);
    ar.u64(value.default_member_initializer_lookup_generation);
    ar.boolean(value.default_member_initializer_potentially_throwing);
    ar.boolean(value.default_member_initializer_throwing_dependent);
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
}

template <typename Ar>
void io_fields(Ar& ar, RecordBaseFact& value) {
    ar.id(value.name);
    ar.type_ref(value.type);
    ar.enum32(value.declared_access);
    ar.id(value.record_entity);
    ar.boolean(value.is_virtual);
    ar.boolean(value.has_non_virtual_offset);
    ar.size(value.non_virtual_offset);
    ar.u32(value.declaration_index);
}

template <typename Ar>
void io_fields(Ar& ar, RecordDependentBaseFact& value) {
    ar.type_ref(value.type);
    ar.enum32(value.declared_access);
    ar.boolean(value.is_virtual);
    ar.u32(value.declaration_index);
}

template <typename Ar>
void io_fields(Ar& ar, VirtualSubobjectFact& value) {
    ar.u32(value.id);
    ar.id(value.record_entity);
    ar.type_ref(value.type);
    ar.vector(value.storage_path, [](auto& a, auto& step) { a.id(step); });
    ar.size(value.static_offset_bytes);
    ar.boolean(value.is_virtual);
}

template <typename Ar>
void io_fields(Ar& ar, VirtualSubobjectEdgeFact& value) {
    ar.u32(value.derived_subobject);
    ar.u32(value.base_subobject);
    ar.enum32(value.declared_access);
    ar.u32(value.declaration_index);
    ar.boolean(value.is_virtual);
}

template <typename Ar>
void io_fields(Ar& ar, VirtualOverrideEdgeFact& value) {
    ar.id(value.overriding);
    ar.id(value.overridden);
    ar.u32(value.overriding_subobject);
    ar.u32(value.overridden_subobject);
    ar.enum32(value.return_relation);
    ar.vector(value.covariance_path, [](auto& a, auto& step) { a.id(step); });
    ar.boolean(value.predicate_dependent);
}

template <typename Ar>
void io_fields(Ar& ar, VirtualFinalOverriderFact& value) {
    ar.id(value.virtual_declaration);
    ar.u32(value.declaration_subobject);
    ar.id(value.final_overrider);
    ar.u32(value.final_subobject);
    ar.vector(value.conflict_candidates,
              [](auto& a, auto& candidate) { a.id(candidate); });
}

template <typename Ar>
void io_fields(Ar& ar, VirtualAdjustmentFact& value) {
    ar.enum32(value.kind);
    ar.i64(value.static_offset_bytes);
    ar.i64(value.vtable_offset_bytes);
    ar.vector(value.path, [](auto& a, auto& step) { a.id(step); });
}

template <typename Ar>
void io_fields(Ar& ar, VirtualTableSlotFact& value) {
    ar.id(value.declaration);
    ar.id(value.final_overrider);
    ar.u32(value.declaration_subobject);
    ar.u32(value.final_subobject);
    io_fields(ar, value.this_adjustment);
    io_fields(ar, value.result_adjustment);
    ar.boolean(value.is_deleting_destructor);
    ar.boolean(value.runtime_callable);
}

template <typename Ar>
void io_fields(Ar& ar, PotentiallyConstructedSubobjectFact& value) {
    ar.enum32(value.kind);
    ar.id(value.entity);
    ar.type_ref(value.type);
}

template <typename Ar>
void io_fields(Ar& ar, DeallocationFunctionForm& value) {
    ar.boolean(value.is_array);
    ar.boolean(value.is_placement);
    ar.boolean(value.is_sized);
    ar.boolean(value.is_aligned);
    ar.boolean(value.is_destroying);
}

template <typename Ar>
void io_fields(Ar& ar, DeallocationFunctionSelectionFact& value) {
    ar.id(value.entity);
    io_fields(ar, value.form);
}

template <typename Ar>
void io_fields(Ar& ar, InheritedConstructorRouteFact& value) {
    ar.id(value.nominated_direct_base);
    ar.u32(value.origin_subobject);
    ar.srcloc(value.using_loc);
}

template <typename Ar>
void io_fields(Ar& ar, InheritedConstructorFact& value) {
    ar.id(value.origin_constructor);
    ar.id(value.origin_record);
    ar.vector(value.routes, [](auto& a, auto& route) { io_fields(a, route); });
}

template <typename Ar>
void io_fields(Ar& ar, ConstructorDelegationFact& value) {
    ar.enum32(value.state);
    ar.enum32(value.initialization_kind);
    ar.id(value.target_constructor);
    ar.srcloc(value.initializer_loc);
}

template <typename Ar>
void io_fields(Ar& ar, FunctionParameterScopeFact& value) {
    ar.id(value.name);
    ar.type_ref(value.type);
    ar.srcloc(value.loc);
    ar.boolean(value.is_parameter_pack);
    ar.id(value.source_parameter_pack_name);
    ar.boolean(value.is_parameter_pack_expansion_sentinel);
    ar.boolean(value.type_originates_from_template_parameter);
}

template <typename Ar>
void io_fields(Ar& ar, RecordMethodFact& value) {
    ar.id(value.name);
    ar.type_ref(value.type);
    ar.enum32(value.declared_access);
    ar.id(value.entity);
    io_fields(ar, value.operator_function);
    ar.boolean(value.is_static);
    ar.boolean(value.is_function_template);
    ar.boolean(value.is_conversion_function);
    ar.boolean(value.is_virtual);
    ar.boolean(value.is_override);
    ar.boolean(value.overrides_base);
    ar.boolean(value.is_final);
    ar.boolean(value.is_deleted);
    ar.boolean(value.is_defaulted);
    ar.boolean(value.is_pure);
    ar.boolean(value.is_constexpr);
    ar.boolean(value.is_consteval);
    ar.boolean(value.has_explicit_exception_spec);
    ar.boolean(value.has_deferred_noexcept_operand);
    ar.u32(value.noexcept_operand_begin);
    ar.u32(value.noexcept_operand_end);
    ar.srcloc(value.noexcept_operand_loc);
    ar.id(value.noexcept_declaration_context);
    ar.u64(value.noexcept_lookup_generation);
    ar.vector(value.declarator_parameters,
              [](auto& a, auto& parameter) { io_fields(a, parameter); });
    ar.boolean(value.is_selected_destructor);
    ar.boolean(value.is_explicit);
    ar.enum32(value.special_member_kind);
    ar.boolean(value.is_implicitly_declared);
    ar.id(value.implicit_equality_origin);
    ar.boolean(value.is_user_provided);
    ar.boolean(value.is_key_function_candidate);
    ar.boolean(value.is_eligible);
    ar.boolean(value.is_trivial);
    ar.boolean(value.has_computed_exception_spec);
    ar.vector(value.potentially_constructed_subobjects,
              [](auto& a, auto& subobject) { io_fields(a, subobject); });
    ar.enum32(value.explicit_specifier);
    ar.size(value.explicit_expression_begin);
    ar.size(value.explicit_expression_end);
    ar.value_expression(value.explicit_value_expression);
    ar.id(value.explicit_declaration_context);
    ar.u64(value.explicit_lookup_generation);
    ar.enum32(value.constraint_satisfaction);
    ar.u64(value.associated_constraint_fingerprint);
    ar.vector(value.more_constrained_than,
              [](auto& a, auto& fingerprint) { a.u64(fingerprint); });
    ar.srcloc(value.first_required_loc);
    ar.u64(value.first_required_lookup_generation);
    ar.i32(value.vtable_slot);
    io_fields(ar, value.deleting_destructor_deallocation);
    io_optional(ar, value.inherited_constructor,
                [](auto& a, auto& fact) { io_fields(a, fact); });
    io_optional(ar, value.constructor_delegation,
                [](auto& a, auto& fact) { io_fields(a, fact); });
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
}

template <typename Ar>
void io_fields(Ar& ar, RecordStaticDataMemberFact& value) {
    ar.id(value.name);
    ar.type_ref(value.type);
    ar.enum32(value.declared_access);
    ar.id(value.entity);
    ar.boolean(value.is_constexpr);
    ar.boolean(value.is_consteval);
    ar.boolean(value.is_inline);
    ar.boolean(value.has_in_class_initializer);
    ar.size(value.initializer_begin);
    ar.size(value.initializer_end);
    ar.srcloc(value.initializer_loc);
    ar.id(value.initializer_context);
    ar.u64(value.initializer_lookup_generation);
    ar.value_expression(value.initializer_value_expression);
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
}

template <typename Ar>
void io_fields(Ar& ar, AnonymousUnionPromotionFact& value) {
    ar.id(value.name);
    ar.id(value.member);
    ar.vector(value.path, [](auto& a, auto& step) { a.id(step); });
}

template <typename Ar>
void io_fields(Ar& ar, VariantMemberFact& value) {
    ar.id(value.member);
    ar.id(value.owning_union);
    ar.vector(value.path, [](auto& a, auto& step) { a.id(step); });
}

template <typename Ar>
void io_fields(Ar& ar, RecordUsingDeclarationEntry& value) {
    ar.id(value.entity);
    ar.id(value.hidden_by);
}

template <typename Ar>
void io_fields(Ar& ar, RecordUsingDeclarationFact& value) {
    ar.id(value.terminal_name);
    ar.id(value.nominated_entity);
    ar.type_ref(value.dependent_qualifier);
    ar.enum32(value.declared_access);
    ar.vector(value.entries, [](auto& a, auto& entry) { io_fields(a, entry); });
    ar.boolean(value.uses_typename);
    ar.boolean(value.base_validation_deferred);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, RecordInheritedConstructorNominationFact& value) {
    ar.id(value.nominated_record);
    ar.type_ref(value.dependent_qualifier);
    ar.boolean(value.base_validation_deferred);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, RecordClassFriendGrant& value) {
    ar.enum32(value.kind);
    ar.enum32(value.recipe_kind);
    ar.id(value.entity);
    ar.type_ref(value.type_pattern);
    ar.id(value.member_name);
    ar.vector(value.required_type_params,
              [](auto& a, auto& param) { a.u32(param); });
    ar.vector(value.required_value_params,
              [](auto& a, auto& param) { a.u32(param); });
    ar.vector(value.required_template_params,
              [](auto& a, auto& param) { a.u32(param); });
    ar.boolean(value.is_pack_expansion);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, TemplateParameterPattern& value) {
    ar.enum32(value.kind);
    ar.boolean(value.is_parameter_pack);
    ar.id(value.type_param_type);
    ar.type_ref(value.non_type_type);
    ar.vector(value.template_parameters,
              [](auto& a, auto& parameter) { io_fields(a, parameter); });
}

template <typename Ar>
void io_fields(Ar& ar, RecordFunctionFriendGrant& value) {
    ar.enum32(value.kind);
    ar.id(value.entity);
    ar.id(value.context);
    ar.id(value.module_attachment);
    ar.id(value.signature_owner);
    ar.id(value.name);
    ar.type_ref(value.type_pattern);
    ar.vector(value.arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
    ar.type_ref(value.qualifier_pattern);
    ar.id(value.member_name);
    ar.vector(value.member_template_parameters,
              [](auto& a, auto& parameter) { io_fields(a, parameter); });
    ar.vector(value.required_type_params,
              [](auto& a, auto& param) { a.u32(param); });
    ar.vector(value.required_value_params,
              [](auto& a, auto& param) { a.u32(param); });
    ar.vector(value.required_template_params,
              [](auto& a, auto& param) { a.u32(param); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, RecordFacts::SecondaryVtable& value) {
    ar.id(value.base_field);
    ar.vector(value.storage_path, [](auto& a, auto& step) { a.id(step); });
    ar.size(value.base_offset_bytes);
    ar.size(value.address_point_bytes);
    ar.type_ref(value.base_type);
    ar.boolean(value.is_virtual);
    ar.vector(value.slots, [](auto& a, auto& slot) { a.id(slot); });
    ar.vector(value.slot_facts,
              [](auto& a, auto& fact) { io_fields(a, fact); });
}

template <typename Ar>
void io_fields(Ar& ar, RecordFacts::VirtualBase& value) {
    ar.id(value.record_entity);
    ar.type_ref(value.type);
    ar.id(value.storage_field);
    ar.size(value.storage_offset_bytes);
    ar.size(value.vtable_index);
}

template <typename Ar>
void io_fields(Ar& ar, RecordFacts& value) {
    ar.id(value.entity);
    ar.type_ref(value.type);
    ar.enum32(value.kind);
    ar.boolean(value.is_incomplete);
    ar.boolean(value.is_template_pattern_provisional);
    ar.boolean(value.is_final);
    ar.boolean(value.is_polymorphic);
    ar.boolean(value.is_abstract);
    ar.enum32(value.is_consteval_only);
    ar.boolean(value.is_literal_class_type);
    ar.enum32(value.is_aggregate);
    ar.enum32(value.is_trivial);
    ar.enum32(value.is_trivially_copyable);
    ar.enum32(value.is_empty);
    ar.enum32(value.is_standard_layout);
    ar.enum32(value.is_implicit_lifetime);
    ar.boolean(value.is_non_trivial_for_calls);
    ar.boolean(value.has_virtual_destructor);
    ar.boolean(value.is_packed);
    ar.boolean(value.is_transparent_union);
    ar.boolean(value.has_flexible_array_member);
    ar.boolean(value.is_lambda_closure);
    ar.boolean(value.lambda_has_capture);
    ar.id(value.closure_identity);
    ar.size(value.requested_alignment);
    ar.size(value.pack_alignment);
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
    io_fields(ar, value.definition_data);
    ar.vector(value.bases, [](auto& a, auto& base) { io_fields(a, base); });
    ar.vector(value.dependent_bases,
              [](auto& a, auto& base) { io_fields(a, base); });
    ar.vector(value.fields, [](auto& a, auto& field) { io_fields(a, field); });
    ar.enum32(value.anonymous_union_object_kind);
    ar.boolean(value.is_anonymous_union_definition);
    ar.id(value.anonymous_union_object);
    ar.id(value.anonymous_union_parent_context);
    ar.vector(value.anonymous_union_promotions,
              [](auto& a, auto& promotion) { io_fields(a, promotion); });
    ar.boolean(value.is_union_like);
    ar.vector(value.variant_members,
              [](auto& a, auto& member) { io_fields(a, member); });
    ar.vector(value.methods,
              [](auto& a, auto& method) { io_fields(a, method); });
    ar.vector(value.static_data_members,
              [](auto& a, auto& member) { io_fields(a, member); });
    ar.vector(value.using_declarations,
              [](auto& a, auto& fact) { io_fields(a, fact); });
    ar.vector(value.inherited_constructor_nominations,
              [](auto& a, auto& nomination) { io_fields(a, nomination); });
    ar.vector(value.virtual_subobjects,
              [](auto& a, auto& subobject) { io_fields(a, subobject); });
    ar.vector(value.virtual_subobject_edges,
              [](auto& a, auto& edge) { io_fields(a, edge); });
    ar.vector(value.virtual_override_edges,
              [](auto& a, auto& edge) { io_fields(a, edge); });
    ar.vector(value.virtual_final_overriders,
              [](auto& a, auto& overrider) { io_fields(a, overrider); });
    ar.boolean(value.virtual_graph_dependent);
    ar.id(value.key_function);
    ar.vector(value.class_friends,
              [](auto& a, auto& grant) { io_fields(a, grant); });
    ar.vector(value.function_friends,
              [](auto& a, auto& grant) { io_fields(a, grant); });
    ar.vector(value.vtable_slots, [](auto& a, auto& slot) { a.id(slot); });
    ar.vector(value.primary_vtable_slot_facts,
              [](auto& a, auto& fact) { io_fields(a, fact); });
    ar.id(value.vtable_entity);
    ar.id(value.typeinfo_entity);
    ar.id(value.vtt_entity);
    ar.vector(value.secondary_vtables,
              [](auto& a, auto& vtable) { io_fields(a, vtable); });
    ar.vector(value.virtual_bases,
              [](auto& a, auto& base) { io_fields(a, base); });
    ar.size(value.vtable_address_point);
    ar.size(value.non_virtual_size_bits);
    ar.size(value.non_virtual_alignment);
    ar.size(value.size_bits);
    ar.size(value.alignment);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCIvarFact& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.type_ref(value.type);
    ar.enum32(value.access);
    ar.boolean(value.is_bitfield);
    ar.u32(value.bit_width);
    ar.size(value.offset_bytes);
    ar.id(value.offset_variable);
    ar.boolean(value.is_property_backing);
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCMethodFact& value) {
    ar.id(value.entity);
    ar.id(value.selector);
    ar.id(value.function_type);
    ar.type_ref(value.return_type);
    ar.boolean(value.is_class_method);
    ar.boolean(value.is_variadic);
    ar.boolean(value.returns_instancetype);
    ar.enum32(value.family);
    ar.boolean(value.is_optional);
    ar.boolean(value.is_property_accessor);
    ar.id(value.definition);
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCPropertyFact& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.type_ref(value.type);
    ar.enum32(value.ownership);
    ar.boolean(value.is_readonly);
    ar.boolean(value.is_class_property);
    ar.boolean(value.is_nonatomic);
    ar.id(value.getter);
    ar.id(value.setter);
    ar.id(value.getter_method);
    ar.id(value.setter_method);
    ar.id(value.backing_ivar);
    ar.id(value.spelled_backing_name);
    ar.boolean(value.is_dynamic);
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCInterfaceFacts& value) {
    ar.id(value.entity);
    ar.id(value.name);
    ar.id(value.object_type);
    ar.id(value.super_class);
    ar.boolean(value.is_forward_only);
    ar.boolean(value.is_defined);
    ar.vector(value.ivars, [](auto& a, auto& ivar) { io_fields(a, ivar); });
    ar.vector(value.instance_methods,
              [](auto& a, auto& method) { io_fields(a, method); });
    ar.vector(value.class_methods,
              [](auto& a, auto& method) { io_fields(a, method); });
    ar.vector(value.properties,
              [](auto& a, auto& property) { io_fields(a, property); });
    ar.vector(value.protocols, [](auto& a, auto& id) { a.id(id); });
    ar.vector(value.categories, [](auto& a, auto& id) { a.id(id); });
    ar.id(value.implementation);
    ar.id(value.protocol_reference);
    ar.id(value.ehtype);
    ar.size(value.instance_start_bytes);
    ar.size(value.instance_size_bytes);
    ar.boolean(value.layout_computed);
    ar.boolean(value.has_nontrivial_cxx_ivars);
    ar.vector(value.cxx_construct_ivars, [](auto& a, auto& id) { a.id(id); });
    ar.vector(value.attributes,
              [](auto& a, auto& attribute) { io_fields(a, attribute); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, ComparisonSubobjectFact& value) {
    ar.enum32(value.kind);
    ar.id(value.entity);
    ar.type_ref(value.type);
    ar.vector(value.array_extents,
              [](auto& a, auto& extent) { a.size(extent); });
    ar.type_ref(value.array_leaf_type);
    ar.size(value.array_element_count);
    ar.id(value.selected_operator);
    ar.boolean(value.selected_builtin);
    ar.boolean(value.selected_rewritten);
    ar.boolean(value.selected_reversed);
    ar.boolean(value.usable);
}

template <typename Ar>
void io_fields(Ar& ar, DefaultedComparisonFact& value) {
    ar.id(value.function);
    ar.id(value.owner_record);
    ar.enum32(value.kind);
    ar.type_ref(value.result_type);
    ar.id(value.implicit_equality_origin);
    ar.vector(value.subobjects,
              [](auto& a, auto& subobject) { io_fields(a, subobject); });
    ar.boolean(value.is_friend);
    ar.boolean(value.is_implicit_equality);
    ar.boolean(value.is_dependent);
    ar.boolean(value.is_deleted);
    ar.boolean(value.is_constexpr);
    ar.boolean(value.is_noexcept);
    ar.str(value.deletion_reason);
}

template <typename Ar>
void io_fields(Ar& ar, StructuredBindingProjectionFact& value) {
    ar.id(value.binding);
    ar.id(value.holder);
    ar.id(value.member);
    ar.vector(value.base_path, [](auto& a, auto& step) { a.id(step); });
    ar.type_ref(value.type);
    ar.type_ref(value.referenced_type);
    ar.u32(value.index);
    ar.boolean(value.is_bitfield);
    ar.boolean(value.is_pack_element);
    ar.boolean(value.is_dependent);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, StructuredBindingFact& value) {
    ar.id(value.backing);
    ar.type_ref(value.decomposed_type);
    ar.enum32(value.strategy);
    ar.vector(value.source_names, [](auto& a, auto& name) { a.id(name); });
    ar.vector(value.projections,
              [](auto& a, auto& projection) { io_fields(a, projection); });
    ar.boolean(value.has_pack);
    ar.u32(value.pack_position);
    ar.boolean(value.is_condition);
    ar.boolean(value.is_dependent);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, InstantiationDemandFact& value) {
    ar.enum32(value.kind);
    ar.enum32(value.status);
    ar.id(value.subject);
    ar.srcloc(value.first_requirement);
    ar.u64(value.point_lookup_generation);
    ar.u64(value.request_id);
}

template <typename Ar>
void io_fields(Ar& ar, TemplateArgumentBinding& value) {
    ar.enum32(value.kind);
    ar.vector(value.arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
}

template <typename Ar>
void io_fields(Ar& ar, TemplateSpecializationFact& value) {
    ar.id(value.template_entity);
    ar.id(value.selected_template_entity);
    ar.u32(value.template_param_index);
    ar.vector(value.argument_bindings,
              [](auto& a, auto& binding) { io_fields(a, binding); });
    ar.vector(value.selected_argument_bindings,
              [](auto& a, auto& binding) { io_fields(a, binding); });
    ar.vector(value.dependent_arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
    ar.vector(value.selected_dependent_arguments,
              [](auto& a, auto& argument) { a.template_argument(argument); });
    ar.id(value.pattern_type);
    ar.srcloc(value.point_of_instantiation);
    ar.u64(value.point_lookup_generation);
    ar.vector(value.instantiation_demands,
              [](auto& a, auto& demand) { io_fields(a, demand); });
}

template <typename Ar>
void io_fields(Ar& ar, PlaceFact& value) {
    ar.type_ref(value.object_type);
    ar.enum32(value.storage_duration);
    ar.id(value.entity);
    ar.id(value.base);
    ar.id(value.source);
    ar.boolean(value.addressable);
    ar.boolean(value.modifiable);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, PlaceholderResultFact& value) {
    ar.id(value.declared_function_type);
    ar.type_ref(value.declared_return_pattern);
    ar.type_ref(value.candidate);
    ar.type_ref(value.result);
    ar.id(value.defining_entity);
    ar.srcloc(value.declaration_loc);
    ar.srcloc(value.first_return_loc);
    ar.enum32(value.state);
    ar.boolean(value.conflict_diagnosed);
    ar.boolean(value.result_only_materialization);
}

template <typename Ar>
void io_fields(Ar& ar, ClosureIdentityFact& value) {
    ar.srcloc(value.source_loc);
    ar.srcloc(value.key_loc);
    ar.id(value.lexical_owner);
    ar.id(value.abi_context_name);
    ar.id(value.abi_context_decl);
    ar.id(value.record);
    ar.type_ref(value.type);
    ar.id(value.call_operator);
    ar.id(value.invoker);
    ar.enum32(value.abi_context);
    ar.boolean(value.is_structural);
    ar.boolean(value.is_generic);
}

template <typename Ar>
void io_fields(Ar& ar, SwitchCaseRange& value) {
    ar.i64(value.low);
    ar.i64(value.high);
    ar.id(value.target);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, SwitchFact& value) {
    ar.id(value.condition.inst);
    ar.type_ref(value.condition_type);
    ar.id(value.dispatch_block);
    ar.id(value.default_block);
    ar.id(value.end_block);
    ar.vector(value.cases,
              [](auto& a, auto& case_range) { io_fields(a, case_range); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, CoroutineFact& value) {
    ar.id(value.function);
    ar.id(value.promise_type);
    ar.id(value.ramp_return_block);
    ar.id(value.alloc_failure_block);
    ar.id(value.eh_action_block);
    ar.u32(value.suspend_count);
    ar.id(value.frame_record);
    ar.id(value.resume_function);
    ar.id(value.destroy_function);
}

template <typename Ar>
void io_fields(Ar& ar, ModuleUnitFact& value) {
    ar.enum32(value.kind);
    ar.id(value.module_name);
    ar.id(value.partition_name);
    ar.vector(value.direct_imports,
              [](auto& a, auto& import) { a.id(import); });
    ar.vector(value.exported_imports,
              [](auto& a, auto& import) { a.id(import); });
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, File::PreludeMark& value) {
    ar.size(value.entities);
    ar.size(value.decl_contexts);
    ar.size(value.bindings);
}

template <typename Ar>
void io_fields(Ar& ar, File::ModuleGraphRemap& value) {
    ar.u32(value.srcloc_delta);
    ar.id(value.unit);
    auto ids = [](auto& a, auto& id) { a.id(id); };
    ar.vector(value.names, ids);
    ar.vector(value.types, ids);
    ar.vector(value.entities, ids);
    ar.vector(value.contexts, ids);
    ar.vector(value.bindings, ids);
    ar.vector(value.functions, ids);
    ar.vector(value.blocks, ids);
    ar.vector(value.insts, ids);
    ar.vector(value.generics, ids);
    ar.vector(value.specifics, ids);
    ar.vector(value.constant_states, ids);
    ar.vector(value.closure_identities, ids);
    ar.vector(value.place_facts, ids);
    ar.vector(value.inline_asm_payloads, ids);
    ar.vector(value.placeholder_facts, ids);
    ar.vector(value.units, ids);
}

template <typename Ar>
void io_literal_value(Ar& ar, LiteralValue& value) {
    io_variant(ar, value,
               [](auto& a, auto& alternative) { io_fields(a, alternative); });
}

template <typename Ar>
void io_fields(Ar& ar, LiteralPayload& value) {
    io_literal_value(ar, value.value);
    ar.str(value.spelling);
}

template <typename Ar>
void io_fields(Ar& ar, AtomicPayload& value) {
    ar.enum32(value.order);
    ar.enum32(value.failure_order);
    ar.enum32(value.rmw_op);
    ar.boolean(value.is_weak);
}

template <typename Ar>
void io_fields(Ar& ar, UnaryOpDescriptor& value) {
    ar.enum32(value.op);
    ar.type_ref(value.computation_type);
}

template <typename Ar>
void io_fields(Ar& ar, BinaryOpDescriptor& value) {
    ar.enum32(value.op);
    ar.type_ref(value.computation_type);
}

template <typename Ar>
void io_fields(Ar& ar, CastPayload& value) {
    ar.str(value.kind);
}

template <typename Ar>
void io_fields(Ar& ar, CallPayload& value) {
    ar.id(value.virtual_declaration);
    ar.boolean(value.must_tail);
}

template <typename Ar>
void io_fields(Ar& ar, BuiltinCallPayload& value) {
    ar.enum32(value.kind);
    ar.str(value.name);
    ar.type_ref(value.type_operand);
    ar.vector(value.integer_operands,
              [](auto& a, auto& operand) { a.i64(operand); });
}

template <typename Ar>
void io_fields(Ar& ar, ReflectPayload& value) {
    ar.enum32(value.kind);
}

template <typename Ar>
void io_fields(Ar& ar, LabelAddressPayload& value) {
    ar.id(value.name);
    ar.id(value.target);
}

template <typename Ar>
void io_fields(Ar& ar, SwitchTerminatorPayload& value) {
    ar.type_ref(value.condition_type);
    ar.vector(value.cases,
              [](auto& a, auto& case_range) { io_fields(a, case_range); });
}

template <typename Ar>
void io_fields(Ar& ar, InlineAsmPayloadRef& value) {
    ar.id(value.payload);
}

template <typename Ar>
void io_fields(Ar& ar, ErrorPayload& value) {
    ar.str(value.message);
}

template <typename Ar>
void io_fields(Ar& ar, DependentRegionPayload& value) {
    ar.u32(value.hole);
    ar.str(value.display);
}

template <typename Ar>
void io_fields(Ar& ar, EhLandingPadPayload& value) {
    ar.boolean(value.is_cleanup);
    ar.boolean(value.has_catch_all);
    ar.vector(value.clause_typeinfos,
              [](auto& a, auto& clause) { a.id(clause); });
}

template <typename Ar>
void io_fields(Ar& ar, CoroSuspendPayload& value) {
    ar.u32(value.index);
    ar.enum32(value.kind);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCMessageSendPayload& value) {
    ar.id(value.selector);
    ar.id(value.method_declaration);
    ar.id(value.interface_context);
    ar.enum32(value.receiver_kind);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCSelectorLiteralPayload& value) {
    ar.id(value.selector);
}

template <typename Ar>
void io_fields(Ar& ar, ObjCArcOpPayload& value) {
    ar.enum32(value.op);
}

template <typename Ar>
void io_inst_payload(Ar& ar, InstPayload& payload) {
    io_variant(ar, payload,
               [](auto& a, auto& alternative) { io_fields(a, alternative); });
}

template <typename Ar>
void io_fields(Ar& ar, InlineAsmOperandPayload& value) {
    ar.id(value.symbolic_name);
    ar.str(value.constraint);
    ar.boolean(value.is_output);
    ar.str(value.register_binding);
}

template <typename Ar>
void io_fields(Ar& ar, InlineAsmPayload& value) {
    ar.str(value.asm_string);
    ar.str(value.constraints);
    ar.vector(value.outputs,
              [](auto& a, auto& operand) { io_fields(a, operand); });
    ar.vector(value.inputs,
              [](auto& a, auto& operand) { io_fields(a, operand); });
    ar.vector(value.clobbers, [](auto& a, auto& clobber) { a.str(clobber); });
    ar.vector(value.goto_labels, [](auto& a, auto& label) { a.id(label); });
    ar.vector(value.goto_targets, [](auto& a, auto& target) { a.id(target); });
    ar.boolean(value.has_side_effects);
    ar.boolean(value.is_inline);
    ar.boolean(value.is_goto);
    ar.boolean(value.align_stack);
    ar.boolean(value.intel_dialect);
}

template <typename Ar>
void io_operand_range(Ar& ar, OperandRange& value) {
    ar.u32(value.first);
    ar.u32(value.count);
}

template <typename Ar>
void io_fields(Ar& ar, Inst& value) {
    ar.enum32(value.kind);
    ar.id(value.result_type);
    ar.id(value.place_fact);
    io_operand_range(ar, value.operands);
    ar.u32(value.payload_index);
    ar.id(value.result_object_entity);
    ar.boolean(value.runtime_elided_object_operation);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, Operand& value) {
    ar.enum32(value.kind);
    io_variant(ar, value.data,
               [](auto& a, auto& alternative) { io_fields(a, alternative); });
}

template <typename Ar>
void io_fields(Ar& ar, Terminator& value) {
    ar.enum32(value.kind);
    io_operand_range(ar, value.operands);
    ar.id(value.target);
    ar.id(value.false_target);
    ar.u32(value.payload_index);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, Block& value) {
    ar.id(value.name);
    ar.vector(value.parameters,
              [](auto& a, auto& parameter) { a.id(parameter); });
    ar.vector(value.instructions, [](auto& a, auto& inst) { a.id(inst); });
    io_fields(ar, value.terminator);
    ar.id(value.unwind_target);
}

template <typename Ar>
void io_fields(Ar& ar, FunctionParameter& value) {
    ar.id(value.entity);
    ar.id(value.value.inst);
}

template <typename Ar>
void io_fields(Ar& ar, Function& value) {
    ar.id(value.entity);
    ar.id(value.type);
    ar.id(value.result_type);
    ar.enum32(value.execution_space);
    ar.vector(value.parameters,
              [](auto& a, auto& parameter) { io_fields(a, parameter); });
    ar.vector(value.blocks, [](auto& a, auto& block) { a.id(block); });
    ar.id(value.entry_block);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_fields(Ar& ar, Generic& value) {
    ar.id(value.entity);
    ar.srcloc(value.loc);
    ar.vector(value.parameters,
              [](auto& a, auto& parameter) { a.id(parameter); });
    ar.id(value.pattern_function);
}

template <typename Ar>
void io_fields(Ar& ar, Specific& value) {
    ar.id(value.generic);
    ar.id(value.function);
    ar.id(value.entity);
    ar.srcloc(value.loc);
}

template <typename Ar>
void io_diagnostics(Ar& ar,
                    std::vector<std::pair<SrcLoc, std::string>>& values) {
    ar.vector(values, [](auto& a, auto& entry) {
        a.srcloc(entry.first);
        a.str(entry.second);
    });
}

} // namespace

struct ModuleGraphSerializer {
    static bool serializable(const File& file) {
        return file.errors_.empty();
    }

    static void rebuild_name_index(File& file) {
        file.name_index_.clear();
        for (uint32_t index = 1; index < file.names_.size(); ++index) {
            uint32_t generation = index < file.name_generations_.size()
                                      ? file.name_generations_[index]
                                      : 0;
            file.name_index_.emplace(file.names_[index],
                                     NameId{index, generation});
        }
    }

    template <typename Ar>
    static void io(Ar& ar, File& file) {
        auto u32s = [](auto& a, auto& value) { a.u32(value); };
        auto strs = [](auto& a, auto& value) { a.str(value); };
        auto structs = [](auto& a, auto& value) { io_fields(a, value); };

        ar.vector(file.names_, strs);
        ar.vector(file.name_generations_, u32s);

        ar.vector(file.types_, structs);
        ar.vector(file.type_generations_, u32s);
        ar.vector(file.type_payloads_,
                  [](auto& a, auto& payload) { io_type_payload(a, payload); });
        io_u64_id_multimap(ar, file.type_index_);
#ifdef ABURI_VERIFY_TYPE_INTERN
        io_string_map(ar, file.verify_type_index_,
                      [](auto& a, auto& type) { a.id(type); });
#endif
        io_builtin_type_map(ar, file.builtin_types_);

        ar.vector(file.entities_, structs);
        ar.vector(file.entity_generations_, u32s);
        io_u64_map(ar, file.record_facts_, structs);
        io_u64_map(ar, file.objc_interface_facts_, structs);
        io_u64_map(ar, file.defaulted_comparison_facts_, structs);
        io_u64_map(ar, file.structured_binding_facts_, structs);
        io_u64_map(ar, file.template_specializations_, structs);

        ar.vector(file.decl_contexts_, structs);
        ar.vector(file.decl_context_generations_, u32s);
        ar.vector(file.bindings_, structs);
        ar.vector(file.binding_generations_, u32s);

        ar.vector(file.place_facts_, structs);
        ar.vector(file.place_fact_generations_, u32s);
        ar.vector(file.placeholder_result_facts_, structs);
        ar.vector(file.placeholder_result_fact_generations_, u32s);
        ar.vector(file.constant_states_, structs);
        ar.vector(file.constant_state_generations_, u32s);
        ar.vector(file.closure_identities_, structs);
        ar.vector(file.closure_identity_generations_, u32s);
        ar.vector(file.switch_facts_, structs);
        ar.vector(file.switch_fact_generations_, u32s);
        ar.vector(file.coroutine_facts_, structs);

        ar.vector(file.module_units_, structs);
        io_fields(ar, file.prelude_mark_);
        io_string_map(ar, file.module_import_provenance_, structs);
        ar.vector(file.module_unit_generations_, u32s);
        ar.vector(file.imported_definition_entities_,
                  [](auto& a, auto& flag) { a.chr(flag); });
        ar.boolean(file.coroutines_lowered_);

        ar.vector(file.insts_, structs);
        ar.vector(file.inst_generations_, u32s);
        ar.vector(file.payloads_,
                  [](auto& a, auto& payload) { io_inst_payload(a, payload); });
        ar.vector(file.inline_asm_payloads_, structs);
        ar.vector(file.inline_asm_payload_generations_, u32s);
        ar.vector(file.operands_, structs);
        ar.vector(file.blocks_, structs);
        ar.vector(file.block_generations_, u32s);
        ar.vector(file.functions_, structs);
        ar.vector(file.function_generations_, u32s);
        ar.vector(file.generics_, structs);
        ar.vector(file.generic_generations_, u32s);
        ar.vector(file.specifics_, structs);
        ar.vector(file.specific_generations_, u32s);

        ar.vector(file.value_expressions_,
                  [](auto& a, auto& expression) {
                      a.value_expression(expression);
                  });
        ar.vector(file.value_expression_generations_, u32s);
        io_u64_id_multimap(ar, file.value_expression_index_);

        io_diagnostics(ar, file.errors_);
        io_diagnostics(ar, file.warnings_);
        io_diagnostics(ar, file.notes_);
        ar.vector(file.module_asm_, strs);
    }
};
uint64_t module_graph_schema_version() { return 39; }

bool module_graph_serializable(const File& file) {

    return ModuleGraphSerializer::serializable(file);
}

bool write_module_graph(const File& file, std::string& out) {
    if (!module_graph_serializable(file)) {
        return false;
    }
    serialize::ByteWriter writer;
    writer.u32(kModuleGraphMagic);
    writer.u64(module_graph_schema_version());
    GraphWriter archive(writer);

    ModuleGraphSerializer::io(archive, const_cast<File&>(file));
    out += writer.buffer();
    return true;
}

std::unique_ptr<File> read_module_graph(std::string_view bytes,
                                        std::shared_ptr<TargetInfo> target) {
    serialize::ByteReader reader(bytes);
    if (reader.u32() != kModuleGraphMagic || !reader.ok()) {
        return nullptr;
    }
    if (reader.u64() != module_graph_schema_version() || !reader.ok()) {
        return nullptr;
    }
    auto file = std::make_unique<File>();
    file->set_target_info(std::move(target));
    GraphReader archive(reader);

    ModuleGraphSerializer::io(archive, *file);
    if (!archive.ok() || !reader.at_end()) {
        return nullptr;
    }
    ModuleGraphSerializer::rebuild_name_index(*file);
    return file;
}

} // namespace aburi::cir
