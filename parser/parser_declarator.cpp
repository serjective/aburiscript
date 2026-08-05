#include "parser.h"

#include "../builtin_registry.h"
#include "../numeric_utils.h"
#include "../token_spelling.h"

#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace aburi::syntax {

namespace {

TextPayload text_payload(std::string_view text) {
    return TextPayload{std::string(text)};
}

cir::TypeRef merge_qualifiers(cir::TypeRef type,
                              uint8_t qualifiers,
                              collect::Session& collect_session) {
    uint8_t merged = static_cast<uint8_t>(type.qualifiers | qualifiers);
    cir::TypeId resolved = type.valid()
        ? collect_session.file().resolved_type(type.type)
        : cir::TypeId{};
    if (collect_session.file().valid(resolved)) {
        cir::TypeKind kind = collect_session.file().type(resolved).kind;
        if (kind == cir::TypeKind::LValueReference ||
            kind == cir::TypeKind::RValueReference) {

            merged = static_cast<uint8_t>(
                merged & ~(cir::QualConst | cir::QualVolatile));
        }
    }
    type.qualifiers = merged;
    return type;
}

cir::TypeRef without_qualifiers(cir::TypeRef type) {
    type.qualifiers = cir::QualNone;
    return type;
}

class DeclaratorTypeSpine {
    struct SlotPayload {};
    struct FixedPayload {
        cir::TypeRef type;
    };
    struct PointerPayload {};
    struct BlockPointerPayload {};
    struct ReferencePayload {
        cir::ReferenceKind reference_kind = cir::ReferenceKind::LValue;
    };
    struct MemberPointerPayload {
        cir::TypeRef class_type;
    };
    struct ArrayPayload {
        std::optional<size_t> size;
        cir::ArraySizeKind size_kind = cir::ArraySizeKind::Incomplete;
        cir::InstId size_expr{};
        bool size_expr_is_dependent = false;
        uint32_t extent_param = cir::ArrayTypePayload::no_extent_param;
        cir::TemplateValueExpression dependent_size_expr;
    };
    struct FunctionPayload {
        std::vector<cir::TypeRef> parameters;
        std::vector<uint8_t> parameter_pack_flags;
        bool is_variadic = false;
        bool has_prototype = true;
        std::optional<cir::TypeRef> fixed_return_type;
        cir::FunctionRefQualifierKind ref_qualifier =
            cir::FunctionRefQualifierKind::None;
        cir::FunctionExceptionSpec exception_spec;
        bool member_is_const = false;
        bool member_is_volatile = false;
    };

    using Payload = std::variant<SlotPayload,
                                 FixedPayload,
                                 PointerPayload,
                                 BlockPointerPayload,
                                 ReferencePayload,
                                 MemberPointerPayload,
                                 ArrayPayload,
                                 FunctionPayload>;

    struct Node {
        explicit Node(Payload payload) : payload(std::move(payload)) {}

        Payload payload;
        std::unique_ptr<Node> child;
        uint8_t child_qualifiers = cir::QualNone;
        uint8_t qualifiers = cir::QualNone;
    };

public:
    static DeclaratorTypeSpine slot() {
        return DeclaratorTypeSpine(make_slot_node());
    }

    static DeclaratorTypeSpine fixed(cir::TypeRef type) {
        return DeclaratorTypeSpine(std::make_unique<Node>(FixedPayload{type}));
    }

    static DeclaratorTypeSpine pointer(uint8_t pointee_qualifiers,
                                       uint8_t pointer_qualifiers = cir::QualNone) {
        return DeclaratorTypeSpine(make_unary_node(PointerPayload{},
                                                   pointee_qualifiers,
                                                   pointer_qualifiers));
    }

    static DeclaratorTypeSpine block_pointer(uint8_t pointee_qualifiers,
                                             uint8_t pointer_qualifiers = cir::QualNone) {
        return DeclaratorTypeSpine(make_unary_node(BlockPointerPayload{},
                                                   pointee_qualifiers,
                                                   pointer_qualifiers));
    }

    static DeclaratorTypeSpine reference(uint8_t referred_qualifiers,
                                         cir::ReferenceKind reference_kind,
                                         uint8_t reference_qualifiers = cir::QualNone) {
        return DeclaratorTypeSpine(make_unary_node(ReferencePayload{reference_kind},
                                                   referred_qualifiers,
                                                   reference_qualifiers));
    }

    static DeclaratorTypeSpine member_pointer(cir::TypeRef class_type,
                                              uint8_t member_qualifiers,
                                              uint8_t pointer_qualifiers = cir::QualNone) {
        return DeclaratorTypeSpine(make_unary_node(MemberPointerPayload{class_type},
                                                   member_qualifiers,
                                                   pointer_qualifiers));
    }

    static DeclaratorTypeSpine array(uint8_t element_qualifiers,
                                     std::optional<size_t> size,
                                     cir::ArraySizeKind size_kind,
                                     cir::InstId size_expr = {},
                                     uint8_t array_qualifiers = cir::QualNone,
                                     bool size_expr_is_dependent = false,
                                     uint32_t extent_param =
                                         cir::ArrayTypePayload::no_extent_param,
                                     cir::TemplateValueExpression
                                         dependent_size_expr = {}) {
        return DeclaratorTypeSpine(
            make_unary_node(ArrayPayload{size,
                                         size_kind,
                                         size_expr,
                                         size_expr_is_dependent,
                                         extent_param,
                                         std::move(dependent_size_expr)},
                            element_qualifiers,
                            array_qualifiers));
    }

    static DeclaratorTypeSpine function(std::vector<cir::TypeRef> parameters,
                                        std::vector<uint8_t> parameter_pack_flags,
                                        bool is_variadic,
                                        bool has_prototype,
                                        uint8_t return_qualifiers = cir::QualNone,
                                        uint8_t function_qualifiers = cir::QualNone,
                                        std::optional<cir::TypeRef> fixed_return_type = std::nullopt,
                                        cir::FunctionRefQualifierKind ref_qualifier =
                                            cir::FunctionRefQualifierKind::None,
                                        cir::FunctionExceptionSpec exception_spec = {},
                                        bool member_is_const = false,
                                        bool member_is_volatile = false) {
        auto node = std::make_unique<Node>(
            FunctionPayload{std::move(parameters),
                            std::move(parameter_pack_flags),
                            is_variadic,
                            has_prototype,
                            fixed_return_type,
                            ref_qualifier,
                            std::move(exception_spec),
                            member_is_const,
                            member_is_volatile});
        if (!fixed_return_type.has_value()) {
            node->child = make_slot_node();
        }
        node->child_qualifiers = return_qualifiers;
        node->qualifiers = function_qualifiers;
        return DeclaratorTypeSpine(std::move(node));
    }

    void wrap_pointer(uint8_t pointee_qualifiers,
                      uint8_t pointer_qualifiers = cir::QualNone) {
        wrap_outer(pointer(pointee_qualifiers, pointer_qualifiers));
    }

    void wrap_block_pointer(uint8_t pointee_qualifiers,
                            uint8_t pointer_qualifiers = cir::QualNone) {
        wrap_outer(block_pointer(pointee_qualifiers, pointer_qualifiers));
    }

    void wrap_reference(uint8_t referred_qualifiers,
                        cir::ReferenceKind reference_kind,
                        uint8_t reference_qualifiers = cir::QualNone) {
        wrap_outer(reference(referred_qualifiers, reference_kind, reference_qualifiers));
    }

    void wrap_member_pointer(cir::TypeRef class_type,
                             uint8_t member_qualifiers,
                             uint8_t pointer_qualifiers = cir::QualNone) {
        wrap_outer(member_pointer(class_type, member_qualifiers, pointer_qualifiers));
    }

    bool replace_slot_with(DeclaratorTypeSpine replacement) {
        return replace_slot_in(root_, replacement.root_);
    }

    bool has_slot() const {
        return has_slot_in(root_.get());
    }

    bool is_slot_only() const {
        return root_ && std::holds_alternative<SlotPayload>(root_->payload);
    }

    cir::TypeRef build(collect::Session& collect_session, cir::TypeRef base) const {
        return build_node(root_.get(), collect_session, base);
    }

private:
    explicit DeclaratorTypeSpine(std::unique_ptr<Node> root)
        : root_(std::move(root)) {}

    static std::unique_ptr<Node> make_slot_node() {
        return std::make_unique<Node>(SlotPayload{});
    }

    static std::unique_ptr<Node> make_unary_node(Payload payload,
                                                 uint8_t child_qualifiers,
                                                 uint8_t qualifiers) {
        auto node = std::make_unique<Node>(std::move(payload));
        node->child = make_slot_node();
        node->child_qualifiers = child_qualifiers;
        node->qualifiers = qualifiers;
        return node;
    }

    static bool replace_slot_in(std::unique_ptr<Node>& node,
                                std::unique_ptr<Node>& replacement) {
        if (!node) {
            return false;
        }
        if (std::holds_alternative<SlotPayload>(node->payload)) {
            node = std::move(replacement);
            if (!node) {
                node = make_slot_node();
            }
            return true;
        }
        if (node->child) {
            return replace_slot_in(node->child, replacement);
        }
        return false;
    }

    static bool has_slot_in(const Node* node) {
        if (!node) {
            return false;
        }
        if (std::holds_alternative<SlotPayload>(node->payload)) {
            return true;
        }
        return has_slot_in(node->child.get());
    }

    static cir::TypeRef qualified_child(const Node& node,
                                        collect::Session& collect_session,
                                        cir::TypeRef base) {
        cir::TypeRef child = build_node(node.child.get(), collect_session, base);
        return merge_qualifiers(
            child, node.child_qualifiers, collect_session);
    }

    static cir::TypeRef build_node(const Node* node,
                                   collect::Session& collect_session,
                                   cir::TypeRef base) {
        if (!node) {
            return base;
        }
        if (std::holds_alternative<SlotPayload>(node->payload)) {
            return base;
        }
        if (const auto* fixed = std::get_if<FixedPayload>(&node->payload)) {
            return fixed->type;
        }
        if (std::holds_alternative<PointerPayload>(node->payload)) {
            cir::TypeRef pointee = qualified_child(*node, collect_session, base);
            cir::TypeId pointer = collect_session.pointer_type(pointee);
            return collect_session.type_ref(pointer, node->qualifiers);
        }
        if (std::holds_alternative<BlockPointerPayload>(node->payload)) {
            cir::TypeRef pointee = qualified_child(*node, collect_session, base);
            cir::TypeId pointer = collect_session.block_pointer_type(pointee);
            return collect_session.type_ref(pointer, node->qualifiers);
        }
        if (const auto* reference = std::get_if<ReferencePayload>(&node->payload)) {
            cir::TypeRef referred = qualified_child(*node, collect_session, base);
            cir::TypeId reference_type =
                collect_session.reference_type(referred, reference->reference_kind);
            return collect_session.type_ref(reference_type, node->qualifiers);
        }
        if (const auto* member = std::get_if<MemberPointerPayload>(&node->payload)) {
            cir::TypeRef member_type = qualified_child(*node, collect_session, base);
            cir::TypeId member_pointer =
                collect_session.member_pointer_type(member->class_type, member_type);
            return collect_session.type_ref(member_pointer, node->qualifiers);
        }
        if (const auto* array = std::get_if<ArrayPayload>(&node->payload)) {
            cir::TypeRef element = qualified_child(*node, collect_session, base);
            cir::TypeId array_type =
                array->extent_param != cir::ArrayTypePayload::no_extent_param
                    ? collect_session.array_type_with_extent_param(
                          element, array->size, array->extent_param)
                    : collect_session.array_type(element,
                                                 array->size_kind,
                                                 array->size,
                                                 array->size_expr,
                                                 array->size_expr_is_dependent,
                                                 array->dependent_size_expr);
            return collect_session.type_ref(array_type, node->qualifiers);
        }
        if (const auto* function = std::get_if<FunctionPayload>(&node->payload)) {
            cir::TypeRef return_type = function->fixed_return_type.has_value()
                ? *function->fixed_return_type
                : qualified_child(*node, collect_session, base);
            cir::TypeId function_type =
                collect_session.function_type(return_type,
                                              function->parameters,
                                              function->is_variadic,
                                              function->has_prototype,
                                              function->member_is_const,
                                              function->exception_spec,
                                              function->parameter_pack_flags,
                                              function->ref_qualifier,
                                              function->member_is_volatile);
            return collect_session.type_ref(function_type, node->qualifiers);
        }
        return base;
    }

    void wrap_outer(DeclaratorTypeSpine wrapper) {
        if (!root_) {
            root_ = make_slot_node();
        }
        if (!wrapper.root_) {
            return;
        }
        wrapper.root_->child = std::move(root_);
        root_ = std::move(wrapper.root_);
    }

    std::unique_ptr<Node> root_;
};

} // namespace

Parser::DeclarationParser::DeclarationParser(Parser& parser,
                                             TypeParseContext context)
    : pars(parser), type_context(context) {}

void Parser::DeclarationParser::error(std::string message) {
    SrcLoc err_loc = pars.at_end() ? begin_loc : pars.current().loc;
    error_custloc(std::move(message), err_loc);
}

void Parser::DeclarationParser::error_custloc(std::string message, SrcLoc loc) {
    pars.diagnose(DiagnosticLevel::Error, std::move(message), loc);
}

Parser::StorageClass
Parser::DeclarationParser::resolve_storage_class(const TypeTally& tally) {
    if (tally.typedef_count) return StorageClass::Typedef;
    if (tally.static_count) return StorageClass::Static;
    if (tally.extern_count) return StorageClass::Extern;
    if (tally.auto_count) return StorageClass::Auto;
    if (tally.register_count) return StorageClass::Register;
    return StorageClass::None;
}

cir::TypeRef Parser::DeclarationParser::resolve_builtin_type(const TypeTally& tally) {
    cir::File& file = pars.collect_session_.file();
    auto builtin = [&](cir::BuiltinTypeKind kind) {
        return pars.collect_session_.type_ref(file.builtin_type(kind));
    };

    auto maybe_complex = [&](cir::TypeRef type) {
        if (!tally.complex_count) {
            return type;
        }
        return pars.collect_session_.type_ref(pars.collect_session_.complex_type(type));
    };
    if (tally.void_count == 1) return builtin(cir::BuiltinTypeKind::Void);
    if (tally.bool_count == 1) return builtin(cir::BuiltinTypeKind::Bool);
    if (tally.wchar_count == 1) return builtin(cir::BuiltinTypeKind::WChar);
    if (tally.char8_count == 1) return builtin(cir::BuiltinTypeKind::Char8);
    if (tally.char16_count == 1) return builtin(cir::BuiltinTypeKind::Char16);
    if (tally.char32_count == 1) return builtin(cir::BuiltinTypeKind::Char32);
    if (tally.char_count == 1) {
        if (tally.unsigned_count == 1) return maybe_complex(builtin(cir::BuiltinTypeKind::UChar));
        if (tally.signed_count == 1) return maybe_complex(builtin(cir::BuiltinTypeKind::SChar));
        return maybe_complex(builtin(cir::BuiltinTypeKind::Char));
    }
    if (tally.bitint_count == 1) {
        return pars.collect_session_.type_ref(
            file.bit_int_type(tally.bitint_bits, tally.unsigned_count > 0));
    }
    if (tally.int128_count == 1) {
        return maybe_complex(builtin(tally.unsigned_count ? cir::BuiltinTypeKind::UInt128
                                                          : cir::BuiltinTypeKind::Int128));
    }
    if (tally.long_count == 2) {
        return maybe_complex(builtin(tally.unsigned_count ? cir::BuiltinTypeKind::ULongLong
                                                          : cir::BuiltinTypeKind::LongLong));
    }
    if (tally.long_count == 1) {
        if (tally.double_count == 1) return maybe_complex(builtin(cir::BuiltinTypeKind::LongDouble));
        return maybe_complex(builtin(tally.unsigned_count ? cir::BuiltinTypeKind::ULong
                                                          : cir::BuiltinTypeKind::Long));
    }
    if (tally.short_count == 1) {
        return maybe_complex(builtin(tally.unsigned_count ? cir::BuiltinTypeKind::UShort
                                                          : cir::BuiltinTypeKind::Short));
    }
    if (tally.float16_count == 1) return maybe_complex(builtin(cir::BuiltinTypeKind::Float16));
    if (tally.float_count == 1) return maybe_complex(builtin(cir::BuiltinTypeKind::Float));
    if (tally.double_count == 1) return maybe_complex(builtin(cir::BuiltinTypeKind::Double));
    if (tally.int_count || tally.signed_count || tally.unsigned_count) {
        return maybe_complex(builtin(tally.unsigned_count ? cir::BuiltinTypeKind::UInt
                                                          : cir::BuiltinTypeKind::Int));
    }
    return {};
}

void Parser::DeclarationParser::validate_tally(const TypeTally& tally) {
    if (tally.signed_count && tally.unsigned_count) {
        error_custloc("Cannot have both signed and unsigned", begin_loc);
    }
    if (tally.int128_count > 1) {
        error_custloc("duplicate '__int128' specifier", begin_loc);
    }
    if (tally.bitint_count > 1) {
        error_custloc("duplicate '_BitInt' specifier", begin_loc);
    }
    if (tally.bitint_count &&
        (tally.char_count || tally.short_count || tally.long_count ||
         tally.int_count || tally.float_count || tally.double_count ||
         tally.void_count || tally.bool_count || tally.wchar_count ||
         tally.char8_count || tally.char16_count || tally.char32_count ||
         tally.float16_count ||
         tally.int128_count || tally.complex_count)) {
        error_custloc("'_BitInt' cannot be combined with other type specifiers", begin_loc);
    }
    if (tally.bitint_count == 1) {
        uint32_t min_bits = tally.unsigned_count ? 1 : 2;
        if (tally.bitint_bits < min_bits) {
            error_custloc(tally.unsigned_count
                              ? "'unsigned _BitInt' requires a width of at least 1"
                              : "'_BitInt' requires a width of at least 2",
                          begin_loc);
        } else if (tally.bitint_bits > 128) {
            error_custloc("'_BitInt' widths greater than 128 are not supported", begin_loc);
        }
    }
    if (tally.int128_count &&
        (tally.char_count || tally.short_count || tally.long_count ||
         tally.int_count || tally.float_count || tally.double_count ||
         tally.void_count || tally.bool_count || tally.wchar_count ||
         tally.char8_count || tally.char16_count || tally.char32_count ||
         tally.float16_count)) {
        error_custloc("'__int128' cannot be combined with other type specifiers", begin_loc);
    }
    if (tally.wchar_count > 1) {
        error_custloc("duplicate 'wchar_t' specifier", begin_loc);
    }
    if (tally.wchar_count &&
        (tally.void_count || tally.char_count || tally.short_count || tally.int_count ||
         tally.long_count || tally.float_count || tally.double_count || tally.bool_count ||
         tally.signed_count || tally.unsigned_count || tally.int128_count ||
         tally.float16_count || tally.complex_count ||
         tally.char8_count || tally.char16_count || tally.char32_count)) {
        error_custloc("'wchar_t' cannot be combined with other type specifiers", begin_loc);
    }
    if (tally.char8_count > 1) {
        error_custloc("duplicate 'char8_t' specifier", begin_loc);
    }
    if (tally.char8_count &&
        (tally.void_count || tally.char_count || tally.short_count ||
         tally.int_count || tally.long_count || tally.float_count ||
         tally.double_count || tally.bool_count || tally.wchar_count ||
         tally.signed_count || tally.unsigned_count || tally.int128_count ||
         tally.float16_count || tally.complex_count || tally.char16_count ||
         tally.char32_count)) {
        error_custloc("'char8_t' cannot be combined with other type specifiers",
                      begin_loc);
    }
    if (tally.char16_count > 1) {
        error_custloc("duplicate 'char16_t' specifier", begin_loc);
    }
    if (tally.char16_count &&
        (tally.void_count || tally.char_count || tally.short_count || tally.int_count ||
         tally.long_count || tally.float_count || tally.double_count || tally.bool_count ||
         tally.wchar_count || tally.signed_count || tally.unsigned_count ||
         tally.int128_count || tally.float16_count || tally.complex_count ||
         tally.char8_count || tally.char32_count)) {
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
         tally.char8_count || tally.char16_count)) {
        error_custloc("'char32_t' cannot be combined with other type specifiers", begin_loc);
    }
    if (tally.auto_type_count > 1) {
        error_custloc("duplicate '__auto_type' specifier", begin_loc);
    }
    if (tally.auto_type_count &&
        (tally.void_count || tally.char_count || tally.short_count ||
         tally.int_count || tally.long_count || tally.float_count || tally.double_count ||
         tally.bool_count || tally.wchar_count || tally.char8_count ||
         tally.char16_count ||
         tally.char32_count || tally.signed_count || tally.unsigned_count ||
         tally.int128_count || tally.float16_count || tally.complex_count)) {
        error_custloc("'__auto_type' cannot be combined with other type specifiers", begin_loc);
    }
    if (tally.auto_type_count && tally.typedef_count) {
        error_custloc("'__auto_type' cannot be combined with 'typedef'", begin_loc);
    }
    if (tally.cxx_auto_count > 1) {
        error_custloc("duplicate 'auto' specifier", begin_loc);
    }
    if (tally.cxx_auto_count && tally.auto_type_count) {
        error_custloc("'auto' cannot be combined with '__auto_type'", begin_loc);
    }
    if (tally.cxx_auto_count &&
        (tally.void_count || tally.char_count || tally.short_count ||
         tally.int_count || tally.long_count || tally.float_count || tally.double_count ||
         tally.bool_count || tally.wchar_count || tally.char8_count ||
         tally.char16_count ||
         tally.char32_count || tally.signed_count || tally.unsigned_count ||
         tally.int128_count || tally.float16_count || tally.complex_count)) {
        error_custloc("'auto' cannot be combined with other type specifiers", begin_loc);
    }
    if (tally.cxx_auto_count && tally.typedef_count) {
        error_custloc("'auto' cannot be combined with 'typedef'", begin_loc);
    }
    if (tally.decltype_auto_count > 1) {
        error_custloc("duplicate 'decltype(auto)' specifier", begin_loc);
    }
    if (tally.decltype_auto_count &&
        (tally.auto_type_count || tally.cxx_auto_count)) {
        error_custloc("'decltype(auto)' cannot be combined with 'auto' or '__auto_type'",
                      begin_loc);
    }
    if (tally.decltype_auto_count &&
        (tally.void_count || tally.char_count || tally.short_count ||
         tally.int_count || tally.long_count || tally.float_count ||
         tally.double_count || tally.bool_count || tally.wchar_count ||
         tally.char8_count || tally.char16_count || tally.char32_count ||
         tally.signed_count ||
         tally.unsigned_count || tally.int128_count || tally.float16_count ||
         tally.complex_count)) {
        error_custloc("'decltype(auto)' cannot be combined with other type specifiers",
                      begin_loc);
    }
    if (tally.decltype_auto_count && tally.typedef_count) {
        error_custloc("'decltype(auto)' cannot be combined with 'typedef'", begin_loc);
    }
    if (tally.long_count > 2) {
        error_custloc("Too many 'long' specifiers", begin_loc);
    }
    if (tally.int_count > 1 || tally.signed_count > 1 || tally.unsigned_count > 1) {
        error_custloc("Too many 'int', 'signed', or 'unsigned' specifiers", begin_loc);
    }
    if (tally.static_count + tally.extern_count + tally.auto_count +
            tally.register_count + tally.typedef_count >
        1) {
        if (tally.typedef_count) {
            error_custloc("'typedef' cannot be combined with other storage class specifiers",
                          begin_loc);
        } else {
            error_custloc("Too many storage class specifiers", begin_loc);
        }
    }
    if (tally.thread_local_count &&
        (tally.auto_count || tally.register_count || tally.typedef_count)) {
        error_custloc("'_Thread_local' cannot be combined with 'auto', 'register', or 'typedef'",
                      begin_loc);
    }
    if (tally.block_byref_count > 1) {
        error_custloc("duplicate '__block' specifier", begin_loc);
    }
    if (tally.block_byref_count &&
        (tally.static_count || tally.extern_count || tally.register_count ||
         tally.typedef_count || tally.thread_local_count || tally.auto_count)) {
        error_custloc("'__block' cannot be combined with storage-class specifiers",
                      begin_loc);
    }
    if (tally.mutable_count > 1) {
        error_custloc("duplicate 'mutable' specifier", begin_loc);
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
    if (tally.constinit_count > 1) {
        error_custloc("duplicate 'constinit' specifier", begin_loc);
    }
    if (tally.constexpr_count && tally.consteval_count) {
        error_custloc("'constexpr' cannot be combined with 'consteval'", begin_loc);
    }
    if (tally.constinit_count &&
        (tally.constexpr_count || tally.consteval_count)) {
        error_custloc("'constinit' cannot be combined with 'constexpr' or 'consteval'",
                      begin_loc);
    }
    if (tally.constexpr_count && tally.typedef_count) {
        error_custloc("'constexpr' cannot be combined with 'typedef'", begin_loc);
    }
    if (tally.consteval_count && tally.typedef_count) {
        error_custloc("'consteval' cannot be combined with 'typedef'", begin_loc);
    }
    if (tally.constinit_count && tally.typedef_count) {
        error_custloc("'constinit' cannot be combined with 'typedef'", begin_loc);
    }
    if ((tally.float_count || tally.double_count) &&
        (tally.signed_count || tally.unsigned_count) &&
        !(tally.long_count == 1 && tally.double_count == 1)) {
        error_custloc("Cannot combine 'signed'/'unsigned' with floating-point type", begin_loc);
    }
    if (tally.float_count > 1 || tally.double_count > 1) {
        error_custloc("duplicate type specifier", begin_loc);
    }
    if (tally.float_count && tally.double_count) {
        error_custloc("Cannot combine 'float' and 'double'", begin_loc);
    }
    if ((tally.float_count || tally.double_count) &&
        (tally.char_count || tally.short_count || tally.int_count ||
         tally.void_count || tally.bool_count || tally.wchar_count ||
         tally.char8_count || tally.char16_count || tally.char32_count)) {
        error_custloc("Cannot combine floating-point type with other type specifiers", begin_loc);
    }
    if (tally.double_count && tally.long_count > 1) {
        error_custloc("Cannot have 'long long double'", begin_loc);
    }
    if (tally.float_count && tally.long_count) {
        error_custloc("Cannot combine 'long' with 'float'", begin_loc);
    }
    if (tally.complex_count) {
        if (tally.complex_count > 1) {
            error_custloc("duplicate '_Complex' specifier", begin_loc);
        }
        if (tally.void_count || tally.bool_count) {
            error_custloc("'_Complex' cannot be combined with 'void' or '_Bool'", begin_loc);
        }
        bool has_arithmetic_specifier =
            tally.char_count || tally.short_count || tally.int_count ||
            tally.long_count || tally.float_count || tally.double_count ||
            tally.float16_count || tally.int128_count ||
            tally.signed_count || tally.unsigned_count;
        if (!has_arithmetic_specifier) {
            error_custloc("'_Complex' requires an arithmetic type specifier", begin_loc);
        }
    }
}

cir::TypeRef Parser::DeclarationParser::parse_declaration_specifiers() {
    begin_loc = pars.current_loc();
    size_t begin = pars.current_raw_index();
    std::vector<NodeId> children;
    std::string text;
    bool saw_any = false;
    bool saw_type_specifier = false;
    bool saw_explicit_specifier = false;
    cir::TypeRef resolved_type{};
    cir::TypeRef atomic_type_specifier{};
    tally = TypeTally{};
    qualifiers = cir::QualNone;
    base_qualifiers = cir::QualNone;
    type_syntax = InvalidNodeId;
    type_text.clear();
    is_mutable = false;
    is_friend = false;
    is_block_byref = false;
    has_unsupported_semantics = false;
    type_originates_from_template_parameter = false;
    has_placeholder_type_constraint = false;
    placeholder_type_constraint_begin = 0;
    placeholder_type_constraint_end = 0;
    placeholder_type_constraint_loc = {};
    abbreviated_type_constraints.clear();

    auto append_token_text = [&](const Token& token) {
        if (!text.empty()) {
            text += ' ';
        }
        text += token.value.empty() ? token_type_to_string(token.type) : token.value;
    };

    auto template_id_qualifier_is_structor = [&]() -> std::optional<bool> {
        std::optional<Parser::TemplateIdQualifierLookahead> qualifier =
            pars.peek_template_id_qualifier();
        if (!qualifier.has_value()) {
            return std::nullopt;
        }

        const Token& terminal = pars.peek(qualifier->terminal_offset);
        return terminal.type == TokenType::BITWISE_NOT ||
               (pars.is_identifier_token(terminal.type) &&
                terminal.value == qualifier->template_name &&
                pars.peek(qualifier->terminal_offset + 1).type ==
                    TokenType::LEFT_PAREN);
    };

    bool parsing = true;
    while (parsing && !pars.at_end()) {
        Token token = pars.current();
        bool function_parameter_type =
            type_context.origin ==
                TypeParseContext::Origin::FunctionParameter ||
            type_context.origin == TypeParseContext::Origin::MemberParameter ||
            type_context.origin ==
                TypeParseContext::Origin::QualifiedDeclaratorParameter ||
            type_context.origin == TypeParseContext::Origin::LambdaParameter;
        if (!saw_type_specifier && !resolved_type.valid() &&
            pars.lang_opts_.is_cxx_mode() &&
            pars.starts_type_constraint_placeholder()) {
            size_t constraint_begin = pars.current_raw_index();
            std::optional<ParsedTypeConstraint> type_constraint =
                pars.try_parse_type_constraint();
            if (type_constraint.has_value()) {
                size_t constraint_end = pars.current_raw_index();
                if (!pars.match(TokenType::AUTO)) {
                    error_custloc("expected 'auto' after type-constraint",
                                  type_constraint->loc);
                    resolved_type = pars.collect_session_.type_ref(
                        pars.collect_session_.file().unknown_type());
                    saw_any = true;
                    saw_type_specifier = true;
                    if (function_parameter_type) {
                        abbreviated_type_constraints.push_back(
                            std::move(type_constraint));
                    }
                    continue;
                }
                tally.cxx_auto_count++;
                if (function_parameter_type) {
                    abbreviated_type_constraints.push_back(type_constraint);
                }
                has_placeholder_type_constraint = true;
                placeholder_type_constraint_begin = constraint_begin;
                placeholder_type_constraint_end = constraint_end;
                placeholder_type_constraint_loc = type_constraint->loc;
                text += (text.empty() ? "" : " ");
                text += "auto";
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
        }
        if (token.type == TokenType::IDENTIFIER && token.value == "__block") {
            tally.block_byref_count++;
            is_block_byref = true;
            append_token_text(token);
            pars.consume();
            saw_any = true;
            continue;
        }
        if (pars.lang_opts_.is_objc() && token.type == TokenType::IDENTIFIER &&
            (token.value == "__strong" || token.value == "__weak" ||
             token.value == "__unsafe_unretained" ||
             token.value == "__autoreleasing")) {

            cir::ObjCOwnership ownership = cir::ObjCOwnership::Strong;
            if (token.value == "__weak") {
                ownership = cir::ObjCOwnership::Weak;
            } else if (token.value == "__unsafe_unretained") {
                ownership = cir::ObjCOwnership::UnsafeUnretained;
            } else if (token.value == "__autoreleasing") {
                ownership = cir::ObjCOwnership::Autoreleasing;
            }
            qualifiers = cir::with_ownership(qualifiers, ownership);
            append_token_text(token);
            pars.consume();
            saw_any = true;
            continue;
        }
        if (token.type == TokenType::LEFT_BRACKET &&
            pars.peek(1).type == TokenType::LEFT_BRACKET) {
            ParsedAttributes attrs = pars.try_parse_attributes();
            leading_attrs.append(std::move(attrs.attrs));
            children.insert(children.end(), attrs.syntax.begin(), attrs.syntax.end());
            saw_any = true;
            continue;
        }
        switch (token.type) {
            case TokenType::VOID: tally.void_count++; saw_type_specifier = true; break;
            case TokenType::CHAR: tally.char_count++; saw_type_specifier = true; break;
            case TokenType::SHORT: tally.short_count++; saw_type_specifier = true; break;
            case TokenType::INT: tally.int_count++; saw_type_specifier = true; break;
            case TokenType::LONG: tally.long_count++; saw_type_specifier = true; break;
            case TokenType::FLOAT: tally.float_count++; saw_type_specifier = true; break;
            case TokenType::DOUBLE: tally.double_count++; saw_type_specifier = true; break;
            case TokenType::SIGNED: tally.signed_count++; saw_type_specifier = true; break;
            case TokenType::UNSIGNED: tally.unsigned_count++; saw_type_specifier = true; break;
            case TokenType::BOOL: tally.bool_count++; saw_type_specifier = true; break;
            case TokenType::WCHAR_T: tally.wchar_count++; saw_type_specifier = true; break;
            case TokenType::CHAR8_T: tally.char8_count++; saw_type_specifier = true; break;
            case TokenType::CHAR16_T: tally.char16_count++; saw_type_specifier = true; break;
            case TokenType::CHAR32_T: tally.char32_count++; saw_type_specifier = true; break;
            case TokenType::INT128: tally.int128_count++; saw_type_specifier = true; break;
            case TokenType::BITINT_KW: {
                append_token_text(token);
                pars.consume();
                tally.bitint_count++;
                saw_any = true;
                saw_type_specifier = true;
                if (!pars.match(TokenType::LEFT_PAREN)) {
                    error("expected '(' after '_BitInt'");
                    continue;
                }
                ParsedExpr width = pars.parse_conditional_expression();
                SrcLoc width_loc = pars.tree_.node(width.syntax).loc;
                width.sem = pars.collect_session_.require_value(
                    std::move(width.sem), collect::UseContext::RValue, width_loc);
                int64_t width_value = 0;
                if (pars.collect_session_.try_evaluate_integer_constant(width.sem,
                                                                        width_value)) {
                    tally.bitint_bits = width_value < 0 || width_value > (1 << 24)
                        ? 0
                        : static_cast<uint32_t>(width_value);
                } else {
                    error_custloc("'_BitInt' width must be an integer constant expression",
                                  width_loc);
                }
                if (!pars.match(TokenType::RIGHT_PAREN)) {
                    error("expected ')' after '_BitInt' width");
                }
                continue;
            }
            case TokenType::UINT128_T:
                tally.int128_count++;
                tally.unsigned_count++;
                saw_type_specifier = true;
                break;
            case TokenType::FLOAT16: tally.float16_count++; saw_type_specifier = true; break;
            case TokenType::COMPLEX: tally.complex_count++; saw_type_specifier = true; break;
            case TokenType::AUTO_TYPE: tally.auto_type_count++; saw_type_specifier = true; break;
            case TokenType::CONST: qualifiers |= cir::QualConst; break;
            case TokenType::VOLATILE: qualifiers |= cir::QualVolatile; break;
            case TokenType::RESTRICT: qualifiers |= cir::QualRestrict; break;
            case TokenType::NULLABILITY_QUALIFIER: break;
            case TokenType::ATOMIC:
                if (pars.peek(1).type == TokenType::LEFT_PAREN) {
                    append_token_text(token);
                    pars.consume();
                    pars.consume();
                    DeclarationParser inner(pars, type_context);
                    atomic_type_specifier = inner.parse_declaration(true, true);
                    if (!pars.match(TokenType::RIGHT_PAREN)) {
                        error("expected ')' after _Atomic type-name");
                    }
                    qualifiers |= cir::QualAtomic;
                    saw_any = true;
                    saw_type_specifier = true;
                    continue;
                }
                qualifiers |= cir::QualAtomic;
                break;
            case TokenType::SPLICE_OPEN: {

                if (saw_type_specifier) {
                    parsing = false;
                    continue;
                }
                resolved_type = pars.parse_splice_type_specifier();
                text += "[:splice:]";
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
            case TokenType::TYPENAME: {
                if (!pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                append_token_text(token);
                pars.consume();
                if (pars.check(TokenType::SPLICE_OPEN)) {

                    resolved_type = pars.parse_splice_type_specifier();
                    saw_any = true;
                    saw_type_specifier = true;
                    continue;
                }
                std::optional<cir::TypeRef> typename_type =
                    pars.parse_cxx_qualified_type_name(
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::ExplicitTypename));
                if (!typename_type.has_value()) {
                    error_custloc(
                        "expected qualified type name after 'typename'",
                        token.loc);
                    resolved_type = pars.collect_session_.type_ref(
                        pars.collect_session_.file().unknown_type());
                } else {
                    resolved_type = *typename_type;
                }
                text += " " +
                    pars.collect_session_.file().format_type(resolved_type);
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
            case TokenType::STRUCT:
            case TokenType::UNION:
            case TokenType::CLASS: {
                if (token.type == TokenType::CLASS &&
                    !pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                bool friend_elaborated_type =
                    pars.lang_opts_.is_cxx_mode() &&
                    (is_friend || allow_friend_type_specifier) &&
                    !saw_type_specifier;
                if (friend_elaborated_type) {
                    cir::RecordKind friend_kind =
                        token.type == TokenType::UNION
                            ? cir::RecordKind::Union
                            : (token.type == TokenType::CLASS
                                   ? cir::RecordKind::Class
                                   : cir::RecordKind::Struct);
                    auto kinds_agree = [](cir::RecordKind lhs,
                                          cir::RecordKind rhs) {
                        return (lhs == cir::RecordKind::Union) ==
                            (rhs == cir::RecordKind::Union);
                    };
                    auto validate_record_kind = [&](cir::TypeRef type,
                                                    SrcLoc loc) {
                        cir::TypeId resolved = pars.collect_session_.file()
                            .resolved_type(type.type);
                        if (!pars.collect_session_.file().valid(resolved) ||
                            pars.collect_session_.file().type(resolved).kind !=
                                cir::TypeKind::Record) {
                            return;
                        }
                        cir::EntityId entity = pars.collect_session_.file()
                            .record_entity(resolved);
                        const cir::RecordFacts* facts =
                            pars.collect_session_.file().record_facts(entity);
                        if (facts && !kinds_agree(friend_kind, facts->kind)) {
                            error_custloc(
                                "class-key does not agree with the nominated friend type",
                                loc);
                        }
                    };
                    auto target_context = [&]() {
                        const cir::File& file =
                            pars.collect_session_.file();
                        for (cir::DeclContextId context =
                                 pars.collect_session_.current_decl_context();
                             context.valid() && file.valid(context);
                             context = file.decl_context(context).parent) {
                            cir::DeclContextKind kind =
                                file.decl_context(context).kind;
                            if (kind == cir::DeclContextKind::Block ||
                                kind == cir::DeclContextKind::Namespace ||
                                kind == cir::DeclContextKind::TranslationUnit) {
                                return context;
                            }
                        }
                        return cir::DeclContextId{};
                    }();

                    append_token_text(token);
                    pars.consume();
                    ParsedAttributes elaborated_attrs =
                        pars.try_parse_attributes();
                    children.insert(children.end(),
                                    elaborated_attrs.syntax.begin(),
                                    elaborated_attrs.syntax.end());
                    SrcLoc name_loc = pars.current_loc();
                    std::optional<QualifiedTypeLookahead> qualified =
                        pars.peek_cxx_qualified_type();
                    if (qualified.has_value()) {
                        if (!elaborated_attrs.attrs.empty()) {
                            error_custloc(
                                "attributes are not allowed on a qualified elaborated friend type",
                                elaborated_attrs.attrs.attrs.front().loc);
                        }
                        if (qualified->template_info &&
                            (!qualified->template_info->is_class_template ||
                             qualified->template_info->is_alias_template)) {
                            error_custloc(
                                "elaborated friend type names a non-class template",
                                name_loc);
                        }
                        if (!qualified->template_info &&
                            qualified->terminal_context.valid()) {
                            const cir::Binding* tag =
                                pars.collect_session_.file().lookup_tag_binding(
                                    qualified->terminal_context,
                                    qualified->terminal_name,
                                    /*include_parents=*/false);
                            cir::EntityId record = qualified->type.valid()
                                ? pars.collect_session_.file().record_entity(
                                      pars.collect_session_.file().resolved_type(
                                          qualified->type.type))
                                : cir::EntityId{};
                            bool names_tag = tag &&
                                std::find(tag->entities.begin(),
                                          tag->entities.end(),
                                          record) != tag->entities.end();
                            if (!names_tag) {
                                error_custloc(
                                    "elaborated friend type shall not name a typedef-name",
                                    qualified->terminal_loc);
                            }
                        }
                        for (size_t i = 0; i < qualified->tokens_to_consume;
                             ++i) {
                            append_token_text(pars.current());
                            pars.consume();
                        }
                        if (qualified->template_info) {
                            cir::EntityId instantiated = pars.instantiate_template(
                                *qualified->template_info,
                                name_loc,
                                /*record_point_of_instantiation=*/false);
                            resolved_type = instantiated.valid()
                                ? pars.collect_session_.type_ref(
                                      pars.collect_session_.file()
                                          .entity(instantiated)
                                          .type)
                                : pars.collect_session_.type_ref(
                                      pars.collect_session_.file()
                                          .unknown_type());
                        } else {
                            resolved_type = qualified->type;
                        }
                        validate_record_kind(resolved_type, name_loc);
                        saw_any = true;
                        saw_type_specifier = true;
                        continue;
                    }

                    bool starts_qualified =
                        pars.check(TokenType::SCOPE_RESOLUTION) ||
                        (pars.is_identifier_token(pars.current().type) &&
                         (pars.peek(1).type == TokenType::SCOPE_RESOLUTION ||
                          (pars.peek(1).type == TokenType::LESS_THAN &&
                           pars.template_id_precedes_scope(0))));
                    if (starts_qualified) {
                        if (!elaborated_attrs.attrs.empty()) {
                            error_custloc(
                                "attributes are not allowed on a qualified elaborated friend type",
                                elaborated_attrs.attrs.attrs.front().loc);
                        }
                        std::optional<cir::TypeRef> dependent =
                            pars.parse_cxx_qualified_type_name(
                                TypeParseContext::type_only(
                                    TypeParseContext::Origin::
                                        ElaboratedTypeSpecifier));
                        resolved_type = dependent.value_or(
                            pars.collect_session_.type_ref(
                                pars.collect_session_.file().unknown_type()));
                        validate_record_kind(resolved_type, name_loc);
                        saw_any = true;
                        saw_type_specifier = true;
                        continue;
                    }

                    if (!pars.is_identifier_token(pars.current().type)) {
                        error_custloc("expected friend class name", name_loc);
                        resolved_type = pars.collect_session_.type_ref(
                            pars.collect_session_.file().unknown_type());
                        saw_any = true;
                        saw_type_specifier = true;
                        continue;
                    }
                    Token friend_name = pars.current();
                    append_token_text(friend_name);
                    pars.consume();
                    if (pars.check(TokenType::LESS_THAN)) {
                        if (!elaborated_attrs.attrs.empty()) {
                            error_custloc(
                                "attributes are not allowed before an elaborated friend template-id",
                                elaborated_attrs.attrs.attrs.front().loc);
                        }
                        const collect::Session::TemplateInfo* info =
                            target_context.valid()
                                ? pars.collect_session_.template_info_in_context(
                                      target_context,
                                      friend_name.value,
                                      /*include_parents=*/false)
                                : nullptr;
                        if (!info) {
                            info = pars.collect_session_.template_info_for_name(
                                friend_name.value);
                        }
                        if (!info || !info->is_class_template ||
                            info->is_alias_template) {
                            error_custloc(
                                "elaborated friend template-id does not name a class template",
                                friend_name.loc);
                            std::vector<collect::Session::TemplateArgument>
                                ignored;
                            (void)pars.parse_dependent_type_template_argument_list(
                                ignored, friend_name.loc);
                            resolved_type = pars.collect_session_.type_ref(
                                pars.collect_session_.file().unknown_type());
                        } else {
                            cir::EntityId instantiated =
                                pars.instantiate_template(*info,
                                    friend_name.loc,
                                    /*record_point_of_instantiation=*/false);
                            resolved_type = instantiated.valid()
                                ? pars.collect_session_.type_ref(
                                      pars.collect_session_.file()
                                          .entity(instantiated)
                                          .type)
                                : pars.collect_session_.type_ref(
                                      pars.collect_session_.file()
                                          .unknown_type());
                            if (!kinds_agree(friend_kind,
                                             info->record_kind)) {
                                error_custloc(
                                    "class-key does not agree with the nominated friend template",
                                    friend_name.loc);
                            }
                        }
                    } else if (pars.collect_session_
                                   .type_name_is_active_template_type_parameter(
                                       friend_name.value)) {
                        error_custloc(
                            "elaborated friend type shall not name a template type parameter",
                            friend_name.loc);
                        resolved_type = pars.collect_session_.type_ref(
                            pars.collect_session_.file().unknown_type());
                    } else {
                        const cir::File& file = pars.collect_session_.file();
                        cir::DeclContextId lookup_context =
                            pars.collect_session_.current_decl_context();
                        const cir::Binding* type_name =
                            lookup_context.valid()
                                ? file.lookup_type_name_binding(
                                      lookup_context,
                                      friend_name.value,
                                      /*include_parents=*/true)
                                : nullptr;
                        const cir::Binding* tag = lookup_context.valid()
                            ? file.lookup_tag_binding(lookup_context,
                                                      friend_name.value,
                                                      /*include_parents=*/true)
                            : nullptr;
                        auto context_distance = [&](const cir::Binding* binding) {
                            size_t distance = 0;
                            for (cir::DeclContextId context = lookup_context;
                                 context.valid() && file.valid(context);
                                 context = file.decl_context(context).parent,
                                 ++distance) {
                                if (binding && binding->context == context) {
                                    return distance;
                                }
                            }
                            return std::numeric_limits<size_t>::max();
                        };
                        const cir::Binding* found =
                            context_distance(type_name) <=
                                    context_distance(tag)
                                ? type_name
                                : tag;
                        if (found && !found->entities.empty() &&
                            file.entity(found->entities.back()).kind ==
                                cir::EntityKind::Record) {
                            cir::EntityId entity = found->entities.back();
                            resolved_type = pars.collect_session_.type_ref(
                                file.entity(entity).type);
                            validate_record_kind(resolved_type,
                                                 friend_name.loc);
                        } else {
                            if (found) {
                                error_custloc(
                                    "elaborated friend type shall not name a typedef-name",
                                    friend_name.loc);
                                resolved_type = pars.collect_session_.type_ref(
                                    pars.collect_session_.file().unknown_type());
                            } else {
                                cir::EntityId injected =
                                    pars.collect_session_
                                        .enclosing_injected_class_record(
                                            lookup_context,
                                            friend_name.value);
                                if (injected.valid()) {
                                    resolved_type =
                                        pars.collect_session_.type_ref(
                                            file.entity(injected).type);
                                    validate_record_kind(resolved_type,
                                                         friend_name.loc);
                                } else {
                                    collect::RecordDeclResult hidden =
                                        pars.collect_session_
                                            .declare_hidden_friend_record(
                                                friend_kind,
                                                friend_name.value,
                                                target_context,
                                                friend_name.loc);
                                    resolved_type =
                                        pars.collect_session_.type_ref(
                                            hidden.type);
                                    if (hidden.has_error) {
                                        has_unsupported_semantics = true;
                                    }
                                }
                            }
                        }
                    }
                    if (!elaborated_attrs.attrs.empty()) {
                        cir::TypeId record_type =
                            pars.collect_session_.file().resolved_type(
                                resolved_type.type);
                        if (pars.collect_session_.file().valid(record_type) &&
                            pars.collect_session_.file().type(record_type).kind ==
                                cir::TypeKind::Record) {
                            cir::EntityId friend_entity =
                                pars.collect_session_.file().record_entity(
                                    record_type);
                            pars.collect_session_.apply_attributes(
                                friend_entity,
                                AttributeTarget::Type,
                                elaborated_attrs.attrs,
                                friend_name.loc);
                        }
                    }
                    saw_any = true;
                    saw_type_specifier = true;
                    continue;
                }

                auto qualified_name_is_class_head = [&]() {
                    size_t offset = 1;
                    if (pars.peek(offset).type ==
                        TokenType::SCOPE_RESOLUTION) {
                        ++offset;
                    }
                    bool saw_terminal = false;
                    while (pars.is_identifier_token(pars.peek(offset).type)) {
                        if (pars.peek(offset + 1).type ==
                            TokenType::SCOPE_RESOLUTION) {
                            offset += 2;
                            continue;
                        }
                        saw_terminal = true;
                        ++offset;
                        break;
                    }
                    if (!saw_terminal) {
                        return false;
                    }
                    const Token& next = pars.peek(offset);
                    return next.type == TokenType::LEFT_BRACE ||
                           next.type == TokenType::COLON ||
                           (pars.is_identifier_token(next.type) &&
                            next.value == "final");
                };
                bool dependent_elaborated_name =
                    pars.lang_opts_.is_cxx_mode() &&
                    pars.starts_cxx_qualified_name(1) &&
                    (pars.collect_session_
                         .type_name_is_active_template_type_parameter(
                             pars.peek(1).value) ||
                     !pars.peek_cxx_qualified_type(1).has_value()) &&
                    !qualified_name_is_class_head();
                if (dependent_elaborated_name) {
                    append_token_text(token);
                    pars.consume();
                    std::optional<cir::TypeRef> elaborated =
                        pars.parse_cxx_qualified_type_name(
                            TypeParseContext::type_only(
                                TypeParseContext::Origin::ElaboratedTypeSpecifier));
                    resolved_type = elaborated.value_or(
                        pars.collect_session_.type_ref(
                            pars.collect_session_.file().unknown_type()));
                    text += " " + pars.collect_session_.file()
                                      .format_type(resolved_type);
                    saw_any = true;
                    saw_type_specifier = true;
                    continue;
                }
                cir::TypeId record_type{};
                NodeId record = pars.parse_record_specifier(&record_type);
                children.push_back(record);
                if (!text.empty()) {
                    text += ' ';
                }
                text += node_text(pars.tree_.node(record));
                resolved_type = pars.collect_session_.type_ref(record_type);
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
            case TokenType::DECLTYPE_KW: {
                if (!pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                append_token_text(token);
                pars.consume();
                if (pars.match(TokenType::LEFT_PAREN)) {
                    if (pars.check(TokenType::AUTO) &&
                        pars.peek(1).type == TokenType::RIGHT_PAREN) {
                        text += "(auto)";
                        pars.consume();
                        pars.consume();
                        tally.decltype_auto_count++;
                    } else {
                        pars.collect_session_.begin_decltype_operand();
                        ParsedExpr decltype_expr =
                            pars.parse_expression(PrecLevel::COMMA);
                        pars.collect_session_.end_decltype_operand();
                        children.push_back(decltype_expr.syntax);
                        text += "(" + node_text(pars.tree_.node(decltype_expr.syntax)) + ")";
                        if (!pars.match(TokenType::RIGHT_PAREN)) {
                            error_custloc("expected ')' after decltype operand",
                                          pars.current_loc());
                        }
                        resolved_type =
                            pars.collect_session_.resolve_decltype_expr_type(
                                decltype_expr.sem,
                                decltype_expr.sem.unparenthesized_id_or_member,
                                token.loc);
                    }
                } else {
                    error_custloc("expected '(' after decltype", token.loc);
                    resolved_type = pars.collect_session_.type_ref(
                        pars.collect_session_.file().unknown_type());
                }
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
            case TokenType::ENUM: {
                cir::TypeId enum_type{};
                NodeId enum_node = pars.parse_enum_specifier(&enum_type);
                children.push_back(enum_node);
                text = node_text(pars.tree_.node(enum_node));
                resolved_type = pars.collect_session_.type_ref(enum_type);
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
            case TokenType::TYPEOF_KW:
            case TokenType::TYPEOF_UNQUAL_KW: {
                const bool strip_qualifiers = token.type == TokenType::TYPEOF_UNQUAL_KW;
                append_token_text(token);
                pars.consume();
                if (!pars.match(TokenType::LEFT_PAREN)) {
                    error_custloc("expected '(' after typeof", token.loc);
                    resolved_type = pars.collect_session_.type_ref(
                        pars.collect_session_.file().unknown_type());
                } else {
                    bool parsed_type_name = false;
                    if (pars.is_type_start(pars.current().type)) {
                        RevertingTentativeParsingAction tentative(pars);
                        DeclarationParser typeof_dp(pars, type_context);
                        cir::TypeRef typeof_type = typeof_dp.parse_declaration(true, true);
                        if (typeof_type.valid() && pars.check(TokenType::RIGHT_PAREN)) {
                            tentative.commit();
                            pars.consume();
                            resolved_type = typeof_type;
                            parsed_type_name = true;
                        }
                    }
                    if (!parsed_type_name) {
                        ParsedExpr typeof_expr = pars.parse_expression(PrecLevel::COMMA);
                        if (!pars.match(TokenType::RIGHT_PAREN)) {
                            error_custloc("expected ')' after typeof operand", pars.current_loc());
                        }
                        resolved_type =
                            pars.collect_session_.resolve_typeof_expr_type(typeof_expr.sem,
                                                                            token.loc);
                    }
                }
                if (strip_qualifiers && resolved_type.valid()) {

                    resolved_type = cir::TypeRef{
                        pars.collect_session_.file().resolved_type(resolved_type.type),
                        cir::QualNone,
                        resolved_type.memory_space};
                }
                saw_any = true;
                saw_type_specifier = true;
                continue;
            }
            case TokenType::STATIC: tally.static_count++; break;
            case TokenType::EXTERN: tally.extern_count++; break;
            case TokenType::AUTO:
                if (pars.lang_opts_.is_cxx_mode()) {
                    tally.cxx_auto_count++;
                    saw_type_specifier = true;
                    if (function_parameter_type) {
                        abbreviated_type_constraints.push_back(std::nullopt);
                    }
                } else {
                    tally.auto_count++;
                }
                break;
            case TokenType::REGISTER: tally.register_count++; break;
            case TokenType::TYPEDEF: tally.typedef_count++; break;
            case TokenType::INLINE: tally.inline_count++; break;
            case TokenType::CONSTEVAL_KW:
                if (!pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                tally.consteval_count++;
                break;
            case TokenType::CONSTEXPR_KW: tally.constexpr_count++; break;
            case TokenType::CONSTINIT_KW:
                if (!pars.lang_opts_.is_cxx20_or_later()) {
                    parsing = false;
                    continue;
                }
                tally.constinit_count++;
                break;
            case TokenType::FRIEND_KW:
                if (!pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                if (is_friend) {
                    error_custloc("duplicate 'friend' specifier", token.loc);
                }
                is_friend = true;
                break;
            case TokenType::MUTABLE_KW:
                if (!pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                tally.mutable_count++;
                break;
            case TokenType::EXPLICIT_KW:
                if (!pars.lang_opts_.is_cxx_mode()) {
                    parsing = false;
                    continue;
                }
                if (saw_explicit_specifier) {
                    error_custloc("duplicate explicit specifier", token.loc);
                }
                saw_explicit_specifier = true;
                (void)pars.parse_explicit_specifier();
                error_custloc(
                    "explicit specifier is only allowed on a constructor, conversion function, or deduction guide",
                    token.loc);
                has_unsupported_semantics = true;
                saw_any = true;
                continue;
            case TokenType::THREAD_LOCAL: tally.thread_local_count++; break;
            case TokenType::NORETURN_KW: {
                ParsedAttribute noreturn_attr;
                noreturn_attr.name = "noreturn";
                noreturn_attr.kind = AttributeKind::NoReturn;
                noreturn_attr.syntax = AttributeSyntax::Keyword;
                noreturn_attr.loc = token.loc;
                leading_attrs.attrs.push_back(std::move(noreturn_attr));
                break;
            }
            case TokenType::EXTENSION_KW:
                break;
            case TokenType::ALIGNAS: {
                ParsedAttributes attrs = pars.try_parse_attributes();
                leading_attrs.append(std::move(attrs.attrs));
                children.insert(children.end(), attrs.syntax.begin(), attrs.syntax.end());
                saw_any = true;
                continue;
            }
            case TokenType::ATTRIBUTE_KW: {
                ParsedAttributes attrs = pars.try_parse_attributes();
                leading_attrs.append(std::move(attrs.attrs));
                children.insert(children.end(), attrs.syntax.begin(), attrs.syntax.end());
                saw_any = true;
                continue;
            }
            case TokenType::SCOPE_RESOLUTION:
            case TokenType::IDENTIFIER:
                if (!saw_type_specifier && !resolved_type.valid()) {
                    const BuiltinInfo* builtin =
                        token.type == TokenType::IDENTIFIER
                            ? BuiltinRegistry::instance().lookup(token.value)
                            : nullptr;
                    if (builtin && builtin->supported &&
                        builtin->syntax ==
                            BuiltinSyntaxKind::IntegerSequenceType) {
                        append_token_text(token);
                        pars.consume();
                        resolved_type =
                            pars.parse_builtin_make_integer_sequence_type(
                                token.loc, children);
                        saw_any = true;
                        saw_type_specifier = true;
                        continue;
                    }
                    if (builtin && builtin->supported &&
                        builtin->syntax ==
                            BuiltinSyntaxKind::PackElementType) {
                        append_token_text(token);
                        pars.consume();
                        resolved_type =
                            pars.parse_builtin_type_pack_element_type(
                                token.loc, children);
                        saw_any = true;
                        saw_type_specifier = true;
                        continue;
                    }
                    if (builtin && builtin->supported &&
                        builtin->syntax == BuiltinSyntaxKind::TypeTransform) {
                        append_token_text(token);
                        pars.consume();
                        if (!pars.match(TokenType::LEFT_PAREN)) {
                            error_custloc(
                                "expected '(' after builtin type transform name",
                                token.loc);
                            resolved_type = pars.collect_session_.type_ref(
                                pars.collect_session_.file().unknown_type());
                        } else {
                            cir::TypeRef operand;
                            NodeId operand_syntax = pars.parse_type_name(
                                nullptr,
                                nullptr,
                                nullptr,
                                &operand,
                                nullptr,
                                nullptr,
                                TypeParseContext::type_only(
                                    TypeParseContext::Origin::DefiningTypeId));
                            children.push_back(operand_syntax);
                            if (!pars.match(TokenType::RIGHT_PAREN)) {
                                error_custloc(
                                    "expected ')' after builtin type transform operand",
                                    pars.current_loc());
                            }
                            resolved_type = pars.collect_session_
                                .collect_builtin_type_transform(
                                    builtin->kind, operand, token.loc);
                        }
                        saw_any = true;
                        saw_type_specifier = true;
                        continue;
                    }
                    if (pars.lang_opts_.is_cxx_mode()) {
                        if (pars.out_of_line_structor_declaration_ahead()) {
                            parsing = false;
                            continue;
                        }
                        std::optional<bool> template_id_qualifier_structor =
                            template_id_qualifier_is_structor();
                        if (template_id_qualifier_structor.value_or(false)) {
                            parsing = false;
                            continue;
                        }
                        std::optional<QualifiedTypeLookahead>
                            template_id_qualified_type;
                        if (template_id_qualifier_structor.has_value()) {
                            template_id_qualified_type =
                                pars.peek_cxx_qualified_type();
                        }
                        if (template_id_qualifier_structor.has_value() &&
                            (!template_id_qualified_type.has_value() ||
                             !template_id_qualified_type
                                  ->is_deduced_placeholder)) {
                            std::optional<cir::TypeRef> actual_type =
                                pars.parse_cxx_qualified_type_name(type_context);
                            if (actual_type.has_value()) {
                                resolved_type = *actual_type;
                            } else {
                                has_unsupported_semantics = true;
                            }
                            text += (text.empty() ? "" : " ");
                            text += pars.collect_session_.file()
                                        .format_type(resolved_type);
                            saw_any = true;
                            saw_type_specifier = true;
                            continue;
                        }
                    }

                    if (pars.lang_opts_.is_cxx_mode() &&
                        token.type == TokenType::IDENTIFIER &&
                        pars.peek(1).type == TokenType::LESS_THAN &&
                        !pars.template_id_precedes_scope(0)) {
                        const collect::Session::TemplateInfo* info =
                            pars.collect_session_.template_info_for_name(token.value);
                        if (info &&
                            (info->is_class_template ||
                             info->is_alias_template)) {
                            append_token_text(token);
                            pars.consume();
                            cir::EntityId instantiated =
                                pars.instantiate_template(
                                    *info,
                                    token.loc,
                                    /*record_point_of_instantiation=*/
                                        !(is_friend ||
                                          allow_friend_type_specifier));
                            if (instantiated.valid()) {
                                resolved_type = pars.collect_session_.file()
                                    .entity_type_ref(instantiated);
                            } else {
                                resolved_type = pars.collect_session_.type_ref(
                                    pars.collect_session_.file().unknown_type());
                                has_unsupported_semantics = true;
                            }
                            saw_any = true;
                            saw_type_specifier = true;
                            continue;
                        }
                    }

                    if (pars.lang_opts_.is_cxx_mode() &&
                        pars.starts_cxx_qualified_name()) {
                        if (auto qualified = pars.peek_cxx_qualified_type()) {
                            SrcLoc qualified_loc = pars.current().loc;
                            cir::EntityId declaration_access_record{};
                            std::string declaration_access_function;
                            if (qualified->terminal_context.valid() &&
                                pars.collect_session_.file().valid(
                                    qualified->terminal_context)) {
                                cir::EntityId owner =
                                    pars.collect_session_.file()
                                        .decl_context(
                                            qualified->terminal_context)
                                        .owner;
                                const Token& declarator_token = pars.peek(
                                    qualified->tokens_to_consume);
                                if (owner.valid() &&
                                    pars.collect_session_.file().valid(owner) &&
                                    pars.is_identifier_token(
                                        declarator_token.type)) {
                                    const cir::Entity& owner_entity =
                                        pars.collect_session_.file().entity(
                                            owner);
                                    if (pars.peek(
                                            qualified->tokens_to_consume + 1)
                                            .type ==
                                            TokenType::SCOPE_RESOLUTION &&
                                        owner_entity.name.valid() &&
                                        pars.collect_session_.file().name(
                                            owner_entity.name) ==
                                            declarator_token.value) {
                                        declaration_access_record = owner;
                                    } else if (pars.peek(
                                                   qualified->tokens_to_consume +
                                                   1)
                                                   .type ==
                                               TokenType::LEFT_PAREN) {
                                        declaration_access_function =
                                            std::string(
                                                declarator_token.value);
                                    }
                                }
                            }
                            for (size_t i = 0;
                                 i < qualified->tokens_to_consume;
                                 ++i) {
                                append_token_text(pars.current());
                                pars.consume();
                            }
                            if (qualified->is_deduced_placeholder &&
                                qualified->template_info) {
                                deduced_class_template_info =
                                    qualified->template_info;
                                deduced_class_template_loc = qualified_loc;
                                resolved_type =
                                    pars.collect_session_.type_ref(
                                        pars.collect_session_.file()
                                            .unknown_type());
                            } else if (qualified->template_info) {
                                cir::EntityId instantiated =
                                    pars.instantiate_template(
                                        *qualified->template_info,
                                        qualified_loc,
                                        /*record_point_of_instantiation=*/
                                            !(is_friend ||
                                              allow_friend_type_specifier));
                                if (instantiated.valid()) {
                                    resolved_type =
                                        pars.collect_session_.file()
                                            .entity_type_ref(instantiated);
                                } else {
                                    resolved_type =
                                        pars.collect_session_.type_ref(
                                            pars.collect_session_.file()
                                                .unknown_type());
                                    has_unsupported_semantics = true;
                                }
                            } else {
                                cir::TypeRef checked = pars.collect_session_
                                    .lookup_qualified_type_name_ref_checked(
                                        qualified->terminal_context,
                                        qualified->terminal_name,
                                        qualified->terminal_loc,
                                        declaration_access_record,
                                        declaration_access_function);
                                resolved_type = checked.valid()
                                    ? checked
                                    : qualified->type;
                            }
                            saw_any = true;
                            saw_type_specifier = true;
                            continue;
                        }
                        TypeParseContext qualified_context = type_context;
                        if ((is_friend || allow_friend_type_specifier) &&
                            !qualified_context.is_type_only()) {
                            qualified_context = TypeParseContext::type_only(
                                TypeParseContext::Origin::FriendTypeSpecifier);
                        }
                        if (qualified_context.is_type_only()) {
                            if (auto dependent_type =
                                    pars.parse_cxx_qualified_type_name(
                                        qualified_context)) {
                                resolved_type = *dependent_type;
                                text += (text.empty() ? "" : " ");
                                text += pars.collect_session_.file()
                                            .format_type(resolved_type);
                                saw_any = true;
                                saw_type_specifier = true;
                                continue;
                            }
                        }
                        parsing = false;
                        continue;
                    }
                    if (token.type == TokenType::IDENTIFIER) {

                        if (pars.lang_opts_.is_cxx_mode() &&
                            pars.peek(1).type != TokenType::LESS_THAN) {
                            const collect::Session::TemplateInfo* alias =
                                pars.collect_session_.template_info_for_name(
                                    token.value);
                            if (alias && alias->is_alias_template &&
                                alias->alias_deduction_projection.has_value()) {
                                append_token_text(token);
                                pars.consume();
                                deduced_class_template_info = alias;
                                deduced_class_template_loc = token.loc;
                                resolved_type =
                                    pars.collect_session_.type_ref(
                                        pars.collect_session_.file()
                                            .unknown_type());
                                saw_any = true;
                                saw_type_specifier = true;
                                continue;
                            }
                        }

                        cir::TypeRef typedef_ref =
                            pars.collect_session_.lookup_type_name_ref_checked(
                                token.value, token.loc);
                        if (typedef_ref.valid()) {
                            if (pars.peek(1).type == TokenType::ELLIPSIS &&
                                pars.peek(2).type == TokenType::LEFT_BRACKET) {
                                append_token_text(token);
                                pars.consume();
                                pars.consume();
                                pars.consume();
                                ParsedExpr index =
                                    pars.parse_conditional_expression();
                                if (!pars.match(TokenType::RIGHT_BRACKET)) {
                                    error_custloc(
                                        "expected ']' after pack index",
                                        pars.current_loc());
                                }
                                if (!pars.lang_opts_.is_cxx26_or_later()) {
                                    error_custloc(
                                        "pack indexing is a C++26 feature",
                                        token.loc);
                                }
                                resolved_type = pars.collect_session_
                                    .collect_pack_index_type(
                                        typedef_ref,
                                        std::move(index.sem),
                                        token.loc);
                                text += "...[...]";
                                children.push_back(index.syntax);
                                type_originates_from_template_parameter = true;
                                saw_any = true;
                                saw_type_specifier = true;
                                continue;
                            }
                            bool directly_names_type_parameter =
                                pars.collect_session_
                                    .type_name_is_active_template_type_parameter(
                                        token.value);
                            if (directly_names_type_parameter) {
                                type_originates_from_template_parameter = true;
                            }
                            if (directly_names_type_parameter &&
                                pars.collect_session_
                                    .type_contains_type_parameter_pack(
                                        typedef_ref.type) &&
                                (pars.peek(1).type != TokenType::ELLIPSIS ||
                                 pars.collect_session_
                                     .in_pack_pattern_capture())) {
                                if (pars.collect_session_
                                        .capture_type_parameter_pack_name(
                                            token.value)) {
                                    append_token_text(token);
                                    pars.consume();
                                    resolved_type = typedef_ref;
                                    saw_any = true;
                                    saw_type_specifier = true;
                                    continue;
                                }
                                error_custloc(
                                    "unexpanded template parameter pack '" +
                                        std::string(token.value) +
                                        "' is not supported yet",
                                    token.loc);
                                pars.consume();
                                resolved_type =
                                    pars.collect_session_.type_ref(
                                        pars.collect_session_.file()
                                            .unknown_type());
                                has_unsupported_semantics = true;
                                saw_any = true;
                                saw_type_specifier = true;
                                continue;
                            }
                            append_token_text(token);
                            pars.consume();
                            if (pars.lang_opts_.is_objc() &&
                                !pars.lang_opts_.is_cxx_mode() &&
                                pars.check(TokenType::LESS_THAN) &&
                                pars.collect_session_
                                    .objc_type_accepts_angle_suffix(
                                        token.value)) {

                                pars.skip_objc_angle_suffix();
                            }
                            resolved_type = typedef_ref;
                            saw_any = true;
                            saw_type_specifier = true;
                            continue;
                        }
                        if (pars.lang_opts_.is_cxx_mode() &&
                            pars.peek(1).type != TokenType::LESS_THAN) {
                            const collect::Session::TemplateInfo* info =
                                pars.collect_session_.template_info_for_name(
                                    token.value);
                            bool is_primary_class =
                                info && info->is_class_template &&
                                !info->is_partial_specialization;
                            bool is_deducible_alias =
                                info && info->is_alias_template &&
                                info->alias_deduction_projection.has_value();
                            if (is_primary_class || is_deducible_alias) {
                                append_token_text(token);
                                pars.consume();
                                deduced_class_template_info = info;
                                deduced_class_template_loc = token.loc;
                                resolved_type =
                                    pars.collect_session_.type_ref(
                                        pars.collect_session_.file()
                                            .unknown_type());
                                saw_any = true;
                                saw_type_specifier = true;
                                continue;
                            }
                        }
                    }
                }
                parsing = false;
                continue;
            default:
                parsing = false;
                continue;
        }

        append_token_text(token);
        pars.consume();
        saw_any = true;
    }

    storage_class = resolve_storage_class(tally);
    is_inline = tally.inline_count > 0 || tally.consteval_count > 0;
    is_thread_local = tally.thread_local_count > 0;
    is_constexpr = tally.constexpr_count > 0 || tally.consteval_count > 0;
    is_consteval = tally.consteval_count > 0;
    is_constinit = tally.constinit_count > 0;
    is_mutable = tally.mutable_count > 0;

    if (!saw_any) {
        if (pars.lang_opts_.is_c_mode() &&
            pars.current().type == TokenType::IDENTIFIER) {

            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.file().builtin_type(cir::BuiltinTypeKind::Int));
            text = "int";
        } else if (pars.out_of_line_structor_declaration_ahead()) {
            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.file().builtin_type(cir::BuiltinTypeKind::Void));
            text = "";
            is_out_of_line_structor = true;
        } else {
            error_custloc("expected type specifier", pars.loc_for_index(begin));
            resolved_type = pars.collect_session_.type_ref(pars.collect_session_.file().unknown_type());
            text = "<error>";
        }
    } else if (!resolved_type.valid()) {
        if (pars.out_of_line_structor_declaration_ahead()) {

            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.file().builtin_type(
                    cir::BuiltinTypeKind::Void));
            text = "";
            is_out_of_line_structor = true;
        } else if (atomic_type_specifier.valid()) {
            resolved_type = without_qualifiers(atomic_type_specifier);
        } else if (tally.auto_type_count > 0) {
            validate_tally(tally);
            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.auto_type(cir::AutoTypeFlavor::Gnu));
        } else if (tally.cxx_auto_count > 0) {
            validate_tally(tally);
            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.auto_type(cir::AutoTypeFlavor::Cxx));
        } else if (tally.decltype_auto_count > 0) {
            validate_tally(tally);
            if (qualifiers != cir::QualNone) {
                error_custloc("'decltype(auto)' cannot be combined with cv-qualifiers",
                              begin_loc);
            }
            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.auto_type(cir::AutoTypeFlavor::DecltypeAuto));
        } else if (tally.auto_count > 0 && pars.lang_opts_.is_c23_or_later()) {

            validate_tally(tally);
            resolved_type = pars.collect_session_.type_ref(
                pars.collect_session_.auto_type(cir::AutoTypeFlavor::Gnu));
        } else {
            if (pars.lang_opts_.implicit_int) {
                if (tally.int_count > 1) tally.int_count = 1;
                if (tally.signed_count > 1) tally.signed_count = 1;
                if (tally.unsigned_count > 1) tally.unsigned_count = 1;
            }
            if (tally.complex_count &&
                tally.float_count == 0 && tally.double_count == 0 &&
                tally.char_count == 0 && tally.short_count == 0 &&
                tally.int_count == 0 && tally.long_count == 0 &&
                tally.signed_count == 0 && tally.unsigned_count == 0 &&
                tally.void_count == 0 && tally.bool_count == 0 &&
                tally.int128_count == 0 && tally.float16_count == 0) {
                tally.double_count = 1;
            }
            validate_tally(tally);
            resolved_type = resolve_builtin_type(tally);
            if (!resolved_type.valid()) {
                if (pars.lang_opts_.is_c_mode()) {

                    resolved_type = pars.collect_session_.type_ref(
                        pars.collect_session_.file().builtin_type(cir::BuiltinTypeKind::Int));
                } else {
                    error_custloc("Couldn't find corresponding internal type", begin_loc);
                    resolved_type = pars.collect_session_.type_ref(
                        pars.collect_session_.file().unknown_type());
                }
            }
        }
    } else {
        validate_tally(tally);
    }

    resolved_type = pars.collect_session_.apply_type_attributes(resolved_type,
                                                                leading_attrs,
                                                                begin_loc);

    qualifiers |= resolved_type.qualifiers;
    base_qualifiers = qualifiers;
    first_half = without_qualifiers(resolved_type);
    result_type = merge_qualifiers(
        first_half, qualifiers, pars.collect_session_);
    type_text = text;
    type_syntax = pars.make_node(NodeKind::TypeName,
                                 begin,
                                 pars.last_consumed_raw_end(),
                                 children,
                                 text_payload(type_text),
                                 result_type.valid() ? NodeFlagNone : NodeFlagHasError);
    return first_half;
}

cir::TypeRef Parser::DeclarationParser::parse_declaration(bool run_second_half,
                                                          bool allow_abstract) {
    cir::TypeRef base = parse_declaration_specifiers();
    if (!run_second_half) {
        result_type = merge_qualifiers(
            base, qualifiers, pars.collect_session_);
        return result_type;
    }
    ParsedDeclarator declarator = parse_declarator(base, allow_abstract);
    declarator_syntax = declarator.syntax;
    name = declarator.name;
    loc = declarator.loc;
    vla_bounds_fragment = std::move(declarator.vla_bounds);
    result_type = declarator.type_ref;
    func_args = std::move(declarator.params);
    captured_func_args = declarator.is_function;
    kr_param_names = std::move(declarator.kr_param_names);
    has_trailing_return_type = declarator.has_trailing_return_type;
    has_unsupported_semantics = has_unsupported_semantics ||
        declarator.has_unsupported_semantics;
    return result_type;
}

void Parser::DeclarationParser::reset_declarator_parsing_state() {
    vla_bounds_fragment = {};
    name.clear();
    loc = SrcLoc();
    result_type = {};
    declarator_syntax = InvalidNodeId;
    qualifiers = base_qualifiers;
    func_args.clear();
    captured_func_args = false;
    is_parameter_pack = false;
    kr_param_names.clear();
    has_trailing_return_type = false;
    abbreviated_template_info = {};
    abbreviated_type_constraints.clear();
}

void Parser::rewrite_abbreviated_function_parameter(
    DeclarationParser& owner,
    ParsedDeclarator& parameter,
    bool is_parameter_pack,
    uint32_t function_parameter_index,
    const std::vector<std::optional<ParsedTypeConstraint>>& constraints,
    SrcLoc loc) {
    size_t cxx_placeholders = collect_session_.count_auto_type_occurrences(
        parameter.type, cir::AutoTypeFlavor::Cxx);
    size_t decltype_placeholders =
        collect_session_.count_auto_type_occurrences(
            parameter.type, cir::AutoTypeFlavor::DecltypeAuto);
    if (decltype_placeholders != 0) {
        diagnose(DiagnosticLevel::Error,
                 "'decltype(auto)' is not permitted in a function parameter",
                 loc);
        parameter.has_unsupported_semantics = true;
    }
    if (cxx_placeholders == 0) {
        return;
    }

    collect::Session::TemplateInfo* target =
        owner.abbreviated_template_target
            ? owner.abbreviated_template_target
            : &owner.abbreviated_template_info;
    const collect::Session::TemplateInfo* replay =
        owner.abbreviated_template_target
            ? nullptr
            : collect_session_.current_abbreviated_function_template();
    std::vector<cir::TypeRef> replacements;
    replacements.reserve(cxx_placeholders);
    for (uint32_t placeholder_index = 0;
         placeholder_index < cxx_placeholders;
         ++placeholder_index) {
        const collect::Session::TemplateInfo::InventedFunctionParameter*
            replay_recipe = nullptr;
        if (replay) {
            auto found = std::find_if(
                replay->invented_function_parameters.begin(),
                replay->invented_function_parameters.end(),
                [&](const auto& recipe) {
                    return recipe.function_parameter_index ==
                               function_parameter_index &&
                        recipe.placeholder_index == placeholder_index &&
                        (recipe.loc.isInvalid() || loc.isInvalid() ||
                         recipe.loc.offset == loc.offset);
                });
            if (found != replay->invented_function_parameters.end()) {
                replay_recipe = &*found;
            }
        }
        if (replay_recipe) {
            replacements.push_back(
                collect_session_.abbreviated_function_parameter_replacement(
                    *replay,
                    replay_recipe->template_parameter_index));
            continue;
        }

        collect::Session::TemplateParameter invented;
        invented.kind = collect::Session::TemplateParameterKind::Type;
        invented.index = static_cast<uint32_t>(target->parameters.size());
        invented.depth = target->parameters.empty()
            ? 0
            : target->parameters.front().depth;
        invented.is_parameter_pack = is_parameter_pack;
        invented.loc = loc;
        invented.type_param_type = collect_session_.file().type_param_type(
            {},
            "",
            invented.index,
            invented.depth,
            is_parameter_pack);
        target->parameters.push_back(invented);
        target->invented_function_parameters.push_back(
            {function_parameter_index,
             placeholder_index,
             invented.index,
             loc});
        replacements.push_back(
            collect_session_.type_ref(invented.type_param_type));

        if (placeholder_index < constraints.size() &&
            constraints[placeholder_index].has_value()) {
            const ParsedTypeConstraint& parsed =
                *constraints[placeholder_index];
            collect::Session::TemplateInfo::IntroducedConstraint constraint;
            constraint.kind = collect::Session::TemplateInfo::
                IntroducedConstraintKind::FunctionParameterTypeConstraint;
            constraint.constrained_parameter_index = invented.index;
            constraint.type_constraint_concept = parsed.concept_info
                ? parsed.concept_info->entity
                : cir::EntityId{};
            constraint.type_constraint_arguments = parsed.arguments;
            constraint.loc = parsed.loc;
            constraint.normal_form = build_type_constraint_normal_form(
                *target, invented, parsed);
            target->introduced_constraints.push_back(std::move(constraint));
        }
    }

    cir::TypeId rewritten = collect_session_.replace_auto_type_occurrences(
        parameter.type,
        replacements,
        cir::AutoTypeFlavor::Cxx,
        loc);
    parameter.type = rewritten;
    parameter.type_ref.type = rewritten;
}
// todo: refactor down to size
Parser::ParsedDeclarator
Parser::DeclarationParser::parse_declarator(cir::TypeRef base_type,
                                            bool allow_abstract,
                                            const ParsedDeclarator* prefix) {
    size_t begin = pars.current_raw_index();
    size_t declarator_mark = pars.mark();
    DeclaratorTypeSpine old_spine = DeclaratorTypeSpine::slot();
    uint8_t current_quals = base_qualifiers;
    bool declarator_has_unsupported_semantics = has_unsupported_semantics;
    AttributeList declarator_attrs;

    auto parse_post_pointer_qualifiers = [&]() {
        while (!pars.at_end()) {
            if (pars.match(TokenType::CONST)) {
                current_quals |= cir::QualConst;
            } else if (pars.match(TokenType::VOLATILE)) {
                current_quals |= cir::QualVolatile;
            } else if (pars.match(TokenType::RESTRICT)) {
                current_quals |= cir::QualRestrict;
            } else if (pars.match(TokenType::ATOMIC)) {
                current_quals |= cir::QualAtomic;
            } else if (pars.match(TokenType::NULLABILITY_QUALIFIER)) {
            } else if (pars.lang_opts_.is_objc() &&
                       pars.check(TokenType::IDENTIFIER) &&
                       (pars.current().value == "__strong" ||
                        pars.current().value == "__weak" ||
                        pars.current().value == "__unsafe_unretained" ||
                        pars.current().value == "__autoreleasing")) {

                cir::ObjCOwnership ownership = cir::ObjCOwnership::Strong;
                if (pars.current().value == "__weak") {
                    ownership = cir::ObjCOwnership::Weak;
                } else if (pars.current().value == "__unsafe_unretained") {
                    ownership = cir::ObjCOwnership::UnsafeUnretained;
                } else if (pars.current().value == "__autoreleasing") {
                    ownership = cir::ObjCOwnership::Autoreleasing;
                }
                current_quals = cir::with_ownership(current_quals, ownership);
                pars.consume();
            } else if (pars.check(TokenType::ATTRIBUTE_KW)) {

                ParsedAttributes attrs = pars.try_parse_attributes();
                declarator_attrs.append(std::move(attrs.attrs));
            } else {
                break;
            }
        }
    };

    while (!pars.at_end()) {
        if (pars.lang_opts_.is_cxx_mode() &&
            pars.check(TokenType::IDENTIFIER) &&
            pars.peek(1).type == TokenType::SCOPE_RESOLUTION &&
            pars.peek(2).type == TokenType::MULTIPLY) {
            Token owner = pars.current();
            cir::TypeId owner_type = pars.collect_session_.lookup_type_name(owner.value);
            cir::TypeRef owner_ref = owner_type.valid()
                ? pars.collect_session_.type_ref(owner_type)
                : pars.collect_session_.type_ref(pars.collect_session_.file().unknown_type());
            if (!owner_type.valid()) {
                error_custloc("member pointer declarator names an unknown class type",
                              owner.loc);
                declarator_has_unsupported_semantics = true;
            } else if (
                pars.collect_session_
                    .type_name_is_active_template_type_parameter(owner.value) &&
                pars.collect_session_.type_contains_type_parameter_pack(
                    owner_type)) {
                error_custloc("unexpanded template parameter pack '" +
                                  std::string(owner.value) +
                                  "' is not supported yet",
                              owner.loc);
                owner_ref = pars.collect_session_.type_ref(
                    pars.collect_session_.file().unknown_type());
                declarator_has_unsupported_semantics = true;
            }
            pars.consume();
            pars.consume();
            pars.consume();
            old_spine.wrap_member_pointer(owner_ref, current_quals);
            current_quals = cir::QualNone;
            parse_post_pointer_qualifiers();
            continue;
        }
        if (pars.match(TokenType::MULTIPLY)) {
            old_spine.wrap_pointer(current_quals);
            current_quals = cir::QualNone;
            parse_post_pointer_qualifiers();
            continue;
        }
        if (pars.match(TokenType::BITWISE_XOR)) {
            old_spine.wrap_block_pointer(current_quals);
            current_quals = cir::QualNone;
            parse_post_pointer_qualifiers();
            continue;
        }
        if (pars.lang_opts_.is_cxx_mode() &&
            (pars.check(TokenType::BITWISE_AND) ||
             pars.check(TokenType::LOGICAL_AND))) {
            bool is_rvalue_reference = pars.match(TokenType::LOGICAL_AND);
            if (!is_rvalue_reference) {
                pars.match(TokenType::BITWISE_AND);
            }
            old_spine.wrap_reference(current_quals,
                                     is_rvalue_reference
                                         ? cir::ReferenceKind::RValue
                                         : cir::ReferenceKind::LValue);
            current_quals = cir::QualNone;
            continue;
        }
        break;
    }

    qualifiers = current_quals;
    loc = pars.current_loc();

    std::optional<DeclaratorTypeSpine> new_spine;
    std::optional<DeclaratorTypeSpine> over_arch;
    NodeId name_node = InvalidNodeId;
    std::vector<NodeId> children;
    bool has_name = false;
    cir::OperatorFunctionIdentity operator_function;
    cir::DeclContextId qualified_context{};
    const collect::Session::TemplateInfo* template_qualifier_info = nullptr;
    std::vector<collect::Session::TemplateArgument>
        template_qualifier_arguments;
    SrcLoc template_qualifier_loc{};
    cir::TypeRef dependent_qualifier_type{};
    std::vector<ParsedParam> parsed_params;
    bool declarator_is_variadic = false;
    bool declarator_has_prototype = true;
    bool declarator_is_kr_style = false;
    bool declarator_has_trailing_return_type = false;
    bool declarator_has_noexcept_specifier = false;
    bool declarator_has_deferred_noexcept_operand = false;
    size_t declarator_noexcept_operand_begin = 0;
    size_t declarator_noexcept_operand_end = 0;
    SrcLoc declarator_noexcept_operand_loc{};
    cir::DeclContextId declarator_noexcept_declaration_context{};
    uint64_t declarator_noexcept_lookup_generation = 0;
    bool declarator_has_trailing_requires_clause = false;
    size_t trailing_requires_constraint_begin = 0;
    size_t trailing_requires_constraint_end = 0;
    std::optional<collect::Session::NormalizedConstraint>
        trailing_requires_normal_form;
    std::optional<bool> trailing_requires_value;
    SrcLoc trailing_requires_loc{};
    std::vector<std::string> declarator_kr_param_names;
    if (prefix && prefix->has_name) {
        name = prefix->name;
        operator_function = prefix->operator_function;
        loc = prefix->loc;
        has_name = true;
        qualified_context = prefix->qualified_context;
        template_qualifier_info = prefix->template_qualifier_info;
        template_qualifier_arguments = prefix->template_qualifier_arguments;
        template_qualifier_loc = prefix->template_qualifier_loc;
        dependent_qualifier_type = prefix->dependent_qualifier_type;
    }

    if (allow_parameter_pack_declarator && allow_abstract &&
        pars.lang_opts_.is_cxx_mode() && pars.match(TokenType::ELLIPSIS)) {
        is_parameter_pack = true;
    }

    auto is_lone_unnamed_void_parameter = [&](const ParsedParam& param) {
        const cir::File& file = pars.collect_session_.file();
        if (!param.name.empty() && param.name != "<anonymous>") {
            return false;
        }
        if (param.type_ref.qualifiers != cir::QualNone || !file.valid(param.type_ref.type)) {
            return false;
        }
        cir::TypeId resolved = file.resolved_type(param.type_ref.type);
        if (!file.valid(resolved) || file.type(resolved).kind != cir::TypeKind::Builtin) {
            return false;
        }
        const auto* payload =
            std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
        return payload && payload->kind == cir::BuiltinTypeKind::Void;
    };

    auto compose_parenthesized_spine = [&]() {
        if (!over_arch) {
            return;
        }
        if (new_spine) {
            over_arch->replace_slot_with(std::move(*new_spine));
            new_spine.reset();
        }
        new_spine.emplace(std::move(*over_arch));
        over_arch.reset();
    };

    auto append_suffix_spine = [&](DeclaratorTypeSpine suffix) {
        if (!new_spine) {
            new_spine.emplace(std::move(suffix));
        } else {
            new_spine->replace_slot_with(std::move(suffix));
        }
        compose_parenthesized_spine();
    };

    auto token_starts_type = [&](size_t offset) {
        const Token& token = pars.peek(offset);
        if (pars.lang_opts_.is_cxx_mode() &&
            pars.starts_cxx_qualified_name(offset)) {

            return pars.peek_cxx_qualified_type(offset).has_value();
        }
        if (token.type == TokenType::IDENTIFIER) {
            if (pars.collect_session_.is_type_name(token.value)) {
                return true;
            }
            if (const BuiltinInfo* builtin =
                    BuiltinRegistry::instance().lookup(token.value);
                builtin && builtin->supported &&
                (builtin->syntax ==
                     BuiltinSyntaxKind::TypeTransform ||
                 builtin->syntax ==
                     BuiltinSyntaxKind::IntegerSequenceType ||
                 builtin->syntax ==
                     BuiltinSyntaxKind::PackElementType)) {
                return true;
            }

            if (pars.lang_opts_.is_cxx_mode() &&
                pars.peek(offset + 1).type == TokenType::LESS_THAN) {
                const collect::Session::TemplateInfo* info =
                    pars.collect_session_.template_info_for_name(token.value);
                return info && (info->is_class_template ||
                                info->is_alias_template);
            }
            return false;
        }
        return pars.is_type_start(token.type);
    };
    auto token_starts_parameter_attribute = [&](size_t offset) {
        TokenType type = pars.peek(offset).type;
        return type == TokenType::ATTRIBUTE_KW ||
               type == TokenType::ALIGNAS ||
               (type == TokenType::LEFT_BRACKET &&
                pars.peek(offset + 1).type == TokenType::LEFT_BRACKET);
    };

    auto finish_spine = [&]() {
        if (!new_spine) {
            if (over_arch) {
                over_arch->replace_slot_with(std::move(old_spine));
                new_spine.emplace(std::move(*over_arch));
                over_arch.reset();
            } else {
                new_spine.emplace(std::move(old_spine));
            }
            return;
        }
        if (over_arch) {
            over_arch->replace_slot_with(std::move(*new_spine));
            new_spine.emplace(std::move(*over_arch));
            over_arch.reset();
        }
        if (new_spine->has_slot()) {
            new_spine->replace_slot_with(std::move(old_spine));
        }
    };

    auto set_declarator_name = [&](std::string parsed_name, SrcLoc parsed_loc) {
        if (has_name) {
            error_custloc("potentially two names in a declarator", parsed_loc);
            declarator_has_unsupported_semantics = true;
            return;
        }
        name = std::move(parsed_name);
        loc = parsed_loc;
        has_name = true;
        name_node = pars.make_node(NodeKind::Name,
                                   pars.last_consumed_raw_index(),
                                   pars.last_consumed_raw_end(),
                                   {},
                                   text_payload(name));
        children.push_back(name_node);
    };

    auto parse_operator_function_name = [&]() -> bool {
        std::optional<Parser::ParsedOperatorFunctionId> operator_id =
            pars.parse_operator_function_id();
        if (!operator_id) {
            return false;
        }
        if (operator_id->has_error) {
            declarator_has_unsupported_semantics = true;
        }
        operator_function = operator_id->identity;
        set_declarator_name(std::move(operator_id->name), operator_id->loc);
        return true;
    };

    auto parse_qualified_declarator_name = [&]() -> bool {
        if (!pars.lang_opts_.is_cxx_mode()) {
            return false;
        }
        bool template_id_qualifier =
            pars.check(TokenType::IDENTIFIER) &&
            pars.peek(1).type == TokenType::LESS_THAN &&
            pars.template_id_precedes_scope(0) &&
            [&] {
                const collect::Session::TemplateInfo* info =
                    pars.collect_session_.template_info_for_name(
                        pars.current().value);
                return info && (info->is_class_template ||
                                info->is_alias_template);
            }();
        if (!pars.check(TokenType::SCOPE_RESOLUTION) &&
            !(pars.check(TokenType::IDENTIFIER) &&
              pars.peek(1).type == TokenType::SCOPE_RESOLUTION) &&
            !template_id_qualifier) {
            return false;
        }

        SrcLoc qualified_loc = pars.current_loc();
        Parser::ParsedNestedName nested = pars.parse_nested_name_specifier();
        if (nested.has_error) {
            declarator_has_unsupported_semantics = true;
        }

        std::string terminal;
        if (pars.check(TokenType::OPERATOR_KW)) {
            std::optional<Parser::ParsedOperatorFunctionId> operator_id =
                pars.parse_operator_function_id();
            if (operator_id) {
                terminal = std::move(operator_id->name);
                operator_function = operator_id->identity;
                declarator_has_unsupported_semantics =
                    declarator_has_unsupported_semantics ||
                    operator_id->has_error;
            }
        } else if (pars.match(TokenType::BITWISE_NOT)) {
            if (!pars.check(TokenType::IDENTIFIER)) {
                error_custloc("expected class name after '~'", qualified_loc);
                declarator_has_unsupported_semantics = true;
            } else {
                terminal = "~" + std::string(pars.current().value);
                pars.consume();
            }
        } else if (pars.check(TokenType::IDENTIFIER)) {
            terminal = pars.current().value;
            pars.consume();
        } else {
            error_custloc("expected a name after the nested name specifier",
                          qualified_loc);
            declarator_has_unsupported_semantics = true;
        }

        set_declarator_name(std::move(terminal), qualified_loc);
        if (!nested.has_error) {
            qualified_context = nested.scope.context;
            template_qualifier_info = nested.template_qualifier_info;
            template_qualifier_arguments =
                std::move(nested.template_qualifier_arguments);
            template_qualifier_loc = nested.template_qualifier_loc;
            dependent_qualifier_type = nested.scope.dependent_type;
        }
        return true;
    };

    auto parse_declarator_name = [&]() -> bool {
        if (parse_qualified_declarator_name()) {
            return true;
        }
        if (parse_operator_function_name()) {
            return true;
        }
        if (pars.lang_opts_.is_cxx_mode() && pars.match(TokenType::BITWISE_NOT)) {
            SrcLoc tilde_loc = pars.last_consumed_loc();
            if (!pars.check(TokenType::IDENTIFIER)) {
                error_custloc("expected class name after '~'", tilde_loc);
                return true;
            }
            std::string destructor_name = "~" + std::string(pars.current().value);
            pars.consume();
            set_declarator_name(std::move(destructor_name), tilde_loc);
            if (!allow_cxx_member_declarator_ids) {
                error_custloc("C++ destructor declarators are not supported",
                              tilde_loc);
                declarator_has_unsupported_semantics = true;
            }
            return true;
        }
        if (!pars.is_identifier_token(pars.current().type)) {
            return false;
        }
        NodeId parsed_name_node = pars.parse_name_node(NodeKind::Name);
        name = node_text(pars.tree_.node(parsed_name_node));
        loc = pars.tree_.node(parsed_name_node).loc;
        has_name = true;
        children.push_back(parsed_name_node);
        name_node = parsed_name_node;
        return true;
    };

    bool parenthesized_structor_declarator =
        !has_name && pars.check(TokenType::LEFT_PAREN) &&
        pars.out_of_line_structor_declaration_ahead();
    auto starts_qualified_name_at = [&](size_t offset) {
        return pars.peek(offset).type == TokenType::SCOPE_RESOLUTION ||
            (pars.is_identifier_token(pars.peek(offset).type) &&
             (pars.peek(offset + 1).type == TokenType::SCOPE_RESOLUTION ||
              (pars.peek(offset + 1).type == TokenType::LESS_THAN &&
               pars.template_id_precedes_scope(offset))));
    };
    auto qualified_name_has_dependent_qualifier_at = [&](size_t offset) {
        if (!starts_qualified_name_at(offset)) {
            return false;
        }
        if (pars.is_identifier_token(pars.peek(offset).type) &&
            pars.collect_session_
                .type_name_is_active_template_type_parameter(
                    pars.peek(offset).value)) {
            return true;
        }
        RevertingTentativeParsingAction tentative(pars);
        for (size_t skipped = 0; skipped < offset; ++skipped) {
            pars.consume();
        }
        Parser::ParsedNestedName nested =
            pars.parse_nested_name_specifier();
        return nested.consumed_any && !nested.has_error &&
            (nested.depends_on_template_parameter ||
             nested.scope.dependent_type.valid());
    };
    auto qualified_name_is_known_expression_at = [&](size_t offset) {
        if (!starts_qualified_name_at(offset)) {
            return false;
        }
        RevertingTentativeParsingAction tentative(pars);
        for (size_t skipped = 0; skipped < offset; ++skipped) {
            pars.consume();
        }
        ParsedExpr expression = pars.parse_cxx_qualified_id_expression();
        return expression.syntax != InvalidNodeId &&
            !expression.sem.has_error && expression.sem.type.valid();
    };
    auto parenthesized_clause_parses_as_parameter = [&]() {

        RevertingTentativeParsingAction tentative(pars);
        size_t diagnostic_watermark = pars.diagnostics_.size();
        pars.consume();
        collect::Session::PrototypeParameterScope prototype_scope =
            pars.collect_session_.begin_prototype_parameter_scope();
        bool complete_parameter_clause = false;
        while (!pars.at_end()) {
            if (pars.match(TokenType::ELLIPSIS)) {
                complete_parameter_clause =
                    pars.match(TokenType::RIGHT_PAREN);
                break;
            }

            collect::Session::ParameterPackPatternCaptureScope
                parameter_pack_capture =
                    pars.collect_session_
                        .begin_parameter_pack_pattern_capture();
            DeclarationParser parameter_parser(
                pars,
                TypeParseContext::type_only(
                    TypeParseContext::Origin::FunctionParameter));
            cir::TypeRef parameter_base =
                parameter_parser.parse_declaration(false, true);
            parameter_parser.allow_parameter_pack_declarator = true;
            ParsedDeclarator parameter =
                parameter_parser.parse_declarator(parameter_base, true);
            (void)pars.collect_session_
                .finish_parameter_pack_pattern_capture(
                    parameter_pack_capture);

            if (!parameter_base.valid() || !parameter.type_ref.valid()) {
                break;
            }
            if (pars.match(TokenType::ASSIGN)) {
                (void)pars.parse_expression(PrecLevel::ASSIGNMENT);
            }
            (void)pars.try_parse_attributes();

            if (parameter.has_name) {
                collect::Session::TemplateInfo::
                    FunctionConstraintParameter projection;
                projection.name = parameter.name;
                projection.type = parameter.type_ref;
                projection.loc = parameter.loc;
                projection.is_parameter_pack =
                    parameter_parser.is_parameter_pack ||
                    parameter.is_parameter_pack;
                projection.type_originates_from_template_parameter =
                    parameter_parser
                        .type_originates_from_template_parameter ||
                    parameter.type_originates_from_template_parameter;
                (void)pars.collect_session_.bind_prototype_parameter(
                    prototype_scope, projection);
            }

            if (pars.match(TokenType::RIGHT_PAREN)) {
                complete_parameter_clause = true;
                break;
            }
            if (!pars.match(TokenType::COMMA) ||
                pars.check(TokenType::RIGHT_PAREN)) {
                break;
            }
        }
        pars.collect_session_.finish_prototype_parameter_scope(
            std::move(prototype_scope));
        return complete_parameter_clause &&
            pars.diagnostics_.size() == diagnostic_watermark;
    };
    bool paren_is_parameter_list =
        !parenthesized_structor_declarator &&
        pars.check(TokenType::LEFT_PAREN) &&
        (has_name ||
         token_starts_parameter_attribute(1) ||
         token_starts_type(1) ||
         (allow_abstract && pars.peek(1).type == TokenType::RIGHT_PAREN));

    std::optional<size_t> nested_begin_cursor;
    size_t nested_begin_raw_end = 0;
    if (!has_name && !paren_is_parameter_list &&
        pars.match(TokenType::LEFT_PAREN)) {
        if (parenthesized_structor_declarator) {

            ParsedDeclarator inner =
                pars.parse_declarator(base_type, allow_abstract, type_context);
            if (!pars.match(TokenType::RIGHT_PAREN)) {
                error("expected ')' after parenthesized constructor declarator-id");
            }
            name = inner.name;
            operator_function = inner.operator_function;
            has_name = inner.has_name;
            qualified_context = inner.qualified_context;
            template_qualifier_info = inner.template_qualifier_info;
            template_qualifier_arguments =
                std::move(inner.template_qualifier_arguments);
            template_qualifier_loc = inner.template_qualifier_loc;
            dependent_qualifier_type = inner.dependent_qualifier_type;
            if (inner.has_name) {
                loc = inner.loc;
            }
            if (inner.syntax != InvalidNodeId) {
                children.push_back(inner.syntax);
            }
            declarator_attrs.append(std::move(inner.attrs.attrs));
            declarator_has_unsupported_semantics =
                declarator_has_unsupported_semantics ||
                inner.has_unsupported_semantics;
        } else {
            nested_begin_cursor = pars.mark();
            nested_begin_raw_end = pars.last_consumed_raw_end_;
            int paren_depth = 1;
            while (!pars.at_end()) {
                TokenType token = pars.current().type;
                if (token == TokenType::LEFT_PAREN) {
                    ++paren_depth;
                } else if (token == TokenType::RIGHT_PAREN) {
                    --paren_depth;
                    if (paren_depth == 0) {
                        break;
                    }
                }
                pars.consume();
            }
            if (!pars.match(TokenType::RIGHT_PAREN)) {
                error("expected ')' after parenthesized declarator");
            }
        }
    } else if (has_name || parse_declarator_name()) {
    } else if (!allow_abstract) {
        cir::TypeRef completed = old_spine.build(pars.collect_session_, base_type);
        completed = merge_qualifiers(
            completed, qualifiers, pars.collect_session_);
        result_type = completed;
        return {InvalidNodeId, {}, completed.type, completed, loc, {}, false};
    }

    struct QualifiedDeclaratorScopeExit {
        collect::Session* session = nullptr;
        std::optional<collect::Session::OutOfLineHeadRebinding>
            header_rebinding;
        ~QualifiedDeclaratorScopeExit() {
            if (session) {
                if (header_rebinding.has_value()) {
                    session->restore_out_of_line_member_head(
                        *header_rebinding);
                }
                session->leave_scope();
            }
        }
    } qualified_declarator_scope;
    if (qualified_context.valid()) {
        const cir::File& file = pars.collect_session_.file();
        if (file.valid(qualified_context) &&
            file.decl_context(qualified_context).kind ==
                cir::DeclContextKind::Record) {
            collect::ScopeEnterResult entered =
                pars.collect_session_.enter_existing_context(
                    qualified_context, collect::ScopeFlags::RecordScope);
            if (entered.scope != collect::InvalidScopeId) {
                qualified_declarator_scope.session = &pars.collect_session_;
                if (pars.qualified_declarator_template_head_wins_) {
                    qualified_declarator_scope.header_rebinding =
                        pars.collect_session_
                            .rebind_active_template_header_in_current_scope(
                                loc);
                }
            }
        }
    }

    while (!pars.at_end()) {
        if (pars.check(TokenType::LEFT_BRACKET) &&
            pars.peek(1).type == TokenType::LEFT_BRACKET) {

            ParsedAttributes attrs = pars.try_parse_attributes();
            declarator_attrs.append(std::move(attrs.attrs));
            continue;
        }
        if (pars.match(TokenType::LEFT_BRACKET)) {
            std::optional<size_t> size;
            cir::ArraySizeKind size_kind = cir::ArraySizeKind::Incomplete;
            cir::InstId size_expr{};
            bool size_expr_is_dependent = false;
            uint32_t extent_param = cir::ArrayTypePayload::no_extent_param;
            cir::TemplateValueExpression dependent_size_expr;
            uint8_t array_qualifiers = cir::QualNone;
            bool saw_static_bound = false;
            auto consume_array_qualifier = [&]() -> bool {
                if (pars.match(TokenType::CONST)) {
                    array_qualifiers |= cir::QualConst;
                    return true;
                }
                if (pars.match(TokenType::VOLATILE)) {
                    array_qualifiers |= cir::QualVolatile;
                    return true;
                }
                if (pars.match(TokenType::RESTRICT)) {
                    array_qualifiers |= cir::QualRestrict;
                    return true;
                }
                if (pars.match(TokenType::ATOMIC)) {
                    array_qualifiers |= cir::QualAtomic;
                    return true;
                }
                if (pars.match(TokenType::NULLABILITY_QUALIFIER)) {

                    return true;
                }
                return false;
            };
            while (true) {
                bool consumed = consume_array_qualifier();
                if (pars.match(TokenType::STATIC)) {
                    saw_static_bound = true;
                    consumed = true;
                }
                if (!consumed) {
                    break;
                }
            }
            if (pars.is_integer_token(pars.current().type) &&
                pars.peek(1).type == TokenType::RIGHT_BRACKET) {

                if (auto parsed = parse_integer_literal_u64(pars.current().value)) {
                    size = static_cast<size_t>(*parsed);
                    size_kind = cir::ArraySizeKind::Constant;
                } else {
                    error_custloc("invalid array bound", pars.current().loc);
                }
                pars.consume();
            } else if (pars.match(TokenType::MULTIPLY)) {
                size_kind = cir::ArraySizeKind::Variable;
            } else if (!pars.check(TokenType::RIGHT_BRACKET)) {
                uint64_t bound_taint_before =
                    pars.collect_session_.pattern_taint();
                ParsedExpr bound = pars.parse_conditional_expression();
                bool bound_references_template_parameter =
                    bound.sem.references_template_value_parameter ||
                    pars.collect_session_.expr_is_value_dependent(bound.sem) ||
                    pars.collect_session_.pattern_taint() !=
                        bound_taint_before;

                uint32_t bound_extent_param =
                    pars.collect_session_.template_value_param_index(
                        bound.sem.entity);

                bound.sem = pars.collect_session_.require_value(
                    std::move(bound.sem),
                    collect::UseContext::RValue,
                    pars.tree_.node(bound.syntax).loc);
                int64_t bound_value = 0;
                if (bound_extent_param !=
                    cir::ArrayTypePayload::no_extent_param) {
                    extent_param = bound_extent_param;
                    size = 0;
                    size_kind = cir::ArraySizeKind::Constant;
                } else if (bound_references_template_parameter) {
                    size_expr = bound.sem.value;
                    size_expr_is_dependent = true;
                    dependent_size_expr =
                        std::move(bound.sem.template_value_expr);
                    size_kind = cir::ArraySizeKind::Variable;
                } else if (pars.collect_session_.try_evaluate_integer_constant(
                               bound.sem, bound_value)) {

                    if (bound_value < 0) {
                        error_custloc("array bound is negative",
                                      pars.tree_.node(bound.syntax).loc);
                    } else {
                        size = static_cast<size_t>(bound_value);
                        size_kind = cir::ArraySizeKind::Constant;
                    }
                } else {
                    size_expr = bound.sem.value;
                    size_kind = cir::ArraySizeKind::Variable;
                    vla_bounds_fragment = pars.collect_session_.chain(
                        std::move(vla_bounds_fragment),
                        std::move(bound.sem.fragment),
                        pars.tree_.node(bound.syntax).loc);
                }
            }
            if (!pars.match(TokenType::RIGHT_BRACKET)) {
                error("expected ']' after array declarator");
            }
            if (saw_static_bound && size_kind == cir::ArraySizeKind::Incomplete) {
                error_custloc("array parameter with 'static' requires a bound",
                              pars.last_consumed_loc());
            }
            append_suffix_spine(
                DeclaratorTypeSpine::array(qualifiers,
                                           size,
                                           size_kind,
                                           size_expr,
                                           array_qualifiers,
                                           size_expr_is_dependent,
                                           extent_param,
                                           std::move(dependent_size_expr)));
            qualifiers = cir::QualNone;
            continue;
        }

        bool starts_constrained_placeholder =
            pars.lang_opts_.is_cxx_mode() &&
            pars.starts_type_constraint_placeholder(1);
        bool starts_parameter_attribute =
            token_starts_parameter_attribute(1);
        bool member_parameter_context =
            type_context.origin ==
                TypeParseContext::Origin::MemberDeclSpecifier;
        bool qualified_declarator_parameter_context =
            qualified_context.valid() || dependent_qualifier_type.valid() ||
            template_qualifier_info;

        bool qualified_name_starts_parameter = false;
        if (starts_qualified_name_at(1)) {
            if (member_parameter_context) {
                qualified_name_starts_parameter = true;
            } else if (qualified_name_has_dependent_qualifier_at(1)) {
                qualified_name_starts_parameter =
                    !qualified_name_is_known_expression_at(1) ||
                    parenthesized_clause_parses_as_parameter();
            } else {
                qualified_name_starts_parameter =
                    !qualified_name_is_known_expression_at(1) &&
                    qualified_declarator_parameter_context;
            }
        }
        bool cxx_parenthesized_initializer =
            pars.lang_opts_.is_cxx_mode() &&
            type_context.origin !=
                TypeParseContext::Origin::MemberDeclSpecifier &&
            !is_out_of_line_structor &&
            has_name &&
            pars.check(TokenType::LEFT_PAREN) &&
            token_starts_type(1) &&
            !parenthesized_clause_parses_as_parameter();
        if (pars.lang_opts_.is_cxx_mode() &&
            has_name &&
            pars.check(TokenType::LEFT_PAREN) &&
            (cxx_parenthesized_initializer ||
             (pars.peek(1).type != TokenType::RIGHT_PAREN &&
              pars.peek(1).type != TokenType::ELLIPSIS &&
              !token_starts_type(1) &&
              !starts_parameter_attribute &&
              !starts_constrained_placeholder &&
              !qualified_name_starts_parameter))) {
            break;
        }

        if (pars.match(TokenType::LEFT_PAREN)) {
            std::vector<ParsedParam> params;
            bool is_variadic = false;
            bool has_prototype = true;
            collect::Session::PrototypeParameterScope
                prototype_parameter_scope;
            TypeParseContext parameter_type_context{};
            if (pars.lang_opts_.is_cxx_mode()) {
                parameter_type_context = TypeParseContext::type_only(
                    TypeParseContext::Origin::FunctionParameter);
            }
            if (type_context.origin ==
                TypeParseContext::Origin::MemberDeclSpecifier) {
                parameter_type_context = TypeParseContext::type_only(
                    TypeParseContext::Origin::MemberParameter);
            } else if (qualified_context.valid() ||
                       dependent_qualifier_type.valid() ||
                       template_qualifier_info) {
                parameter_type_context = TypeParseContext::type_only(
                    TypeParseContext::Origin::QualifiedDeclaratorParameter);
            }
            if (pars.match(TokenType::RIGHT_PAREN)) {

                has_prototype = pars.lang_opts_.is_cxx_mode() ||
                                pars.lang_opts_.is_c23_or_later();
            } else if (pars.check(TokenType::VOID) &&
                       pars.peek(1).type == TokenType::RIGHT_PAREN) {
                pars.consume();
                pars.consume();
            } else if (!pars.lang_opts_.is_cxx_mode() &&
                       pars.check(TokenType::IDENTIFIER) &&
                       !pars.is_type_start(pars.current().type)) {
                std::vector<std::string> names;
                bool valid_identifier_list = true;
                names.push_back(std::string(pars.current().value));
                pars.consume();
                while (pars.match(TokenType::COMMA)) {
                    if (!pars.check(TokenType::IDENTIFIER) ||
                        pars.is_type_start(pars.current().type)) {
                        valid_identifier_list = false;
                        break;
                    }
                    names.push_back(std::string(pars.current().value));
                    pars.consume();
                }
                if (!valid_identifier_list || !pars.match(TokenType::RIGHT_PAREN)) {
                    error("invalid K&R parameter identifier list");
                }
                cir::TypeRef int_type = pars.collect_session_.type_ref(
                    pars.collect_session_.file().builtin_type(cir::BuiltinTypeKind::Int));
                for (const std::string& param_name : names) {
                    params.push_back(ParsedParam{
                        InvalidNodeId,
                        param_name,
                        int_type.type,
                        int_type,
                        loc,
                        {},
                        false,
                        0,
                        0,
                        SrcLoc{}});
                }
                declarator_kr_param_names = std::move(names);
                declarator_is_kr_style = true;
                has_prototype = false;
            } else {

                prototype_parameter_scope =
                    pars.collect_session_.begin_prototype_parameter_scope();
                auto bind_finalized_parameter =
                    [&](ParsedParam& parameter) {
                        collect::Session::TemplateInfo::
                            FunctionConstraintParameter projection;
                        projection.name = parameter.name;
                        projection.type = parameter.type_ref;
                        projection.loc = parameter.loc;
                        projection.is_parameter_pack =
                            parameter.is_parameter_pack;
                        projection.source_parameter_pack_name =
                            parameter.source_parameter_pack_name;
                        projection.is_parameter_pack_expansion_sentinel =
                            parameter.is_parameter_pack_expansion_sentinel;
                        projection.type_originates_from_template_parameter =
                            parameter
                                .type_originates_from_template_parameter;
                        parameter.prototype_entity =
                            pars.collect_session_.bind_prototype_parameter(
                                prototype_parameter_scope, projection);
                    };
                while (!pars.at_end()) {
                    if (pars.match(TokenType::ELLIPSIS)) {
                        is_variadic = true;
                        if (!pars.match(TokenType::RIGHT_PAREN)) {
                            error("expected ')' after variadic parameter list");
                        }
                        break;
                    }
                    size_t param_begin = pars.current_raw_index();

                    size_t pattern_cursor = pars.cursor_;
                    size_t pattern_last_consumed = pars.last_consumed_raw_end_;
                    collect::Session::ParameterPackPatternCaptureScope
                        param_capture_scope;
                    bool capture_parameter_packs =
                        pars.lang_opts_.is_cxx_mode();
                    if (capture_parameter_packs) {
                        param_capture_scope = pars.collect_session_
                            .begin_parameter_pack_pattern_capture();
                    }
                    DeclarationParser param_parser(pars,
                                                   parameter_type_context);

                    param_parser.defer_abbreviated_parameter_rewrite = true;
                    cir::TypeRef param_base = param_parser.parse_declaration(false, true);
                    param_parser.allow_parameter_pack_declarator = true;
                    ParsedDeclarator param_decl = param_parser.parse_declarator(param_base, true);
                    size_t pattern_declarator_end = pars.cursor_;
                    std::vector<collect::Session::ParameterPackIdentity>
                        decorated_packs;
                    if (capture_parameter_packs) {
                        decorated_packs = pars.collect_session_
                            .finish_parameter_pack_pattern_capture(
                                param_capture_scope);
                    }
                    std::vector<NodeId> param_children{param_parser.type_syntax};
                    if (param_decl.syntax != InvalidNodeId) {
                        param_children.push_back(param_decl.syntax);
                    }
                    bool param_is_parameter_pack =
                        param_parser.is_parameter_pack ||
                        param_decl.is_parameter_pack;
                    bool param_type_originates_from_template_parameter =
                        param_parser.type_originates_from_template_parameter ||
                        param_decl.type_originates_from_template_parameter;
                    bool has_default_argument = false;
                    size_t default_argument_begin = 0;
                    size_t default_argument_end = 0;
                    SrcLoc default_argument_loc{};
                    cir::DeclContextId default_argument_declaration_context{};
                    uint64_t default_argument_lookup_generation = 0;
                    bool default_argument_requires_complete_class_replay =
                        false;
                    if (pars.match(TokenType::ASSIGN)) {
                        if (!pars.lang_opts_.is_cxx_mode()) {
                            error_custloc("default arguments are only allowed in C++ declarations",
                                          pars.last_consumed_loc());
                        }
                        default_argument_begin = pars.current_raw_index();
                        default_argument_loc = pars.current_loc();
                        default_argument_declaration_context =
                            pars.collect_session_.current_decl_context();
                        default_argument_lookup_generation =
                            pars.collect_session_.lookup_generation();
                        default_argument_requires_complete_class_replay =
                            pars.should_defer_complete_class_region();
                        bool defer_default_argument_collection =
                            default_argument_requires_complete_class_replay ||
                            (pars.collect_session_.is_instantiating() &&
                             !pars.instantiate_member_parameter_defaults_);
                        size_t diagnostic_watermark =
                            pars.diagnostics_.size();
                        if (defer_default_argument_collection) {
                            pars.collect_session_.begin_speculative_parse();
                        }
                        ParsedExpr default_arg = pars.parse_expression(PrecLevel::ASSIGNMENT);
                        if (defer_default_argument_collection) {
                            pars.collect_session_.rollback_speculative_parse();
                            pars.diagnostics_.resize(diagnostic_watermark);
                        }
                        default_argument_end = pars.current_raw_index();
                        param_children.push_back(default_arg.syntax);
                        has_default_argument = true;
                    }
                    if (param_is_parameter_pack && has_default_argument) {
                        error_custloc(
                            "function parameter pack cannot have a default argument",
                            default_argument_loc);
                    }
                    ParsedAttributes param_attrs = pars.try_parse_attributes();
                    param_decl.attrs.append(std::move(param_attrs.attrs));
                    if (defer_abbreviated_parameter_rewrite) {
                        abbreviated_type_constraints.insert(
                            abbreviated_type_constraints.end(),
                            std::make_move_iterator(
                                param_parser.abbreviated_type_constraints
                                    .begin()),
                            std::make_move_iterator(
                                param_parser.abbreviated_type_constraints
                                    .end()));
                    } else {
                        pars.rewrite_abbreviated_function_parameter(
                            *this,
                            param_decl,
                            param_is_parameter_pack,
                            static_cast<uint32_t>(params.size()),
                            param_parser.abbreviated_type_constraints,
                            param_parser.begin_loc);
                    }
                    if (param_is_parameter_pack && decorated_packs.empty() &&
                        !pars.collect_session_.type_contains_type_parameter_pack(
                            param_decl.type)) {
                        error_custloc(
                            "pack expansion pattern does not contain a template parameter pack",
                            param_decl.loc.isInvalid()
                                ? pars.loc_for_index(param_begin)
                                : param_decl.loc);
                    }
                    param_children.insert(param_children.end(),
                                          param_attrs.syntax.begin(),
                                          param_attrs.syntax.end());
                    if (!param_decl.is_function) {
                        param_decl.type_ref =
                            pars.collect_session_.apply_type_attributes(param_decl.type_ref,
                                                                        param_decl.attrs,
                                                                        param_decl.loc);
                        param_decl.type = param_decl.type_ref.type;
                    }
                    pars.adjust_function_parameter_type(param_decl.type_ref);
                    param_decl.type = param_decl.type_ref.type;
                    NodeId param_syntax = pars.make_node(NodeKind::ParamDecl,
                                                         param_begin,
                                                         pars.last_consumed_raw_end(),
                                                         param_children);

                    if (param_is_parameter_pack && !decorated_packs.empty()) {
                        std::optional<size_t> element_count;
                        bool decorated_dependent = false;
                        for (const auto& pack : decorated_packs) {
                            std::optional<size_t> concrete_count =
                                pars.collect_session_
                                    .parameter_pack_element_count(pack);
                            if (!concrete_count.has_value()) {
                                decorated_dependent = true;
                                break;
                            }
                            if (element_count.has_value() &&
                                *element_count != *concrete_count) {
                                error_custloc(
                                    "pack expansion contains packs with different lengths",
                                    param_decl.loc);
                                *element_count = std::min(*element_count,
                                                          *concrete_count);
                            } else if (!element_count.has_value()) {
                                element_count = *concrete_count;
                            }
                        }
                        if (!decorated_dependent) {
                            size_t resume_cursor = pars.cursor_;
                            size_t resume_last_consumed =
                                pars.last_consumed_raw_end_;
                            std::string source_name = param_decl.has_name
                                ? param_decl.name
                                : std::string{};
                            size_t count = element_count.value_or(0);
                            if (count == 0) {
                                params.push_back(ParsedParam{
                                    InvalidNodeId,
                                    param_decl.has_name ? param_decl.name
                                                        : "<anonymous>",
                                    param_decl.type,
                                    param_decl.type_ref,
                                    param_decl.loc,
                                    param_decl.attrs,
                                    false,
                                    0,
                                    0,
                                    SrcLoc{},
                                    {},
                                    {},
                                    false,
                                    source_name,
                                    true,
                                    param_type_originates_from_template_parameter});
                                bind_finalized_parameter(params.back());
                            }
                            for (size_t i = 0; i < count; ++i) {
                                pars.cursor_ = pattern_cursor;
                                pars.last_consumed_raw_end_ =
                                    pattern_last_consumed;
                                auto element_scope = pars.collect_session_
                                    .begin_parameter_pack_element_replay(
                                        decorated_packs, i);
                                DeclarationParser element_parser(
                                    pars, parameter_type_context);
                                element_parser
                                    .defer_abbreviated_parameter_rewrite =
                                    true;
                                cir::TypeRef element_base =
                                    element_parser.parse_declaration(false,
                                                                     true);
                                element_parser
                                    .allow_parameter_pack_declarator = true;
                                ParsedDeclarator element_decl =
                                    element_parser.parse_declarator(
                                        element_base, true);
                                pars.collect_session_
                                    .finish_parameter_pack_element_replay(
                                        element_scope);
                                if (pars.cursor_ != pattern_declarator_end) {
                                    error_custloc(
                                        "could not replay parameter pack expansion pattern",
                                        param_decl.loc);
                                    pars.cursor_ = pattern_declarator_end;
                                }
                                pars.adjust_function_parameter_type(
                                    element_decl.type_ref);
                                element_decl.type = element_decl.type_ref.type;
                                std::string element_name =
                                    param_decl.has_name
                                        ? param_decl.name + "." +
                                              std::to_string(i)
                                        : "<anonymous>";
                                params.push_back(ParsedParam{
                                    i == 0 ? param_syntax : InvalidNodeId,
                                    std::move(element_name),
                                    element_decl.type,
                                    element_decl.type_ref,
                                    param_decl.loc,
                                    param_decl.attrs,
                                    has_default_argument,
                                    default_argument_begin,
                                    default_argument_end,
                                    default_argument_loc,
                                    {},
                                    {},
                                    false,
                                    source_name,
                                    false,
                                    param_type_originates_from_template_parameter});
                                params.back()
                                    .default_argument_declaration_context =
                                    default_argument_declaration_context;
                                params.back()
                                    .default_argument_lookup_generation =
                                    default_argument_lookup_generation;
                                params.back()
                                    .default_argument_requires_complete_class_replay =
                                    default_argument_requires_complete_class_replay;
                                bind_finalized_parameter(params.back());
                            }
                            pars.cursor_ = resume_cursor;
                            pars.last_consumed_raw_end_ =
                                resume_last_consumed;
                            if (pars.match(TokenType::RIGHT_PAREN)) {
                                break;
                            }
                            if (!pars.match(TokenType::COMMA)) {
                                error("expected ',' or ')' in parameter list");
                                while (!pars.at_end() &&
                                       !pars.check(TokenType::RIGHT_PAREN) &&
                                       !pars.check(TokenType::LEFT_BRACE)) {
                                    pars.consume();
                                }
                                pars.match(TokenType::RIGHT_PAREN);
                                break;
                            }
                            continue;
                        }
                    } else if (!decorated_packs.empty()) {
                        error_custloc(
                            "unexpanded template parameter pack '" +
                                decorated_packs.front().name +
                                "' is not supported yet",
                            param_decl.loc.isInvalid()
                                ? pars.loc_for_index(param_begin)
                                : param_decl.loc);
                    }
                    std::optional<
                        std::vector<collect::Session::TemplateArgument>>
                        concrete_type_pack =
                            param_is_parameter_pack
                                ? pars.collect_session_
                                      .template_type_pack_arguments(
                                          param_decl.type)
                                : std::nullopt;
                    if (concrete_type_pack.has_value()) {
                        if (concrete_type_pack->empty()) {
                            params.push_back(ParsedParam{
                                InvalidNodeId,
                                param_decl.has_name ? param_decl.name
                                                    : "<anonymous>",
                                param_decl.type,
                                param_decl.type_ref,
                                param_decl.loc,
                                param_decl.attrs,
                                false,
                                0,
                                0,
                                SrcLoc{},
                                {},
                                {},
                                false,
                                param_decl.has_name ? param_decl.name
                                                    : std::string{},
                                true,
                                param_type_originates_from_template_parameter});
                            bind_finalized_parameter(params.back());
                        }
                        size_t element_index = 0;
                        for (const collect::Session::TemplateArgument& element :
                             *concrete_type_pack) {
                            if (element.kind != cir::TemplateArgumentKind::Type) {
                                continue;
                            }
                            std::string element_name =
                                param_decl.has_name
                                    ? param_decl.name + "." +
                                          std::to_string(element_index)
                                    : "<anonymous>";
                            cir::TypeRef element_type = element.type;
                            params.push_back(ParsedParam{
                                element_index == 0 ? param_syntax
                                                   : InvalidNodeId,
                                std::move(element_name),
                                element_type.type,
                                element_type,
                                param_decl.loc,
                                param_decl.attrs,
                                has_default_argument,
                                default_argument_begin,
                                default_argument_end,
                                default_argument_loc,
                                {},
                                element_index == 0
                                    ? std::move(param_decl.vla_bounds)
                                    : cir::Fragment{},
                                false,
                                param_decl.has_name ? param_decl.name
                                                    : std::string{},
                                false,
                                param_type_originates_from_template_parameter});
                            params.back().default_argument_declaration_context =
                                default_argument_declaration_context;
                            params.back().default_argument_lookup_generation =
                                default_argument_lookup_generation;
                            params.back()
                                .default_argument_requires_complete_class_replay =
                                default_argument_requires_complete_class_replay;
                            bind_finalized_parameter(params.back());
                            ++element_index;
                        }
                        if (pars.match(TokenType::RIGHT_PAREN)) {
                            break;
                        }
                        if (!pars.match(TokenType::COMMA)) {
                            error("expected ',' or ')' in parameter list");
                            while (!pars.at_end() &&
                                   !pars.check(TokenType::RIGHT_PAREN) &&
                                   !pars.check(TokenType::LEFT_BRACE)) {
                                pars.consume();
                            }
                            pars.match(TokenType::RIGHT_PAREN);
                            break;
                        }
                        continue;
                    }
                    params.push_back(ParsedParam{
                        param_syntax,
                        param_decl.has_name ? param_decl.name : "<anonymous>",
                        param_decl.type,
                        param_decl.type_ref,
                        param_decl.loc,
                        param_decl.attrs,
                        has_default_argument,
                        default_argument_begin,
                        default_argument_end,
                        default_argument_loc,
                        {},
                        std::move(param_decl.vla_bounds),
                        param_is_parameter_pack,
                        {},
                        false,
                        param_type_originates_from_template_parameter});
                    params.back().default_argument_declaration_context =
                        default_argument_declaration_context;
                    params.back().default_argument_lookup_generation =
                        default_argument_lookup_generation;
                    params.back()
                        .default_argument_requires_complete_class_replay =
                        default_argument_requires_complete_class_replay;
                    bind_finalized_parameter(params.back());
                    if (pars.match(TokenType::RIGHT_PAREN)) {
                        break;
                    }
                    if (!pars.match(TokenType::COMMA)) {
                        error("expected ',' or ')' in parameter list");
                        while (!pars.at_end() &&
                               !pars.check(TokenType::RIGHT_PAREN) &&
                               !pars.check(TokenType::LEFT_BRACE)) {
                            pars.consume();
                        }
                        pars.match(TokenType::RIGHT_PAREN);
                        break;
                    }
                }
            }
            if (!is_variadic && params.size() == 1 &&
                is_lone_unnamed_void_parameter(params.front())) {
                params.clear();
            }
            std::optional<cir::TypeRef> fixed_return_type;
            cir::FunctionRefQualifierKind ref_qualifier =
                cir::FunctionRefQualifierKind::None;
            cir::FunctionExceptionSpec exception_spec;
            bool member_is_const = false;
            bool member_is_volatile = false;
            if (pars.lang_opts_.is_cxx_mode()) {
                while (true) {
                    if (pars.match(TokenType::CONST)) {
                        member_is_const = true;
                        continue;
                    }
                    if (pars.match(TokenType::VOLATILE)) {
                        member_is_volatile = true;
                        continue;
                    }
                    break;
                }
                if (pars.match(TokenType::LOGICAL_AND)) {
                    ref_qualifier = cir::FunctionRefQualifierKind::RValue;
                } else if (pars.match(TokenType::BITWISE_AND)) {
                    ref_qualifier = cir::FunctionRefQualifierKind::LValue;
                }
                cir::DeclContextId member_context =
                    qualified_context.valid()
                        ? qualified_context
                        : pars.collect_session_.current_decl_context();
                cir::EntityId member_record =
                    (!is_friend &&
                     (allow_cxx_member_declarator_ids ||
                      qualified_context.valid()))
                        ? pars.collect_session_
                              .enclosing_record_for_context(member_context)
                        : cir::EntityId{};
                std::optional<
                    collect::Session::MemberDeclaratorThisScope>
                    member_this_scope;
                if (member_record.valid()) {
                    member_this_scope.emplace(
                        pars.collect_session_.begin_member_declarator_this(
                            member_record,
                            member_is_const,
                            member_is_volatile,
                            storage_class == StorageClass::Static));
                }
                if (pars.check(TokenType::THROW_KW)) {
                    SrcLoc throw_loc = pars.current_loc();
                    pars.consume();
                    if (!pars.match(TokenType::LEFT_PAREN)) {
                        error_custloc("expected '(' after 'throw'",
                                      throw_loc);
                        declarator_has_unsupported_semantics = true;
                    } else if (pars.match(TokenType::RIGHT_PAREN)) {

                        declarator_has_noexcept_specifier = true;
                        exception_spec =
                            cir::FunctionExceptionSpecKind::NonThrowing;
                    } else {
                        error_custloc("dynamic exception specifications are not supported; use 'noexcept' instead",
                                      throw_loc);
                        int depth = 1;
                        while (!pars.at_end() && depth > 0) {
                            TokenType type = pars.current().type;
                            pars.consume();
                            if (type == TokenType::LEFT_PAREN) ++depth;
                            if (type == TokenType::RIGHT_PAREN) --depth;
                        }
                        declarator_has_unsupported_semantics = true;
                    }
                }
                if (pars.match(TokenType::NOEXCEPT_KW)) {

                    declarator_has_noexcept_specifier = true;
                    exception_spec = cir::FunctionExceptionSpecKind::NonThrowing;
                    if (pars.match(TokenType::LEFT_PAREN)) {
                        size_t operand_begin = pars.current_raw_index();
                        SrcLoc operand_loc = pars.current_loc();
                        cir::DeclContextId declaration_context =
                            pars.collect_session_.current_decl_context();
                        uint64_t lookup_generation =
                            pars.collect_session_.lookup_generation();
                        bool defer =
                            pars.should_defer_complete_class_region();
                        size_t diagnostic_watermark =
                            pars.diagnostics_.size();
                        if (defer) {
                            pars.collect_session_.begin_speculative_parse();
                        }
                        ParsedExpr operand = pars.parse_conditional_expression();
                        size_t operand_end = pars.current_raw_index();
                        if (defer) {
                            pars.collect_session_.rollback_speculative_parse();
                            pars.diagnostics_.resize(diagnostic_watermark);
                        }
                        children.push_back(operand.syntax);
                        if (!pars.match(TokenType::RIGHT_PAREN)) {
                            error_custloc("expected ')' after noexcept specifier operand",
                                          pars.current_loc());
                        }
                        if (defer) {
                            declarator_has_deferred_noexcept_operand = true;
                            declarator_noexcept_operand_begin = operand_begin;
                            declarator_noexcept_operand_end = operand_end;
                            declarator_noexcept_operand_loc = operand_loc;
                            declarator_noexcept_declaration_context =
                                declaration_context;
                            declarator_noexcept_lookup_generation =
                                lookup_generation;
                            exception_spec =
                                cir::FunctionExceptionSpecKind::PotentiallyThrowing;
                        } else {
                            exception_spec =
                                pars.collect_session_.evaluate_noexcept_spec(
                                    operand.sem, pars.last_consumed_loc());
                        }
                    }
                }
                if (pars.match(TokenType::ARROW)) {
                    cir::TypeId trailing_type{};
                    NodeId trailing_syntax = pars.parse_type_name(
                        &trailing_type,
                        nullptr,
                        nullptr,
                        nullptr,
                        nullptr,
                        nullptr,
                        TypeParseContext::type_only(
                            TypeParseContext::Origin::TrailingReturnType));
                    children.push_back(trailing_syntax);
                    fixed_return_type = pars.collect_session_.type_ref(trailing_type);
                    declarator_has_trailing_return_type = true;

                    const cir::File& file = pars.collect_session_.file();
                    cir::TypeId resolved_base = file.valid(base_type.type)
                        ? file.resolved_type(base_type.type)
                        : cir::TypeId{};
                    bool base_is_cxx_auto = false;
                    if (file.valid(resolved_base) &&
                        file.type(resolved_base).kind == cir::TypeKind::Auto) {
                        const auto* auto_payload =
                            std::get_if<cir::AutoTypePayload>(&file.type_payload(resolved_base));
                        base_is_cxx_auto = auto_payload &&
                            auto_payload->flavor == cir::AutoTypeFlavor::Cxx &&
                            base_type.qualifiers == cir::QualNone;
                    }
                    if (!base_is_cxx_auto) {
                        error_custloc("function with trailing return type must specify return type 'auto'",
                                      pars.tree_.node(trailing_syntax).loc);
                        declarator_has_unsupported_semantics = true;
                    }
                }
                if (pars.match(TokenType::REQUIRES_KW)) {
                    SrcLoc requires_loc = pars.last_consumed_loc();
                    size_t constraint_begin = 0;
                    size_t constraint_end = 0;
                    collect::Session::NormalizedConstraint normal_form;
                    std::optional<bool> constraint_value;
                    bool valid =
                        pars.parse_and_validate_constraint_expression(
                            requires_loc,
                            constraint_begin,
                            constraint_end,
                            &constraint_value,
                            &normal_form);
                    if (!valid) {
                        declarator_has_unsupported_semantics = true;
                    } else if (!pars.collect_session_.in_template_header() &&
                               !pars.collect_session_
                                    .in_template_definition() &&
                               !pars.collect_session_
                                    .in_template_instantiation() &&
                               abbreviated_template_info
                                   .invented_function_parameters.empty() &&
                               (!abbreviated_template_target ||
                                abbreviated_template_target
                                    ->invented_function_parameters.empty())) {
                        error_custloc(
                            "a requires-clause cannot appear on a declaration "
                            "of a non-templated function",
                            requires_loc);
                        declarator_has_unsupported_semantics = true;
                    } else {
                        declarator_has_trailing_requires_clause = true;
                        trailing_requires_constraint_begin = constraint_begin;
                        trailing_requires_constraint_end = constraint_end;
                        trailing_requires_normal_form =
                            std::move(normal_form);
                        trailing_requires_value = constraint_value;
                        trailing_requires_loc = requires_loc;
                    }
                }
                if (member_this_scope.has_value()) {
                    pars.collect_session_.finish_member_declarator_this(
                        std::move(*member_this_scope));
                }
            }

            if (prototype_parameter_scope.active) {
                pars.collect_session_.finish_prototype_parameter_scope(
                    std::move(prototype_parameter_scope));
            }
            parsed_params = params;
            declarator_is_variadic = is_variadic;
            declarator_has_prototype = has_prototype;
            std::vector<cir::TypeRef> param_types;
            std::vector<uint8_t> parameter_pack_flags;
            bool has_parameter_pack = false;
            param_types.reserve(params.size());
            parameter_pack_flags.reserve(params.size());
            for (const ParsedParam& param : params) {
                if (param.is_parameter_pack_expansion_sentinel) {
                    continue;
                }
                param_types.push_back(param.type_ref);
                uint8_t pack_flag = param.is_parameter_pack ? 1 : 0;
                parameter_pack_flags.push_back(pack_flag);
                has_parameter_pack = has_parameter_pack || pack_flag != 0;
            }
            if (!has_parameter_pack) {
                parameter_pack_flags.clear();
            }
            append_suffix_spine(DeclaratorTypeSpine::function(std::move(param_types),
                                                              std::move(parameter_pack_flags),
                                                              is_variadic,
                                                              has_prototype,
                                                              qualifiers,
                                                              cir::QualNone,
                                                              fixed_return_type,
                                                              ref_qualifier,
                                                              std::move(exception_spec),
                                                              member_is_const,
                                                              member_is_volatile));
            qualifiers = cir::QualNone;
            continue;
        }
        break;
    }

    finish_spine();
    bool declarator_has_operators = !new_spine->is_slot_only();
    cir::TypeRef completed = new_spine->build(pars.collect_session_, base_type);
    completed = merge_qualifiers(
        completed, qualifiers, pars.collect_session_);

    if (nested_begin_cursor.has_value()) {
        size_t resume_cursor = pars.mark();
        size_t resume_raw_end = pars.last_consumed_raw_end_;
        pars.cursor_ = *nested_begin_cursor;
        pars.last_consumed_raw_end_ = nested_begin_raw_end;
        DeclarationParser inner_parser(pars, type_context);
        inner_parser.allow_parameter_pack_declarator =
            allow_parameter_pack_declarator;
        inner_parser.allow_cxx_member_declarator_ids =
            allow_cxx_member_declarator_ids;
        inner_parser.defer_abbreviated_parameter_rewrite =
            defer_abbreviated_parameter_rewrite;
        ParsedDeclarator inner =
            inner_parser.parse_declarator(completed, allow_abstract);
        if (!pars.match(TokenType::RIGHT_PAREN)) {
            error("expected ')' after parenthesized declarator");
        }
        pars.cursor_ = resume_cursor;
        pars.last_consumed_raw_end_ = resume_raw_end;

        completed = inner.type_ref;
        is_parameter_pack = is_parameter_pack || inner.is_parameter_pack;
        name = inner.name;
        operator_function = inner.operator_function;
        has_name = inner.has_name;
        qualified_context = inner.qualified_context;
        template_qualifier_info = inner.template_qualifier_info;
        template_qualifier_arguments =
            std::move(inner.template_qualifier_arguments);
        template_qualifier_loc = inner.template_qualifier_loc;
        dependent_qualifier_type = inner.dependent_qualifier_type;
        if (inner.has_name) {
            loc = inner.loc;
        }
        declarator_attrs.append(std::move(inner.attrs.attrs));
        if (inner.is_function && inner.has_declarator_operators) {
            parsed_params = std::move(inner.params);
            declarator_is_variadic = inner.is_variadic;
            declarator_has_prototype = inner.has_prototype;
            declarator_is_kr_style = inner.is_kr_style;
            declarator_kr_param_names = std::move(inner.kr_param_names);
            declarator_has_noexcept_specifier =
                inner.has_noexcept_specifier;
            declarator_has_deferred_noexcept_operand =
                inner.has_deferred_noexcept_operand;
            declarator_noexcept_operand_begin = inner.noexcept_operand_begin;
            declarator_noexcept_operand_end = inner.noexcept_operand_end;
            declarator_noexcept_operand_loc = inner.noexcept_operand_loc;
            declarator_noexcept_declaration_context =
                inner.noexcept_declaration_context;
            declarator_noexcept_lookup_generation =
                inner.noexcept_lookup_generation;
            if (inner.has_trailing_requires_clause) {
                declarator_has_trailing_requires_clause = true;
                trailing_requires_constraint_begin =
                    inner.trailing_requires_constraint_begin;
                trailing_requires_constraint_end =
                    inner.trailing_requires_constraint_end;
                trailing_requires_normal_form =
                    std::move(inner.trailing_requires_normal_form);
                trailing_requires_value = inner.trailing_requires_value;
                trailing_requires_loc = inner.trailing_requires_loc;
            }
        }
        declarator_has_operators =
            declarator_has_operators || inner.has_declarator_operators;
        vla_bounds_fragment = pars.collect_session_.chain(
            std::move(vla_bounds_fragment), std::move(inner.vla_bounds), loc);
        declarator_has_unsupported_semantics =
            declarator_has_unsupported_semantics || inner.has_unsupported_semantics;
        if (inner.abbreviated_template_info.has_value() &&
            !abbreviated_template_target) {
            abbreviated_template_info =
                std::move(*inner.abbreviated_template_info);
        }
    }
    NodeId syntax = InvalidNodeId;
    if (has_name || pars.made_progress(declarator_mark)) {
        syntax = pars.make_node(NodeKind::Name,
                                begin,
                                pars.last_consumed_raw_end(),
                                children,
                                text_payload(name));
    }
    const cir::File& file = pars.collect_session_.file();
    cir::TypeId resolved = file.valid(completed.type)
        ? file.resolved_type(completed.type)
        : cir::TypeId{};
    bool final_is_function = file.valid(resolved) &&
        file.type(resolved).kind == cir::TypeKind::Function;
    bool continues_as_explicit_template_id_function =
        !final_is_function && has_name &&
        pars.lang_opts_.is_cxx_mode() &&
        pars.check(TokenType::LESS_THAN) &&
        pars.peek(1).type == TokenType::GREATER_THAN &&
        pars.peek(2).type == TokenType::LEFT_PAREN;

    bool constexpr_const_is_implicit =
        pars.lang_opts_.is_cxx_mode() && is_constexpr &&
        !final_is_function && !continues_as_explicit_template_id_function &&
        !pars.collect_session_.is_reference_type(completed.type) &&
        (completed.qualifiers & cir::QualConst) == 0;
    if (constexpr_const_is_implicit) {
        completed.qualifiers = static_cast<uint8_t>(
            completed.qualifiers | cir::QualConst);
    }
    result_type = completed;
    declarator_syntax = syntax;
    ParsedDeclarator result;
    result.syntax = syntax;
    result.name = name;
    result.operator_function = operator_function;
    result.type = completed.type;
    result.type_ref = completed;
    result.loc = loc;

    for (const ParsedAttribute& attr : leading_attrs.attrs) {
        if (attr.kind == AttributeKind::Mode ||
            attr.kind == AttributeKind::VectorSize ||
            attr.kind == AttributeKind::ExtVectorType ||
            attr.kind == AttributeKind::NeonVectorType) {
            continue;
        }
        declarator_attrs.attrs.push_back(attr);
    }
    result.attrs = std::move(declarator_attrs);
    result.has_name = has_name;
    result.is_function = final_is_function;
    result.constexpr_const_is_implicit = constexpr_const_is_implicit;
    result.is_variadic = declarator_is_variadic;
    result.has_prototype = declarator_has_prototype;
    result.is_kr_style = declarator_is_kr_style;
    result.has_trailing_return_type = declarator_has_trailing_return_type;
    result.has_placeholder_type_constraint =
        has_placeholder_type_constraint;
    result.placeholder_type_constraint_begin =
        placeholder_type_constraint_begin;
    result.placeholder_type_constraint_end =
        placeholder_type_constraint_end;
    result.placeholder_type_constraint_loc =
        placeholder_type_constraint_loc;
    result.has_noexcept_specifier = declarator_has_noexcept_specifier;
    result.has_deferred_noexcept_operand =
        declarator_has_deferred_noexcept_operand;
    result.noexcept_operand_begin = declarator_noexcept_operand_begin;
    result.noexcept_operand_end = declarator_noexcept_operand_end;
    result.noexcept_operand_loc = declarator_noexcept_operand_loc;
    result.noexcept_declaration_context =
        declarator_noexcept_declaration_context;
    result.noexcept_lookup_generation =
        declarator_noexcept_lookup_generation;
    result.has_trailing_requires_clause =
        declarator_has_trailing_requires_clause;
    result.trailing_requires_constraint_begin =
        trailing_requires_constraint_begin;
    result.trailing_requires_constraint_end =
        trailing_requires_constraint_end;
    result.trailing_requires_normal_form =
        std::move(trailing_requires_normal_form);
    result.trailing_requires_value = trailing_requires_value;
    result.trailing_requires_loc = trailing_requires_loc;
    result.has_declarator_operators = declarator_has_operators;
    result.has_unsupported_semantics =
        declarator_has_unsupported_semantics;
    result.qualified_context = qualified_context;
    result.template_qualifier_info = template_qualifier_info;
    result.template_qualifier_arguments =
        std::move(template_qualifier_arguments);
    result.template_qualifier_loc = template_qualifier_loc;
    result.dependent_qualifier_type = dependent_qualifier_type;
    result.kr_param_names = std::move(declarator_kr_param_names);
    result.params = std::move(parsed_params);
    if (!abbreviated_template_target &&
        !abbreviated_template_info.invented_function_parameters.empty()) {
        result.abbreviated_template_info =
            std::move(abbreviated_template_info);
    }
    result.deduced_class_template_info = deduced_class_template_info;
    result.deduced_class_template_loc = deduced_class_template_loc;
    result.vla_bounds = std::move(vla_bounds_fragment);
    result.is_parameter_pack = is_parameter_pack;
    result.type_originates_from_template_parameter =
        type_originates_from_template_parameter;
    return result;
}

Parser::ParsedDeclarator Parser::parse_declarator(cir::TypeRef base_type,
                                                  bool allow_abstract,
                                                  TypeParseContext context) {
    DeclarationParser parser(*this, context);
    parser.first_half = without_qualifiers(base_type);
    parser.base_qualifiers = base_type.qualifiers;
    parser.qualifiers = base_type.qualifiers;
    return parser.parse_declarator(without_qualifiers(base_type), allow_abstract);
}

} // namespace aburi::syntax
