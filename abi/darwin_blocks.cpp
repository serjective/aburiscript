#include "darwin_blocks.h"

#include <algorithm>
#include <cctype>
#include <string>
#include <unordered_set>

#include "../lang_options.h"
#include "../ast/ast.h"
#include "target_info.h"
#include "../ast/types.h"

namespace darwin_blocks {

namespace {

std::string lowercase_copy(std::string value) {
    std::transform(value.begin(), value.end(), value.begin(),
        [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return value;
}

bool triple_mentions_darwin(std::string triple) {
    if (triple.empty()) {
        return false;
    }
    triple = lowercase_copy(std::move(triple));
    return triple.find("apple-darwin") != std::string::npos ||
           triple.find("-darwin") != std::string::npos ||
           triple.find("apple-macos") != std::string::npos ||
           triple.find("apple-macosx") != std::string::npos;
}

size_t align_up(size_t value, size_t alignment) {
    if (alignment <= 1) {
        return value;
    }
    size_t remainder = value % alignment;
    if (remainder == 0) {
        return value;
    }
    return value + (alignment - remainder);
}

size_t pointer_size_bytes(const TargetInfo* target) {
    if (target && target->pointer_width > 0) {
        return static_cast<size_t>(target->pointer_width / 8);
    }
    return sizeof(void*);
}

size_t long_size_bytes(const TargetInfo* target) {
    if (target && target->long_width > 0) {
        return static_cast<size_t>(target->long_width / 8);
    }
    return sizeof(long);
}

size_t long_double_storage_bytes(const TargetInfo* target) {
    if (target && target->long_double_width > 0) {
        if (target->long_double_width == 80) {
            return 16;
        }
        return static_cast<size_t>((target->long_double_width + 7) / 8);
    }
    return sizeof(long double);
}

size_t long_double_alignment_bytes(const TargetInfo* target) {
    if (target && target->long_double_width == 80) {
        return 16;
    }
    size_t storage = long_double_storage_bytes(target);
    return storage == 0 ? 1 : storage;
}

struct EncodedTypeInfo {
    std::string encoding;
    size_t size = 0;
    size_t alignment = 1;
};

EncodedTypeInfo encode_type(QualType type,
                            const TargetInfo* target,
                            std::unordered_set<const CType*>& active_records);

EncodedTypeInfo encode_builtin_type(const BuiltinType* builtin,
                                    const TargetInfo* target) {
    if (!builtin) {
        return {"?", 0, 1};
    }

    switch (builtin->builtin_kind) {
        case BuiltinTypes::Void:
            return {"v", 0, 1};
        case BuiltinTypes::Bool:
            return {"B", 1, 1};
        case BuiltinTypes::Char:
            return {"c", 1, 1};
        case BuiltinTypes::UChar:
            return {"C", 1, 1};
        case BuiltinTypes::Short:
            return {"s", 2, 2};
        case BuiltinTypes::UShort:
            return {"S", 2, 2};
        case BuiltinTypes::Int:
            return {"i", 4, 4};
        case BuiltinTypes::UInt:
            return {"I", 4, 4};
        case BuiltinTypes::Long: {
            size_t bytes = long_size_bytes(target);
            return {bytes == 4 ? "l" : "q", bytes, bytes};
        }
        case BuiltinTypes::ULong: {
            size_t bytes = long_size_bytes(target);
            return {bytes == 4 ? "L" : "Q", bytes, bytes};
        }
        case BuiltinTypes::LongLong:
            return {"q", 8, 8};
        case BuiltinTypes::ULongLong:
            return {"Q", 8, 8};
        case BuiltinTypes::Int128:
            return {"t", 16, 16};
        case BuiltinTypes::UInt128:
            return {"T", 16, 16};
        case BuiltinTypes::Float16:
            return {"?", 2, 2};
        case BuiltinTypes::Float:
            return {"f", 4, 4};
        case BuiltinTypes::Double:
            return {"d", 8, 8};
        case BuiltinTypes::LongDouble: {
            size_t bytes = long_double_storage_bytes(target);
            size_t align = long_double_alignment_bytes(target);
            return {"D", bytes, align};
        }
        case BuiltinTypes::NullPtr: {
            size_t bytes = pointer_size_bytes(target);
            return {"^v", bytes, bytes};
        }
    }
    return {"?", 0, 1};
}

EncodedTypeInfo encode_record_type(const ObjectType* object_type,
                                   const TargetInfo* target,
                                   std::unordered_set<const CType*>& active_records) {
    (void)target;
    if (!object_type) {
        return {"?", 0, 1};
    }

    const TagDecl* tag_decl = object_type->get_decl();
    std::string name =
        (tag_decl && !tag_decl->get_tag_name().empty())
            ? tag_decl->get_tag_name()
            : "?";
    std::string encoding = object_type->is_union ? "(" : "{";
    encoding += name;
    encoding += "=";

    if (!object_type->isIncomplete() &&
        active_records.insert(object_type).second) {
        for (const auto& field : object_type->semantic_fields()) {
            encoding += encode_type(field.type, target, active_records).encoding;
        }
        active_records.erase(object_type);
    }

    encoding += object_type->is_union ? ")" : "}";

    auto* mutable_object = const_cast<ObjectType*>(object_type);
    size_t size =
        static_cast<size_t>(std::max<int64_t>(0, mutable_object->getWidthBytes()));
    size_t align = std::max<size_t>(1, mutable_object->getAlignment());
    return {encoding, size, align};
}

EncodedTypeInfo encode_type(QualType type,
                            const TargetInfo* target,
                            std::unordered_set<const CType*>& active_records) {
    if (!type) {
        return {"?", 0, 1};
    }

    QualType canonical = desugar_type(type);
    if (!canonical) {
        canonical = type;
    }

    if (auto* reference = canonical.as<ReferenceType>()) {
        canonical = QualType(std::make_shared<PointerType>(reference->referred_type));
    }

    if (auto* enum_type = canonical.as<EnumType>()) {
        auto underlying = enum_type->semantic_underlying_type();
        if (underlying) {
            return encode_type(QualType(underlying), target, active_records);
        }
        return {"i", 4, 4};
    }

    if (auto* builtin = canonical.as<BuiltinType>()) {
        return encode_builtin_type(builtin, target);
    }

    if (auto* pointer = canonical.as<PointerType>()) {
        size_t bytes = pointer_size_bytes(target);
        QualType pointee = desugar_type(pointer->pointed_type);
        if (!pointee) {
            pointee = pointer->pointed_type;
        }
        if (auto* pointee_builtin = pointee.as<BuiltinType>()) {
            if (pointee_builtin->builtin_kind == BuiltinTypes::Char ||
                pointee_builtin->builtin_kind == BuiltinTypes::UChar) {
                return {"*", bytes, bytes};
            }
            if (pointee_builtin->builtin_kind == BuiltinTypes::Void) {
                return {"^v", bytes, bytes};
            }
        }
        if (pointee && pointee->kind == TypeKind::Function) {
            return {"^?", bytes, bytes};
        }
        auto pointee_info = encode_type(pointee, target, active_records);
        return {"^" + pointee_info.encoding, bytes, bytes};
    }

    if (canonical->kind == TypeKind::BlockPointer) {
        size_t bytes = pointer_size_bytes(target);
        return {"@?", bytes, bytes};
    }

    if (auto* array = canonical.as<ArrayType>()) {
        auto element_info = encode_type(array->element_type, target, active_records);
        if (array->size_kind == ArraySizeKind::Constant && array->size.has_value()) {
            size_t count = static_cast<size_t>(*array->size);
            return {
                "[" + std::to_string(count) + element_info.encoding + "]",
                element_info.size * count,
                std::max<size_t>(1, element_info.alignment)
            };
        }
        return {"?", 0, std::max<size_t>(1, element_info.alignment)};
    }

    if (auto* object = canonical.as<ObjectType>()) {
        return encode_record_type(object, target, active_records);
    }

    if (auto* complex_type = canonical.as<ComplexType>()) {
        auto element_info = encode_type(QualType(complex_type->element_type), target, active_records);
        return {
            "j" + element_info.encoding,
            element_info.size * 2,
            std::max<size_t>(1, element_info.alignment)
        };
    }

    if (auto* vector_type = canonical.as<VectorType>()) {
        auto element_info = encode_type(vector_type->element_type, target, active_records);
        size_t element_size = std::max<size_t>(1, element_info.size);
        size_t element_count = vector_type->total_bytes / element_size;
        size_t align = vector_type->total_bytes == 0 ? 1 : vector_type->total_bytes;
        return {
            "[" + std::to_string(element_count) + element_info.encoding + "]",
            vector_type->total_bytes,
            align
        };
    }

    if (canonical->kind == TypeKind::Function) {
        size_t bytes = pointer_size_bytes(target);
        return {"^?", bytes, bytes};
    }

    size_t size = static_cast<size_t>(std::max<int64_t>(0, canonical->getWidthBytes()));
    size_t align = std::max<size_t>(1, size == 0 ? 1 : size);
    return {"?", size, align};
}

} // namespace

bool target_supports_darwin_blocks(const TargetInfo& target) {
    if (!target.triple.empty()) {
        return triple_mentions_darwin(target.triple);
    }
    return target.os == TargetOS::MACOS;
}

bool blocks_default_enabled_for_target(const TargetInfo& target) {
    return target_supports_darwin_blocks(target);
}

bool blocks_enabled_for_langopts(const LangOptions& lang_opts,
                                 const TargetInfo& target) {
    if (!target_supports_darwin_blocks(target)) {
        return false;
    }
    switch (lang_opts.blocks_mode) {
        case BlocksMode::Default:
            return blocks_default_enabled_for_target(target);
        case BlocksMode::Enabled:
            return true;
        case BlocksMode::Disabled:
            return false;
    }
    return false;
}

const BlockLiteralHeaderLayout& block_literal_header_layout() {
    static const BlockLiteralHeaderLayout kLayout;
    return kLayout;
}

const BlockDescriptorLayout& block_descriptor_layout() {
    static const BlockDescriptorLayout kLayout;
    return kLayout;
}

uint32_t block_descriptor_signature_offset(bool has_copy_dispose_helpers) {
    const auto& layout = block_descriptor_layout();
    return has_copy_dispose_helpers
        ? layout.signature_offset_with_copy_dispose
        : layout.signature_offset_without_copy_dispose;
}

uint32_t block_descriptor_layout_string_offset(bool has_copy_dispose_helpers) {
    const auto& layout = block_descriptor_layout();
    return has_copy_dispose_helpers
        ? layout.layout_offset_with_copy_dispose
        : layout.layout_offset_without_copy_dispose;
}

const BlockByrefLayout& block_byref_layout() {
    static const BlockByrefLayout kLayout;
    return kLayout;
}

uint32_t block_byref_header_size(bool has_copy_dispose_helpers) {
    const auto& layout = block_byref_layout();
    return has_copy_dispose_helpers
        ? layout.payload_offset_with_helpers
        : layout.payload_offset_without_helpers;
}

uint32_t block_byref_payload_offset(bool has_copy_dispose_helpers) {
    return block_byref_header_size(has_copy_dispose_helpers);
}

std::string_view runtime_class_symbol(ConcreteBlockStorageClass storage) {
    switch (storage) {
        case ConcreteBlockStorageClass::Global:
            return "_NSConcreteGlobalBlock";
        case ConcreteBlockStorageClass::Stack:
            return "_NSConcreteStackBlock";
    }
    return "_NSConcreteStackBlock";
}

std::string encode_block_invoke_signature(QualType invoke_type,
                                          const TargetInfo* target) {
    auto function_type = desugar_type(invoke_type).as_shared<FunctionType>();
    if (!function_type || function_type->parameters.empty()) {
        return {};
    }

    std::unordered_set<const CType*> active_records;
    auto return_info = encode_type(function_type->ret_type, target, active_records);

    size_t pointer_bytes = pointer_size_bytes(target);
    size_t offset = pointer_bytes;
    std::vector<std::pair<std::string, size_t>> parameter_encodings;
    parameter_encodings.emplace_back("@?", 0);

    for (size_t index = 1; index < function_type->parameters.size(); ++index) {
        auto param_info =
            encode_type(function_type->parameters[index], target, active_records);
        size_t alignment = std::max<size_t>(1, param_info.alignment);
        offset = align_up(offset, alignment);
        parameter_encodings.emplace_back(param_info.encoding, offset);
        offset += param_info.size;
    }

    std::string signature =
        return_info.encoding.empty() ? "?" : return_info.encoding;
    signature += std::to_string(offset);
    for (const auto& [encoding, param_offset] : parameter_encodings) {
        signature += encoding;
        signature += std::to_string(param_offset);
    }
    return signature;
}

} // namespace darwin_blocks
