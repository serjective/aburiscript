#include "objc_runtime.h"

#include <algorithm>
#include <variant>
#include <vector>

#include "../cir/file.h"
#include "../cir/layout.h"
#include "call_classify.h"
#include "target_info.h"

namespace aburi::objc_runtime {
namespace {

cir::TypeId strip_sugar(const cir::File& file, cir::TypeId id) {
    cir::TypeId resolved = file.resolved_type(id);
    while (file.valid(resolved) &&
           file.type(resolved).kind == cir::TypeKind::Typedef) {
        const auto* payload =
            std::get_if<cir::TypedefTypePayload>(&file.type_payload(resolved));
        if (!payload || !payload->underlying_type.valid()) {
            break;
        }
        cir::TypeId next = file.resolved_type(payload->underlying_type.type);
        if (!file.valid(next) || next == resolved) {
            break;
        }
        resolved = next;
    }
    return resolved;
}

const cir::BuiltinTypePayload* builtin_payload(const cir::File& file,
                                               cir::TypeId resolved) {
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Builtin) {
        return nullptr;
    }
    return std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
}

std::string_view builtin_encoding(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Void: return "v";
        case cir::BuiltinTypeKind::Bool: return "B";
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar: return "c";
        case cir::BuiltinTypeKind::UChar: return "C";
        case cir::BuiltinTypeKind::Char8: return "C";
        case cir::BuiltinTypeKind::Short: return "s";
        case cir::BuiltinTypeKind::UShort: return "S";
        case cir::BuiltinTypeKind::Int: return "i";
        case cir::BuiltinTypeKind::UInt: return "I";
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::LongLong: return "q";
        case cir::BuiltinTypeKind::ULong:
        case cir::BuiltinTypeKind::ULongLong:
        case cir::BuiltinTypeKind::USize: return "Q";
        case cir::BuiltinTypeKind::Int128: return "t";
        case cir::BuiltinTypeKind::UInt128: return "T";
        case cir::BuiltinTypeKind::Float: return "f";
        case cir::BuiltinTypeKind::Double: return "d";
        case cir::BuiltinTypeKind::LongDouble: return "D";

        case cir::BuiltinTypeKind::WChar: return "i";
        case cir::BuiltinTypeKind::Char16: return "S";
        case cir::BuiltinTypeKind::Char32: return "I";
        case cir::BuiltinTypeKind::NullPtr: return "*";
        default: return "?";
    }
}

bool is_char_like(cir::BuiltinTypeKind kind) {
    return kind == cir::BuiltinTypeKind::Char ||
           kind == cir::BuiltinTypeKind::SChar ||
           kind == cir::BuiltinTypeKind::UChar ||
           kind == cir::BuiltinTypeKind::Char8;
}

std::string_view opaque_objc_pointer_encoding(const cir::File& file,
                                              cir::TypeId pointee) {
    const auto* payload =
        std::get_if<cir::RecordTypePayload>(&file.type_payload(pointee));
    if (!payload || !file.valid(payload->name)) {
        return {};
    }
    std::string_view tag = file.name(payload->name);

    if (tag.rfind("struct ", 0) == 0) {
        tag.remove_prefix(7);
    }
    if (tag == "objc_object") {
        return "@";
    }
    if (tag == "objc_class") {
        return "#";
    }
    if (tag == "objc_selector") {
        return ":";
    }
    return {};
}

void encode_impl(const cir::File& file,
                 cir::TypeRef type,
                 bool expand_structs,
                 bool in_field,
                 std::string& out);

void encode_pointer(const cir::File& file,
                    cir::TypeRef pointee,
                    std::string& out) {
    if (pointee.qualifiers & cir::QualConst) {
        out += 'r';
    }
    cir::TypeId resolved = strip_sugar(file, pointee.type);
    if (file.valid(resolved)) {
        if (file.type(resolved).kind == cir::TypeKind::Record) {
            std::string_view opaque =
                opaque_objc_pointer_encoding(file, resolved);
            if (!opaque.empty()) {
                out += opaque;
                return;
            }
        }
        if (const cir::BuiltinTypePayload* builtin =
                builtin_payload(file, resolved)) {
            if (is_char_like(builtin->kind)) {
                out += '*';
                return;
            }
        }
    }
    out += '^';

    cir::TypeRef stripped = pointee;
    stripped.qualifiers &= static_cast<uint8_t>(~cir::QualConst);
    encode_impl(file, stripped, /*expand_structs=*/false, /*in_field=*/false,
                out);
}

void encode_record(const cir::File& file,
                   cir::TypeId record,
                   const cir::RecordTypePayload& payload,
                   bool expand_structs,
                   std::string& out) {
    out += payload.is_union ? '(' : '{';
    if (file.valid(payload.name)) {
        out += file.name(payload.name);
    } else {
        out += '?';
    }
    out += '=';
    if (expand_structs) {
        if (const cir::RecordFacts* facts = file.record_facts_for_type(record)) {
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.is_virtual_base_storage) {
                    continue;
                }
                if (field.is_bitfield) {
                    out += 'b';
                    out += std::to_string(field.bit_width);
                    continue;
                }
                encode_impl(file, field.type, expand_structs,
                            /*in_field=*/true, out);
            }
        }
    }
    out += payload.is_union ? ')' : '}';
}

void encode_impl(const cir::File& file,
                 cir::TypeRef type,
                 bool expand_structs,
                 bool in_field,
                 std::string& out) {
    if (type.qualifiers & cir::QualConst) {
        out += 'r';
    }
    cir::TypeId resolved = strip_sugar(file, type.type);
    if (!file.valid(resolved)) {
        out += '?';
        return;
    }
    const cir::TypePayload& payload = file.type_payload(resolved);
    switch (file.type(resolved).kind) {
        case cir::TypeKind::Builtin: {
            const auto* builtin = std::get_if<cir::BuiltinTypePayload>(&payload);
            out += builtin ? builtin_encoding(builtin->kind) : "?";
            return;
        }
        case cir::TypeKind::Enum: {

            const auto* enum_payload = std::get_if<cir::EnumTypePayload>(&payload);
            if (enum_payload && enum_payload->underlying_type.valid()) {
                const cir::BuiltinTypePayload* builtin = builtin_payload(
                    file, strip_sugar(file, enum_payload->underlying_type.type));
                if (builtin) {
                    out += builtin_encoding(builtin->kind);
                    return;
                }
            }
            out += 'i';
            return;
        }
        case cir::TypeKind::Pointer: {
            const auto* pointer = std::get_if<cir::PointerTypePayload>(&payload);
            if (!pointer) {
                out += '?';
                return;
            }
            cir::TypeId pointee = strip_sugar(file, pointer->pointee.type);
            if (file.valid(pointee) &&
                file.type(pointee).kind == cir::TypeKind::Function) {
                out += "^?";
                return;
            }
            encode_pointer(file, pointer->pointee, out);
            return;
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {

            const auto* reference =
                std::get_if<cir::ReferenceTypePayload>(&payload);
            if (!reference) {
                out += '?';
                return;
            }
            encode_pointer(file, reference->referred_type, out);
            return;
        }
        case cir::TypeKind::BlockPointer:
            out += "@?";
            return;
        case cir::TypeKind::Function:
            out += '?';
            return;
        case cir::TypeKind::Array: {
            const auto* array = std::get_if<cir::ArrayTypePayload>(&payload);
            if (!array) {
                out += '?';
                return;
            }
            if (array->size_kind == cir::ArraySizeKind::Constant &&
                array->size) {
                out += '[';
                out += std::to_string(*array->size);
                encode_impl(file, array->element_type, expand_structs, in_field,
                            out);
                out += ']';
            } else if (in_field) {

                out += "[0";
                encode_impl(file, array->element_type, expand_structs, in_field,
                            out);
                out += ']';
            } else {

                encode_pointer(file, array->element_type, out);
            }
            return;
        }
        case cir::TypeKind::Record: {
            const auto* record = std::get_if<cir::RecordTypePayload>(&payload);
            if (!record) {
                out += '?';
                return;
            }
            encode_record(file, resolved, *record, expand_structs, out);
            return;
        }
        case cir::TypeKind::Complex: {
            const auto* complex_payload =
                std::get_if<cir::ComplexTypePayload>(&payload);
            out += 'j';
            if (complex_payload) {
                encode_impl(file, complex_payload->element_type, expand_structs,
                            in_field, out);
            } else {
                out += '?';
            }
            return;
        }
        default:
            out += '?';
            return;
    }
}

std::string index_suffixed(std::string_view stem, uint32_t index) {
    std::string out(stem);
    out += '.';
    out += std::to_string(index);
    return out;
}

bool is_long_double_builtin(const cir::File& file, cir::TypeId resolved) {
    const cir::BuiltinTypePayload* builtin = builtin_payload(file, resolved);
    return builtin && builtin->kind == cir::BuiltinTypeKind::LongDouble;
}

} // namespace

const ClassLayout& class_layout() {
    static const ClassLayout layout;
    return layout;
}

const ClassRoLayout& class_ro_layout() {
    static const ClassRoLayout layout;
    return layout;
}

const MethodLayout& method_layout() {
    static const MethodLayout layout;
    return layout;
}

const IvarLayout& ivar_layout() {
    static const IvarLayout layout;
    return layout;
}

const CfStringLayout& cfstring_layout() {
    static const CfStringLayout layout;
    return layout;
}

std::string class_symbol(std::string_view class_name) {
    std::string out = "OBJC_CLASS_$_";
    out += class_name;
    return out;
}

std::string metaclass_symbol(std::string_view class_name) {
    std::string out = "OBJC_METACLASS_$_";
    out += class_name;
    return out;
}

std::string class_ro_symbol(std::string_view class_name, bool metaclass) {
    std::string out = metaclass ? "_OBJC_METACLASS_RO_$_" : "_OBJC_CLASS_RO_$_";
    out += class_name;
    return out;
}

std::string ivar_offset_symbol(std::string_view class_name,
                               std::string_view ivar_name) {
    std::string out = "OBJC_IVAR_$_";
    out += class_name;
    out += '.';
    out += ivar_name;
    return out;
}

std::string instance_method_list_symbol(std::string_view class_name) {
    std::string out = "_OBJC_$_INSTANCE_METHODS_";
    out += class_name;
    return out;
}

std::string class_method_list_symbol(std::string_view class_name) {
    std::string out = "_OBJC_$_CLASS_METHODS_";
    out += class_name;
    return out;
}

std::string ivar_list_symbol(std::string_view class_name) {
    std::string out = "_OBJC_$_INSTANCE_VARIABLES_";
    out += class_name;
    return out;
}

std::string class_name_literal_symbol(uint32_t index) {
    return index_suffixed("OBJC_CLASS_NAME_", index);
}

std::string meth_var_name_symbol(uint32_t index) {
    return index_suffixed("OBJC_METH_VAR_NAME_", index);
}

std::string meth_var_type_symbol(uint32_t index) {
    return index_suffixed("OBJC_METH_VAR_TYPE_", index);
}

std::string selector_ref_symbol(uint32_t index) {
    return index_suffixed("OBJC_SELECTOR_REFERENCES_", index);
}

std::string classlist_ref_symbol(uint32_t index) {
    return index_suffixed("OBJC_CLASSLIST_REFERENCES_$_", index);
}

std::string superclass_ref_symbol(uint32_t index) {
    return index_suffixed("OBJC_CLASSLIST_SUP_REFS_$_", index);
}

std::string cfstring_symbol(uint32_t index) {
    return index_suffixed("_unnamed_cfstring_", index);
}

std::string cstring_literal_symbol(uint32_t index) {
    return index_suffixed(".str", index);
}

std::string label_class_list_symbol() {
    return "_OBJC_LABEL_CLASS_$";
}

std::string image_info_symbol() {
    return "OBJC_IMAGE_INFO";
}

std::string method_body_asm_label(std::string_view class_name,
                                  std::string_view selector,
                                  bool is_class_method,
                                  std::string_view category) {
    std::string out;
    out += is_class_method ? '+' : '-';
    out += '[';
    out += class_name;
    if (!category.empty()) {
        out += '(';
        out += category;
        out += ')';
    }
    out += ' ';
    out += selector;
    out += ']';
    return out;
}

std::string_view methname_section() {
    return "__TEXT,__objc_methname,cstring_literals";
}

std::string_view classname_section() {
    return "__TEXT,__objc_classname,cstring_literals";
}

std::string_view methtype_section() {
    return "__TEXT,__objc_methtype,cstring_literals";
}

std::string_view selrefs_section() {
    return "__DATA,__objc_selrefs,literal_pointers,no_dead_strip";
}

std::string_view classrefs_section() {
    return "__DATA,__objc_classrefs,regular,no_dead_strip";
}

std::string_view superrefs_section() {
    return "__DATA,__objc_superrefs,regular,no_dead_strip";
}

std::string_view classlist_section() {
    return "__DATA,__objc_classlist,regular,no_dead_strip";
}

std::string_view nlclslist_section() {
    return "__DATA,__objc_nlclslist,regular,no_dead_strip";
}

std::string_view objc_const_section() {
    return "__DATA,__objc_const";
}

std::string_view objc_data_section() {
    return "__DATA,__objc_data";
}

std::string_view objc_ivar_section() {
    return "__DATA,__objc_ivar";
}

std::string_view imageinfo_section() {
    return "__DATA,__objc_imageinfo,regular,no_dead_strip";
}

std::string_view cfstring_section() {
    return "__DATA,__cfstring";
}

std::string_view cstring_section() {
    return "__TEXT,__cstring,cstring_literals";
}

std::string encode_type(const cir::File& file,
                        cir::TypeRef type,
                        const EncodeOptions& options) {
    std::string out;
    encode_impl(file, type, options.expand_structs, /*in_field=*/false, out);
    return out;
}

std::string encode_method(const cir::File& file, cir::TypeId function_type) {
    cir::TypeId resolved = strip_sugar(file, function_type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Function) {
        return {};
    }
    const auto* payload =
        std::get_if<cir::FunctionTypePayload>(&file.type_payload(resolved));
    if (!payload) {
        return {};
    }

    std::vector<uint64_t> slot_sizes;
    slot_sizes.reserve(payload->parameters.size());
    uint64_t total_bytes = 16;
    for (const cir::TypeRef& parameter : payload->parameters) {
        uint64_t size = 8;
        if (auto size_align = cir::size_align_of_type(file, parameter.type)) {
            size = size_align->size_bytes;
        }
        uint64_t slot = std::max<uint64_t>(size, 8);
        slot = (slot + 7) & ~static_cast<uint64_t>(7);
        slot_sizes.push_back(slot);
        total_bytes += slot;
    }

    const EncodeOptions options;
    std::string out = encode_type(file, payload->return_type, options);
    out += std::to_string(total_bytes);
    out += "@0:8";
    uint64_t offset = 16;
    for (size_t i = 0; i < payload->parameters.size(); ++i) {
        out += encode_type(file, payload->parameters[i], options);
        out += std::to_string(offset);
        offset += slot_sizes[i];
    }
    return out;
}

const char* msgsend_function_name(MsgSendVariant variant) {
    switch (variant) {
        case MsgSendVariant::Standard: return "objc_msgSend";
        case MsgSendVariant::Stret: return "objc_msgSend_stret";
        case MsgSendVariant::Fpret: return "objc_msgSend_fpret";
        case MsgSendVariant::Fp2ret: return "objc_msgSend_fp2ret";
        case MsgSendVariant::Super2: return "objc_msgSendSuper2";
        case MsgSendVariant::Super2Stret: return "objc_msgSendSuper2_stret";
    }
    return "objc_msgSend";
}

MsgSendVariant select_msgsend_variant(const cir::File& file,
                                      cir::TypeId return_type,
                                      const TargetInfo& target,
                                      bool is_super) {

    if (target.arch != TargetArch::X86_64) {
        return is_super ? MsgSendVariant::Super2 : MsgSendVariant::Standard;
    }

    if (!is_super) {

        cir::TypeId resolved = strip_sugar(file, return_type);
        if (is_long_double_builtin(file, resolved)) {
            return MsgSendVariant::Fpret;
        }
        if (file.valid(resolved) &&
            file.type(resolved).kind == cir::TypeKind::Complex) {
            const auto* complex_payload = std::get_if<cir::ComplexTypePayload>(
                &file.type_payload(resolved));
            if (complex_payload &&
                is_long_double_builtin(
                    file,
                    strip_sugar(file, complex_payload->element_type.type))) {
                return MsgSendVariant::Fp2ret;
            }
        }
    }

    bool memory_returned = false;
    if (file.valid(return_type)) {
        cir::TypeRef return_ref;
        return_ref.type = return_type;
        abi::AggregateClass classified =
            abi::classify_argument_native(file, return_ref, &target);
        memory_returned = classified.pass == abi::AggregatePass::Indirect ||
                          classified.pass == abi::AggregatePass::MemoryByval;
    }
    if (is_super) {
        return memory_returned ? MsgSendVariant::Super2Stret
                               : MsgSendVariant::Super2;
    }
    return memory_returned ? MsgSendVariant::Stret : MsgSendVariant::Standard;
}

} // namespace aburi::objc_runtime
