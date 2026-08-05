#ifndef ABURI_OBJC_RUNTIME_H
#define ABURI_OBJC_RUNTIME_H

#include <cstdint>
#include <string>
#include <string_view>

#include "../cir/type.h"

struct TargetInfo;

namespace aburi::cir {
class File;
} // namespace aburi::cir

namespace aburi::objc_runtime {

struct ClassLayout {
    uint32_t isa_offset = 0;
    uint32_t superclass_offset = 8;
    uint32_t cache_offset = 16;
    uint32_t vtable_offset = 24;
    uint32_t ro_offset = 32;
    uint32_t size = 40;
};

struct ClassRoLayout {
    uint32_t flags_offset = 0;
    uint32_t instance_start_offset = 4;
    uint32_t instance_size_offset = 8;
    uint32_t reserved_offset = 12;
    uint32_t ivar_layout_offset = 16;
    uint32_t name_offset = 24;
    uint32_t base_methods_offset = 32;
    uint32_t base_protocols_offset = 40;
    uint32_t ivars_offset = 48;
    uint32_t weak_ivar_layout_offset = 56;
    uint32_t base_properties_offset = 64;
    uint32_t size = 72;
};

struct MethodLayout {
    uint32_t name_offset = 0;
    uint32_t types_offset = 8;
    uint32_t imp_offset = 16;
    uint32_t size = 24;
    uint32_t list_entsize = 24;
    uint32_t list_entsize_offset = 0;
    uint32_t list_count_offset = 4;
    uint32_t list_header_size = 8;
};

struct IvarLayout {
    uint32_t offset_variable_offset = 0;
    uint32_t name_offset = 8;
    uint32_t type_offset = 16;
    uint32_t alignment_offset = 24;
    uint32_t size_field_offset = 28;
    uint32_t size = 32;
    uint32_t list_entsize = 32;
    uint32_t list_entsize_offset = 0;
    uint32_t list_count_offset = 4;
    uint32_t list_header_size = 8;
};

struct CfStringLayout {
    uint32_t isa_offset = 0;
    uint32_t flags_offset = 8;
    uint32_t string_offset = 16;
    uint32_t length_offset = 24;
    uint32_t size = 32;
    uint32_t flags_value = 0x7C8;
};

enum ClassRoFlags : uint32_t {
    RO_META = 0x1,
    RO_ROOT = 0x2,
    RO_HAS_CXX_STRUCTORS = 0x4,
    RO_HIDDEN = 0x10,
    RO_EXCEPTION = 0x20,
    RO_IS_ARC = 0x80,
    RO_HAS_CXX_DTOR_ONLY = 0x100,
};

inline constexpr uint32_t image_info_version = 0;
inline constexpr uint32_t image_info_flags = 64;

const ClassLayout& class_layout();
const ClassRoLayout& class_ro_layout();
const MethodLayout& method_layout();
const IvarLayout& ivar_layout();
const CfStringLayout& cfstring_layout();

std::string class_symbol(std::string_view class_name);
std::string metaclass_symbol(std::string_view class_name);
std::string class_ro_symbol(std::string_view class_name, bool metaclass);
std::string ivar_offset_symbol(std::string_view class_name,
                               std::string_view ivar_name);
std::string instance_method_list_symbol(std::string_view class_name);
std::string class_method_list_symbol(std::string_view class_name);
std::string ivar_list_symbol(std::string_view class_name);
std::string class_name_literal_symbol(uint32_t index);
std::string meth_var_name_symbol(uint32_t index);
std::string meth_var_type_symbol(uint32_t index);
std::string selector_ref_symbol(uint32_t index);
std::string classlist_ref_symbol(uint32_t index);
std::string superclass_ref_symbol(uint32_t index);
std::string cfstring_symbol(uint32_t index);
std::string cstring_literal_symbol(uint32_t index);
std::string label_class_list_symbol();
std::string image_info_symbol();

std::string method_body_asm_label(std::string_view class_name,
                                  std::string_view selector,
                                  bool is_class_method,
                                  std::string_view category = "");

std::string_view methname_section();
std::string_view classname_section();
std::string_view methtype_section();
std::string_view selrefs_section();
std::string_view classrefs_section();
std::string_view superrefs_section();
std::string_view classlist_section();
std::string_view nlclslist_section();
std::string_view objc_const_section();
std::string_view objc_data_section();
std::string_view objc_ivar_section();
std::string_view imageinfo_section();
std::string_view cfstring_section();
std::string_view cstring_section();

struct EncodeOptions {
    bool expand_structs = true;
};

std::string encode_type(const cir::File& file,
                        cir::TypeRef type,
                        const EncodeOptions& options);

std::string encode_method(const cir::File& file, cir::TypeId function_type);

enum class MsgSendVariant {
    Standard,
    Stret,
    Fpret,
    Fp2ret,
    Super2,
    Super2Stret,
};

const char* msgsend_function_name(MsgSendVariant variant);
MsgSendVariant select_msgsend_variant(const cir::File& file,
                                      cir::TypeId return_type,
                                      const TargetInfo& target,
                                      bool is_super);

} // namespace aburi::objc_runtime

#endif // ABURI_OBJC_RUNTIME_H
