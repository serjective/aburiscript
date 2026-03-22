#ifndef ABURI_DARWIN_BLOCKS_H
#define ABURI_DARWIN_BLOCKS_H

#include <cstdint>
#include <string>
#include <string_view>

struct LangOptions;
struct TargetInfo;
class QualType;

namespace darwin_blocks {

enum class ConcreteBlockStorageClass {
    Global,
    Stack,
};

enum BlockLiteralFlags : uint32_t {
    BLOCK_IS_NOESCAPE = 1u << 23,
    BLOCK_HAS_COPY_DISPOSE = 1u << 25,
    BLOCK_HAS_CTOR = 1u << 26,
    BLOCK_IS_GLOBAL = 1u << 28,
    BLOCK_HAS_SIGNATURE = 1u << 30,
};

enum BlockFieldFlags : uint32_t {
    BLOCK_FIELD_IS_OBJECT = 3u,
    BLOCK_FIELD_IS_BLOCK = 7u,
    BLOCK_FIELD_IS_BYREF = 8u,
    BLOCK_FIELD_IS_WEAK = 16u,
    BLOCK_BYREF_CALLER = 128u,
};

struct BlockLiteralHeaderLayout {
    uint32_t reserved_offset = 8;
    uint32_t flags_offset = 12;
    uint32_t invoke_offset = 16;
    uint32_t descriptor_offset = 24;
};

struct BlockDescriptorLayout {
    uint32_t reserved_offset = 0;
    uint32_t size_offset = 8;
    uint32_t copy_helper_offset = 16;
    uint32_t dispose_helper_offset = 24;
    uint32_t signature_offset_without_copy_dispose = 16;
    uint32_t layout_offset_without_copy_dispose = 24;
    uint32_t signature_offset_with_copy_dispose = 32;
    uint32_t layout_offset_with_copy_dispose = 40;
};

struct BlockByrefLayout {
    uint32_t isa_offset = 0;
    uint32_t forwarding_offset = 8;
    uint32_t flags_offset = 16;
    uint32_t size_offset = 20;
    uint32_t keep_helper_offset = 24;
    uint32_t destroy_helper_offset = 32;
    uint32_t payload_offset_without_helpers = 24;
    uint32_t payload_offset_with_helpers = 40;
};

bool target_supports_darwin_blocks(const TargetInfo& target);
bool blocks_default_enabled_for_target(const TargetInfo& target);
bool blocks_enabled_for_langopts(const LangOptions& lang_opts,
                                 const TargetInfo& target);

const BlockLiteralHeaderLayout& block_literal_header_layout();
const BlockDescriptorLayout& block_descriptor_layout();
const BlockByrefLayout& block_byref_layout();
uint32_t block_descriptor_signature_offset(bool has_copy_dispose_helpers);
uint32_t block_descriptor_layout_string_offset(bool has_copy_dispose_helpers);
uint32_t block_byref_header_size(bool has_copy_dispose_helpers);
uint32_t block_byref_payload_offset(bool has_copy_dispose_helpers);

std::string_view runtime_class_symbol(ConcreteBlockStorageClass storage);
std::string encode_block_invoke_signature(QualType invoke_type,
                                          const TargetInfo* target);

} // namespace darwin_blocks

#endif // ABURI_DARWIN_BLOCKS_H
