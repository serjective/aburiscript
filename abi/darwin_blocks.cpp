#include "darwin_blocks.h"

#include <algorithm>
#include <cctype>
#include <string>

#include "../lang_options.h"
#include "target_info.h"

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
    static const BlockLiteralHeaderLayout layout;
    return layout;
}

const BlockDescriptorLayout& block_descriptor_layout() {
    static const BlockDescriptorLayout layout;
    return layout;
}

const BlockByrefLayout& block_byref_layout() {
    static const BlockByrefLayout layout;
    return layout;
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

} // namespace darwin_blocks
