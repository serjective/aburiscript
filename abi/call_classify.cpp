#include "call_classify.h"

#include "../cir/layout.h"
#include "aarch64_call_classify.h"
#include "or1k_call_classify.h"
#include "x86_64_call_classify.h"

#include <algorithm>
#include <optional>

namespace aburi::abi {

namespace {

std::optional<AggregateClass> classify_non_trivial_class(
    const cir::File& file,
    cir::TypeRef type) {
    cir::TypeId resolved = file.resolved_type(type.type);
    const cir::RecordFacts* facts =
        file.valid(resolved) ? file.record_facts_for_type(resolved) : nullptr;
    if (!facts || facts->is_incomplete ||
        !facts->is_non_trivial_for_calls) {
        return std::nullopt;
    }
    AggregateClass result;
    result.pass = AggregatePass::Indirect;
    if (auto size_align = cir::size_align_of_type(file, resolved)) {
        result.byte_size = size_align->size_bytes;
        result.byte_align = static_cast<uint32_t>(
            std::max<size_t>(1, size_align->alignment_bytes));
    }
    return result;
}

AggregateClass classify_x86_32(const cir::File& file, cir::TypeRef type) {
    AggregateClass result;
    if (!file.valid(type.type)) {
        return result;
    }
    cir::TypeId resolved = file.resolved_type(type.type);
    if (!file.valid(resolved)) {
        return result;
    }
    bool is_complex = file.type(resolved).kind == cir::TypeKind::Complex;
    if (!is_complex && !is_complete_record_type(file, resolved)) {
        return result;
    }
    auto size_align = cir::size_align_of_type(file, resolved);
    if (!size_align) {
        return result;
    }
    if (is_empty_record_abi_ignored(file, resolved)) {
        result.pass = AggregatePass::Ignore;
        return result;
    }
    result.pass = AggregatePass::MemoryByval;
    result.byte_size = size_align->size_bytes;
    result.byte_align = static_cast<uint32_t>(
        std::max<size_t>(1, size_align->alignment_bytes));
    return result;
}

} // namespace

AggregateClass classify_argument_native(const cir::File& file,
                                        cir::TypeRef type,
                                        const TargetInfo* target) {
    if (std::optional<AggregateClass> non_trivial =
            classify_non_trivial_class(file, type)) {
        return *non_trivial;
    }
    if (target && target->arch == TargetArch::X86_64) {
        return classify_x86_64_argument_native(file, type, target);
    }
    if (target && target->arch == TargetArch::X86) {
        return classify_x86_32(file, type);
    }
    if (target && target->arch == TargetArch::OR1K) {
        return classify_or1k_argument_native(file, type, target);
    }
    return classify_aarch64_argument_native(file, type, target);
}

AggregateClass classify_vararg_native(const cir::File& file,
                                      cir::TypeRef type,
                                      const TargetInfo* target) {
    if (std::optional<AggregateClass> non_trivial =
            classify_non_trivial_class(file, type)) {
        return *non_trivial;
    }
    if (target && target->arch == TargetArch::X86_64) {
        return classify_x86_64_vararg_native(file, type, target);
    }
    if (target && target->arch == TargetArch::X86) {
        return classify_x86_32(file, type);
    }
    if (target && target->arch == TargetArch::OR1K) {
        return classify_or1k_vararg_native(file, type, target);
    }
    return classify_aarch64_vararg_native(file, type, target);
}

} // namespace aburi::abi
