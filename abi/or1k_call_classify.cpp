#include "or1k_call_classify.h"

#include "ilp32_classify_common.h"

namespace aburi::abi {

namespace {

AggregateClass classify_or1k(const cir::File& file, cir::TypeRef type) {
    if (!file.valid(type.type)) {
        return {};
    }
    cir::TypeId resolved = file.resolved_type(type.type);
    std::optional<Ilp32SizeAlign> size_align =
        aggregate_size_align(file, resolved);
    if (!size_align) {
        return {};
    }
    if (is_ignored_empty_record(file, resolved)) {
        AggregateClass ignored;
        ignored.pass = AggregatePass::Ignore;
        return ignored;
    }
    return pass_indirect(size_align->size_bytes, size_align->align_bytes);
}

} // namespace

AggregateClass classify_or1k_argument_native(const cir::File& file,
                                             cir::TypeRef type,
                                             const TargetInfo*) {
    return classify_or1k(file, type);
}

AggregateClass classify_or1k_vararg_native(const cir::File& file,
                                           cir::TypeRef type,
                                           const TargetInfo*) {
    return classify_or1k(file, type);
}

} // namespace aburi::abi
