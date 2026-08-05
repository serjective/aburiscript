#ifndef ABURI_CIR_IDS_H
#define ABURI_CIR_IDS_H

#include <cstdint>

namespace aburi::cir {

template <typename Tag>
struct Id {
    uint32_t index = 0;
    uint32_t generation = 0;

    bool valid() const {
        return index != 0;
    }

    friend bool operator==(Id lhs, Id rhs) {
        return lhs.index == rhs.index && lhs.generation == rhs.generation;
    }

    friend bool operator!=(Id lhs, Id rhs) {
        return !(lhs == rhs);
    }
};

struct NameTag;
struct TypeTag;
struct EntityTag;
struct DeclContextTag;
struct BindingTag;
struct PlaceFactTag;
struct SwitchTag;
struct InstTag;
struct BlockTag;
struct FunctionTag;
struct GenericTag;
struct SpecificTag;
struct InlineAsmPayloadTag;
struct ValueExprTag;
struct LifetimeTag;
struct ModuleAttachmentTag;
struct ConstantStateTag;
struct PlaceholderResultFactTag;
struct ClosureIdentityTag;
struct SelectorTag;

using NameId = Id<NameTag>;
using TypeId = Id<TypeTag>;
using EntityId = Id<EntityTag>;
using DeclContextId = Id<DeclContextTag>;
using BindingId = Id<BindingTag>;
using PlaceFactId = Id<PlaceFactTag>;
using SwitchId = Id<SwitchTag>;
using InstId = Id<InstTag>;
using BlockId = Id<BlockTag>;
using InstBlockId = BlockId;
using FunctionId = Id<FunctionTag>;
using GenericId = Id<GenericTag>;
using SpecificId = Id<SpecificTag>;
using InlineAsmPayloadId = Id<InlineAsmPayloadTag>;
using ValueExprId = Id<ValueExprTag>;
using LifetimeId = Id<LifetimeTag>;

using ModuleAttachmentId = Id<ModuleAttachmentTag>;

using ConstantStateId = Id<ConstantStateTag>;

using ClosureIdentityId = Id<ClosureIdentityTag>;

using PlaceholderResultFactId = Id<PlaceholderResultFactTag>;

using SelectorId = Id<SelectorTag>;

template <typename IdT>
constexpr IdT invalid_id() {
    return {};
}

} // namespace aburi::cir

#endif // ABURI_CIR_IDS_H
