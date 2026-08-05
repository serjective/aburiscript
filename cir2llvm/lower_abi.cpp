#include "lowerer.h"

#include <algorithm>
#include <cstdint>
#include <variant>

#include <llvm/IR/Attributes.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Instructions.h>

#include "../abi/aarch64_call_classify.h"
#include "../cir/layout.h"

namespace aburi::cir2llvm {

Lowerer::FunctionAbiInfo Lowerer::classify_function_abi(cir::TypeId function_type) {
    FunctionAbiInfo abi;
    abi.source_function_type = function_type;
    if (!file_.valid(function_type)) {
        return abi;
    }
    function_type = file_.resolved_type(function_type);
    if (!file_.valid(function_type) ||
        file_.type(function_type).kind != cir::TypeKind::Function) {
        return abi;
    }

    const auto& payload =
        std::get<cir::FunctionTypePayload>(file_.type_payload(function_type));
    abi.return_type = payload.return_type;
    abi.is_variadic = payload.is_variadic;
    abi.has_prototype = payload.has_prototype;
    abi.result = classify_result_abi(payload.return_type);

    std::vector<llvm::Type*> llvm_params;
    if (abi.result.kind == AbiArgKind::Indirect) {
        llvm_params.push_back(abi.result.abi_type);
    }

    abi.params.reserve(payload.parameters.size());
    llvm_params.reserve(llvm_params.size() + payload.parameters.size());
    for (cir::TypeRef param : payload.parameters) {
        AbiArgInfo info = classify_param_abi(param);
        abi.params.push_back(info);
        if (info.is_ignored) {
            continue;
        }
        llvm_params.push_back(info.abi_type ? info.abi_type : llvm_type(param));
    }

    llvm::Type* return_type = abi.result.kind == AbiArgKind::Indirect
        ? llvm::Type::getVoidTy(context())
        : (abi.result.abi_type ? abi.result.abi_type : llvm_type(payload.return_type));
    abi.llvm_type = llvm::FunctionType::get(return_type,
                                            llvm_params,
                                            payload.is_variadic);
    return abi;
}

llvm::Type* Lowerer::direct_aggregate_llvm_type(const abi::AggregateClass& cls,
                                                cir::TypeRef source_type) {
    if (cls.pass == abi::AggregatePass::CoerceHfa) {
        llvm::Type* element_type = llvm_builtin_type(cls.hfa_element);
        if (!element_type) {
            return nullptr;
        }
        return llvm::ArrayType::get(element_type, cls.hfa_count);
    }
    if (cls.pass == abi::AggregatePass::CoerceIntSlots) {
        if (cls.int_slot_count == 1) {
            return llvm::Type::getInt64Ty(context());
        }
        return llvm::ArrayType::get(llvm::Type::getInt64Ty(context()),
                                    cls.int_slot_count);
    }
    (void)source_type;
    return nullptr;
}

Lowerer::AbiArgInfo Lowerer::classify_result_abi(cir::TypeRef type) {
    AbiArgInfo info;
    info.source_type = type;
    info.abi_type = llvm_type(type);
    info.is_aggregate = abi::is_complete_record_type(file_, type.type);

    abi::AggregateClass cls =
        abi::classify_aarch64_argument(file_, type, options_.target.get());

    const cir::RecordFacts* record_facts =
        file_.record_facts_for_type(file_.resolved_type(type.type));
    if (record_facts && record_facts->is_non_trivial_for_calls) {
        info.kind = AbiArgKind::Indirect;
        info.abi_type = llvm::PointerType::get(context(), 0);
        info.is_sret = true;
        return info;
    }

    switch (cls.pass) {
        case abi::AggregatePass::UseSourceType:
        case abi::AggregatePass::CoerceClassedSlots:
        case abi::AggregatePass::MemoryByval:
            return info;
        case abi::AggregatePass::Ignore:
            info.abi_type = llvm::Type::getVoidTy(context());
            info.is_ignored = true;
            return info;
        case abi::AggregatePass::CoerceHfa:
        case abi::AggregatePass::CoerceIntSlots:
            if (llvm::Type* direct_type = direct_aggregate_llvm_type(cls, type)) {
                info.abi_type = direct_type;
                info.is_direct_aggregate = info.abi_type != llvm_type(type);
                return info;
            }

            if (cls.byte_size > 16) {
                break;
            }
            return info;
        case abi::AggregatePass::Indirect:
            break;
    }
    info.kind = AbiArgKind::Indirect;
    info.abi_type = llvm::PointerType::get(context(), 0);
    info.is_sret = true;
    return info;
}

Lowerer::AbiArgInfo Lowerer::classify_param_abi(cir::TypeRef type) {
    AbiArgInfo info;
    info.source_type = type;
    info.abi_type = llvm_type(type);
    info.is_aggregate = abi::is_complete_record_type(file_, type.type);

    abi::AggregateClass cls =
        abi::classify_aarch64_argument(file_, type, options_.target.get());

    const cir::RecordFacts* record_facts =
        file_.record_facts_for_type(file_.resolved_type(type.type));
    if (record_facts && record_facts->is_non_trivial_for_calls) {
        info.kind = AbiArgKind::Indirect;
        info.abi_type = llvm::PointerType::get(context(), 0);
        return info;
    }

    switch (cls.pass) {
        case abi::AggregatePass::UseSourceType:
        case abi::AggregatePass::CoerceClassedSlots:
        case abi::AggregatePass::MemoryByval:
            return info;
        case abi::AggregatePass::Ignore:
            info.abi_type = nullptr;
            info.is_ignored = true;
            return info;
        case abi::AggregatePass::CoerceHfa:
        case abi::AggregatePass::CoerceIntSlots:
            if (llvm::Type* direct_type = direct_aggregate_llvm_type(cls, type)) {
                info.abi_type = direct_type;
                info.is_direct_aggregate = info.abi_type != llvm_type(type);
                return info;
            }
            if (cls.byte_size > 16) {
                break;
            }
            return info;
        case abi::AggregatePass::Indirect:
            break;
    }

    info.kind = AbiArgKind::Indirect;
    info.abi_type = llvm::PointerType::get(context(), 0);
    return info;
}

Lowerer::AbiArgInfo Lowerer::classify_vararg_abi(cir::TypeRef type) {
    AbiArgInfo info;
    info.source_type = type;
    info.abi_type = llvm_type(type);
    info.is_aggregate = abi::is_complete_record_type(file_, type.type);

    abi::AggregateClass cls =
        abi::classify_aarch64_vararg(file_, type, options_.target.get());
    switch (cls.pass) {
        case abi::AggregatePass::UseSourceType:
        case abi::AggregatePass::CoerceClassedSlots:
        case abi::AggregatePass::MemoryByval:
        case abi::AggregatePass::Ignore:
            return info;
        case abi::AggregatePass::Indirect:
            info.kind = AbiArgKind::Indirect;
            info.abi_type = llvm::PointerType::get(context(), 0);
            return info;
        case abi::AggregatePass::CoerceHfa:

        case abi::AggregatePass::CoerceIntSlots:
            if (llvm::Type* direct_type = direct_aggregate_llvm_type(cls, type)) {
                info.abi_type = direct_type;
                info.is_direct_aggregate = info.abi_type != llvm_type(type);
            }
            return info;
    }
    return info;
}

llvm::Value* Lowerer::materialize_abi_value_to_source(llvm::Value* abi_value,
                                                      cir::TypeRef source_type,
                                                      SrcLoc loc,
                                                      llvm::StringRef name) {
    if (!abi_value) {
        return nullptr;
    }
    llvm::Type* source_llvm_type = llvm_type(source_type);
    if (abi_value->getType() == source_llvm_type) {
        return abi_value;
    }

    auto size_align = cir::size_align_of_type(file_, source_type.type);
    if (!size_align) {
        error("cannot materialize ABI aggregate with incomplete source type", loc);
        return nullptr;
    }

    llvm::AllocaInst* abi_tmp = create_entry_alloca(abi_value->getType(), "abi.value.tmp");
    llvm::AllocaInst* source_tmp = create_entry_alloca(source_llvm_type, name);
    abi_tmp->setAlignment(module().getDataLayout().getABITypeAlign(abi_value->getType()));
    source_tmp->setAlignment(llvm::Align(std::max<size_t>(1, size_align->alignment_bytes)));
    builder().CreateStore(abi_value, abi_tmp);
    builder().CreateMemCpy(source_tmp,
                           llvm::MaybeAlign(size_align->alignment_bytes),
                           abi_tmp,
                           llvm::MaybeAlign(abi_tmp->getAlign()),
                           static_cast<uint64_t>(size_align->size_bytes));
    auto* load = builder().CreateLoad(source_llvm_type, source_tmp, name);
    load->setAlignment(llvm::Align(std::max<size_t>(1, size_align->alignment_bytes)));
    return load;
}

llvm::Value* Lowerer::materialize_indirect_abi_value_to_source(llvm::Value* pointer,
                                                               cir::TypeRef source_type,
                                                               SrcLoc loc,
                                                               llvm::StringRef name) {
    if (!pointer) {
        return nullptr;
    }
    auto size_align = cir::size_align_of_type(file_, source_type.type);
    if (!size_align) {
        error("cannot materialize indirect ABI aggregate with incomplete source type", loc);
        return nullptr;
    }
    llvm::Type* source_llvm_type = llvm_type(source_type);
    auto* load = builder().CreateLoad(source_llvm_type, pointer, name);
    load->setAlignment(llvm::Align(std::max<size_t>(1, size_align->alignment_bytes)));
    return load;
}

llvm::Value* Lowerer::materialize_source_value_to_abi(llvm::Value* source_value,
                                                     cir::TypeRef source_type,
                                                     llvm::Type* abi_type,
                                                     SrcLoc loc,
                                                     llvm::StringRef name) {
    if (!source_value || !abi_type) {
        return nullptr;
    }
    if (source_value->getType() == abi_type) {
        return source_value;
    }

    auto size_align = cir::size_align_of_type(file_, source_type.type);
    if (!size_align) {
        error("cannot coerce source aggregate with incomplete type", loc);
        return nullptr;
    }
    llvm::Type* source_llvm_type = llvm_type(source_type);
    llvm::AllocaInst* source_tmp = create_entry_alloca(source_llvm_type, "abi.source.tmp");
    llvm::AllocaInst* abi_tmp = create_entry_alloca(abi_type, name);
    source_tmp->setAlignment(llvm::Align(std::max<size_t>(1, size_align->alignment_bytes)));
    abi_tmp->setAlignment(module().getDataLayout().getABITypeAlign(abi_type));
    builder().CreateStore(source_value, source_tmp);
    builder().CreateStore(llvm::Constant::getNullValue(abi_type), abi_tmp);
    builder().CreateMemCpy(abi_tmp,
                           llvm::MaybeAlign(abi_tmp->getAlign()),
                           source_tmp,
                           llvm::MaybeAlign(size_align->alignment_bytes),
                           static_cast<uint64_t>(size_align->size_bytes));
    auto* load = builder().CreateLoad(abi_type, abi_tmp, name);
    load->setAlignment(abi_tmp->getAlign());
    return load;
}

llvm::Value* Lowerer::materialize_source_value_to_indirect_abi(
    llvm::Value* source_value,
    cir::TypeRef source_type,
    SrcLoc loc,
    llvm::StringRef name) {
    if (!source_value) {
        return nullptr;
    }
    auto size_align = cir::size_align_of_type(file_, source_type.type);
    if (!size_align) {
        error("cannot materialize indirect ABI argument with incomplete source type", loc);
        return nullptr;
    }
    llvm::Type* source_llvm_type = llvm_type(source_type);
    llvm::AllocaInst* tmp = create_entry_alloca(source_llvm_type, name);
    llvm::Align alignment(std::max<size_t>(1, size_align->alignment_bytes));
    tmp->setAlignment(alignment);

    if (auto* load = llvm::dyn_cast<llvm::LoadInst>(source_value)) {

        bool found_load = false;
        bool clobbered = false;
        llvm::BasicBlock* block = builder().GetInsertBlock();
        llvm::BasicBlock::iterator cursor = builder().GetInsertPoint();
        for (int steps = 0; steps < 128; ++steps) {
            if (cursor == block->begin()) {
                llvm::BasicBlock* predecessor = block->getSinglePredecessor();
                if (!predecessor) {
                    break;
                }
                block = predecessor;
                cursor = block->end();
                continue;
            }
            --cursor;
            if (&*cursor == load) {
                found_load = true;
                break;
            }
            if (cursor->mayWriteToMemory()) {
                clobbered = true;
                break;
            }
        }
        if (found_load && !clobbered) {
            builder().CreateMemCpy(tmp,
                                   alignment,
                                   load->getPointerOperand(),
                                   load->getAlign(),
                                   size_align->size_bytes);
            return tmp;
        }
    }
    builder().CreateStore(source_value, tmp);
    return tmp;
}

void Lowerer::apply_function_abi_attributes(llvm::Function* function,
                                            const FunctionAbiInfo& abi) {
    if (!function) {
        return;
    }
    unsigned index = 0;
    if (abi.result.kind == AbiArgKind::Indirect && abi.result.is_sret) {
        llvm::Type* source_type = llvm_type(abi.result.source_type);
        function->addParamAttr(index,
                               llvm::Attribute::getWithStructRetType(context(),
                                                                      source_type));
        if (auto size_align = cir::size_align_of_type(file_, abi.result.source_type.type)) {
            function->addParamAttr(index,
                                   llvm::Attribute::getWithAlignment(
                                       context(),
                                       llvm::Align(std::max<size_t>(1, size_align->alignment_bytes))));
        }
        ++index;
    }
    for (const AbiArgInfo& param : abi.params) {
        if (param.is_ignored) {
            continue;
        }
        if (param.kind == AbiArgKind::Indirect && param.is_byval) {
            function->addParamAttr(index,
                                   llvm::Attribute::getWithByValType(
                                       context(),
                                       llvm_type(param.source_type)));
            if (auto size_align = cir::size_align_of_type(file_, param.source_type.type)) {
                function->addParamAttr(index,
                                       llvm::Attribute::getWithAlignment(
                                           context(),
                                           llvm::Align(std::max<size_t>(1, size_align->alignment_bytes))));
            }
        }
        ++index;
    }
}

void Lowerer::apply_call_abi_attributes(llvm::CallBase* call,
                                        const FunctionAbiInfo& abi) {
    if (!call) {
        return;
    }
    unsigned index = 0;
    if (abi.result.kind == AbiArgKind::Indirect && abi.result.is_sret) {
        llvm::Type* source_type = llvm_type(abi.result.source_type);
        call->addParamAttr(index,
                           llvm::Attribute::getWithStructRetType(context(),
                                                                  source_type));
        if (auto size_align = cir::size_align_of_type(file_, abi.result.source_type.type)) {
            call->addParamAttr(index,
                               llvm::Attribute::getWithAlignment(
                                   context(),
                                   llvm::Align(std::max<size_t>(1, size_align->alignment_bytes))));
        }
        ++index;
    }
    for (const AbiArgInfo& param : abi.params) {
        if (param.is_ignored) {
            continue;
        }
        if (param.kind == AbiArgKind::Indirect && param.is_byval) {
            call->addParamAttr(index,
                               llvm::Attribute::getWithByValType(
                                   context(),
                                   llvm_type(param.source_type)));
            if (auto size_align = cir::size_align_of_type(file_, param.source_type.type)) {
                call->addParamAttr(index,
                                   llvm::Attribute::getWithAlignment(
                                       context(),
                                       llvm::Align(std::max<size_t>(1, size_align->alignment_bytes))));
            }
        }
        ++index;
    }
}

} // namespace aburi::cir2llvm
