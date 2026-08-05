#include "lowerer.h"

#include "../abi/mangle_cir.h"
#include "../cir/layout.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <variant>
#include <vector>

#include <llvm/ADT/APInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/TargetParser/Triple.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalObject.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

namespace aburi::cir2llvm {

namespace {

bool bytes_are_zero(const std::vector<uint8_t>& bytes) {
    return std::all_of(bytes.begin(), bytes.end(), [](uint8_t byte) {
        return byte == 0;
    });
}

llvm::Constant* integer_constant_from_bytes(llvm::IntegerType* type,
                                            const std::vector<uint8_t>& bytes) {
    unsigned bits = type->getBitWidth();
    std::vector<uint64_t> words(std::max<size_t>(1, (bits + 63) / 64), 0);
    for (size_t index = 0; index < bytes.size(); ++index) {
        size_t word_index = index / sizeof(uint64_t);
        if (word_index >= words.size()) {
            break;
        }
        words[word_index] |= static_cast<uint64_t>(bytes[index]) << ((index % sizeof(uint64_t)) * 8);
    }
    llvm::APInt value(bits, llvm::ArrayRef<uint64_t>(words));
    return llvm::ConstantInt::get(type, value);
}

void apply_global_visibility(llvm::GlobalValue& value, const std::string& visibility) {

    if (value.hasLocalLinkage()) {
        return;
    }
    if (visibility == "hidden") {
        value.setVisibility(llvm::GlobalValue::HiddenVisibility);
    } else if (visibility == "protected") {
        value.setVisibility(llvm::GlobalValue::ProtectedVisibility);
    } else if (visibility == "default") {
        value.setVisibility(llvm::GlobalValue::DefaultVisibility);
    }

    if (value.getVisibility() != llvm::GlobalValue::DefaultVisibility) {
        value.setDSOLocal(true);
    }
}

cir::LinkageKind resolved_linkage(const cir::Entity& entity) {
    return entity.symbol_policy.finalized
        ? entity.symbol_policy.emission
        : entity.linkage;
}

void apply_symbol_policy(llvm::Module& module,
                         llvm::GlobalValue& value,
                         const cir::Entity& entity,
                         const cir::File& file,
                         bool emits_definition) {
    if (!entity.symbol_policy.finalized) {
        if (!entity.attr_facts.visibility.empty()) {
            apply_global_visibility(value, entity.attr_facts.visibility);
        }
        return;
    }
    switch (entity.symbol_policy.visibility) {
        case cir::SymbolVisibilityKind::Default:
            value.setVisibility(llvm::GlobalValue::DefaultVisibility);
            break;
        case cir::SymbolVisibilityKind::Hidden:
            value.setVisibility(llvm::GlobalValue::HiddenVisibility);
            break;
        case cir::SymbolVisibilityKind::Protected:
            value.setVisibility(llvm::GlobalValue::ProtectedVisibility);
            break;
    }
    if (entity.symbol_policy.comdat_key.valid() && emits_definition &&
        !module.getTargetTriple().isOSBinFormatMachO()) {
        if (auto* object = llvm::dyn_cast<llvm::GlobalObject>(&value)) {
            object->setComdat(module.getOrInsertComdat(
                std::string(file.name(entity.symbol_policy.comdat_key))));
        }
    }
}

} // namespace

bool Lowerer::definition_required(const cir::Entity& entity) const {
    return !entity.symbol_policy.finalized ||
           entity.symbol_policy.definition_emission ==
               cir::DefinitionEmissionKind::Required;
}

void Lowerer::declare_entities() {

    for (cir::EntityId entity_id : file_.entity_ids()) {
        const cir::Entity& entity = file_.entity(entity_id);
        if (entity.is_deleted ||
            entity.is_template_pattern ||
            entity.result_type_only_definition) {
            continue;
        }
        if (entity.suppressed_by_explicit_instantiation_declaration ||
            entity.suppressed_as_unselected_template_candidate) {
            continue;
        }
        if (!definition_required(entity)) {
            continue;
        }

        if (!entity.attr_facts.ifunc_target.empty() &&
            entity.kind == cir::EntityKind::Function) {
            (void)function_symbol(entity_id);
            continue;
        }
        if (!entity.is_definition) {

            if (!entity.attr_facts.weakref_target.empty() &&
                entity.attr_facts.is_weak) {
                if (entity.kind == cir::EntityKind::Function) {
                    (void)function_symbol(entity_id);
                } else if (entity.kind == cir::EntityKind::Variable) {
                    (void)get_or_create_global(entity_id);
                }
            }

            if (!entity.attr_facts.alias_target.empty()) {
                if (entity.kind == cir::EntityKind::Function) {
                    (void)function_symbol(entity_id);
                } else if (entity.kind == cir::EntityKind::Variable) {
                    (void)get_or_create_global(entity_id);
                }
            }
            continue;
        }
        if (entity.kind == cir::EntityKind::Function) {
            (void)get_or_declare_function(entity_id);
        } else if (entity.kind == cir::EntityKind::Variable &&
                   (entity.storage_duration == cir::StorageDuration::Static ||
                    entity.storage_duration == cir::StorageDuration::Thread)) {
            (void)get_or_create_global(entity_id);
        }
    }
}

llvm::GlobalValue* Lowerer::resolve_weakref_target(const std::string& target_name,
                                                   cir::EntityId self,
                                                   SrcLoc loc) {

    llvm::GlobalValue* target = module().getNamedValue(target_name);
    if (!target) {
        for (cir::EntityId candidate : file_.entity_ids()) {
            const cir::Entity& other = file_.entity(candidate);
            if (candidate != self && other.name.valid() &&
                file_.name(other.name) == target_name && other.is_definition) {
                target = other.kind == cir::EntityKind::Function
                    ? static_cast<llvm::GlobalValue*>(get_or_declare_function(candidate))
                    : static_cast<llvm::GlobalValue*>(get_or_create_global(candidate));
                break;
            }
        }
    }
    if (!target) {
        error("weakref target '" + target_name + "' is not defined in this translation unit",
              loc);
    }
    return target;
}

llvm::GlobalValue* Lowerer::function_symbol(cir::EntityId entity_id) {
    auto found = entity_values_.find(id_key(entity_id));
    if (found != entity_values_.end()) {
        return llvm::dyn_cast<llvm::GlobalValue>(found->second);
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (!entity.attr_facts.weakref_target.empty() && !entity.is_definition) {
        FunctionAbiInfo abi = classify_function_abi(entity.type);
        if (!abi.llvm_type) {
            error("cannot lower function type for " + file_.format_entity(entity_id),
                  entity.loc);
            return nullptr;
        }
        llvm::GlobalValue* target = resolve_weakref_target(
            entity.attr_facts.weakref_target, entity_id, entity.loc);
        if (!target) {
            return nullptr;
        }
        std::string name = linkage_name(entity_id);
        llvm::GlobalAlias* alias = llvm::GlobalAlias::create(
            abi.llvm_type, 0,
            entity.attr_facts.is_weak ? llvm::GlobalValue::WeakAnyLinkage
                                      : llvm::GlobalValue::InternalLinkage,
            name, target, &module());
        entity_values_[id_key(entity_id)] = alias;
        return alias;
    }

    if (!entity.attr_facts.alias_target.empty()) {
        FunctionAbiInfo abi = classify_function_abi(entity.type);
        if (!abi.llvm_type) {
            error("cannot lower function type for " + file_.format_entity(entity_id),
                  entity.loc);
            return nullptr;
        }
        llvm::GlobalValue* target = resolve_weakref_target(
            entity.attr_facts.alias_target, entity_id, entity.loc);
        if (!target) {
            return nullptr;
        }
        std::string name = linkage_name(entity_id);
        llvm::GlobalValue::LinkageTypes linkage =
            entity.linkage == cir::LinkageKind::Internal
                ? llvm::GlobalValue::InternalLinkage
            : entity.attr_facts.is_weak ? llvm::GlobalValue::WeakAnyLinkage
                                        : llvm::GlobalValue::ExternalLinkage;
        llvm::GlobalAlias* alias = llvm::GlobalAlias::create(
            abi.llvm_type, 0, linkage, name, target, &module());
        entity_values_[id_key(entity_id)] = alias;
        return alias;
    }

    if (!entity.attr_facts.ifunc_target.empty()) {
        FunctionAbiInfo abi = classify_function_abi(entity.type);
        if (!abi.llvm_type) {
            error("cannot lower function type for " + file_.format_entity(entity_id),
                  entity.loc);
            return nullptr;
        }
        llvm::GlobalValue* resolver = resolve_weakref_target(
            entity.attr_facts.ifunc_target, entity_id, entity.loc);
        if (!resolver) {
            return nullptr;
        }
        std::string name = linkage_name(entity_id);
        llvm::GlobalIFunc* ifunc = llvm::GlobalIFunc::create(
            abi.llvm_type, 0,
            entity.linkage == cir::LinkageKind::Internal
                ? llvm::GlobalValue::InternalLinkage
                : llvm::GlobalValue::ExternalLinkage,
            name, resolver, &module());
        if (!options_.pic) {
            ifunc->setDSOLocal(true);
        }
        entity_values_[id_key(entity_id)] = ifunc;
        return ifunc;
    }
    return get_or_declare_function(entity_id);
}

void Lowerer::emit_structor_aliases() {
    if (!options_.cxx_mangling) {
        return;
    }
    for (cir::FunctionId function_id : file_.function_ids()) {
        const cir::Function& function = file_.function(function_id);
        if (!function.entity.valid() || !file_.valid(function.entity)) {
            continue;
        }
        const cir::Entity& entity = file_.entity(function.entity);
        if (entity.is_deleted ||
            entity.is_extern_c || !entity.is_definition ||
            entity.is_template_pattern ||
            entity.decl_flags.is_consteval ||
            entity.result_type_only_definition ||
            entity.suppressed_by_explicit_instantiation_declaration ||
            entity.suppressed_as_unselected_template_candidate) {
            continue;
        }
        if (!definition_required(entity)) {
            continue;
        }
        const char* variant = nullptr;
        if (entity.kind == cir::EntityKind::Constructor) {
            variant = "C2";
        } else if (entity.kind == cir::EntityKind::Destructor) {
            variant = "D2";
        } else {
            continue;
        }

        const cir::RecordFacts* record = file_.record_facts(entity.parent);
        if (record && !record->virtual_bases.empty()) {
            continue;
        }
        std::string alias_name =
            abi::itanium_structor_variant_name(file_, function.entity, variant);
        if (alias_name.empty() || module().getNamedValue(alias_name)) {
            continue;
        }
        llvm::Function* definition =
            module().getFunction(linkage_name(function.entity));
        if (!definition) {
            continue;
        }
        llvm::GlobalAlias::create(definition->getValueType(),
                                  0,
                                  definition->getLinkage(),
                                  alias_name,
                                  definition,
                                  &module());
    }
}

std::string Lowerer::linkage_name(cir::EntityId entity_id) const {
    const cir::Entity& entity = file_.entity(entity_id);
    if (options_.cxx_mangling && !entity.is_extern_c) {
        if (entity.kind == cir::EntityKind::Constructor ||
            entity.kind == cir::EntityKind::Destructor) {

            const cir::RecordFacts* record = file_.record_facts(entity.parent);
            if (record && !record->virtual_bases.empty()) {
                std::string unified = abi::itanium_structor_variant_name(
                    file_, entity_id,
                    entity.kind == cir::EntityKind::Constructor ? "C4" : "D4");
                if (!unified.empty()) {
                    return unified;
                }
            }
        }
        std::string mangled = abi::itanium_linkage_name(file_, entity_id);
        if (!mangled.empty()) {
            return mangled;
        }
    }
    return entity.name.valid() ? std::string(file_.name(entity.name))
                               : file_.format_entity(entity_id);
}

llvm::Function* Lowerer::get_or_declare_function(cir::EntityId entity_id) {
    auto found = entity_values_.find(id_key(entity_id));
    if (found != entity_values_.end()) {
        return llvm::dyn_cast<llvm::Function>(found->second);
    }

    const cir::Entity& entity = file_.entity(entity_id);
    bool imported_declaration_only =
        entity.symbol_policy.imported_definition &&
        entity.symbol_policy.emission != cir::LinkageKind::LinkOnceODR;
    bool emits_definition = false;
    if (entity.is_definition && !entity.is_deleted &&
        !entity.decl_flags.is_consteval &&
        definition_required(entity) &&
        !imported_declaration_only &&
        !entity.result_type_only_definition &&
        !entity.suppressed_by_explicit_instantiation_declaration &&
        !entity.suppressed_as_unselected_template_candidate) {
        for (cir::FunctionId function_id : file_.function_ids()) {
            if (file_.function(function_id).entity == entity_id) {
                emits_definition = true;
                break;
            }
        }
    }
    cir::TypeId resolved_entity_type = file_.resolved_type(entity.type);
    const auto* source_function_type =
        file_.valid(resolved_entity_type) &&
                file_.type(resolved_entity_type).kind ==
                    cir::TypeKind::Function
            ? std::get_if<cir::FunctionTypePayload>(
                  &file_.type_payload(resolved_entity_type))
            : nullptr;
    if (source_function_type &&
        source_function_type->exception_spec.kind ==
            cir::FunctionExceptionSpecKind::Dependent) {
        error("cannot lower a function with an unresolved dependent "
              "exception specification",
              entity.loc);
        return nullptr;
    }
    FunctionAbiInfo abi = classify_function_abi(entity.type);
    llvm::FunctionType* function_type = abi.llvm_type;
    if (!function_type) {
        error("cannot lower function type for " + file_.format_entity(entity_id), entity.loc);
        return nullptr;
    }

    std::string name = linkage_name(entity_id);
    llvm::Function* function = module().getFunction(name);
    const bool function_already_existed = function != nullptr;
    if (!function) {
        function = llvm::Function::Create(function_type,
                                          llvm::GlobalValue::ExternalLinkage,
                                          name,
                                          module());
    } else if (function->getFunctionType() != function_type) {

        if (emits_definition && function->isDeclaration()) {
            llvm::Function* replacement =
                llvm::Function::Create(function_type,
                                       llvm::GlobalValue::ExternalLinkage,
                                       "",
                                       module());
            function->replaceAllUsesWith(replacement);
            for (auto& cached : entity_values_) {
                if (cached.second == function) {
                    cached.second = replacement;
                }
            }
            replacement->takeName(function);
            function->eraseFromParent();
            function = replacement;
        } else if (!emits_definition) {

        } else {
            error("conflicting function type for " + name, entity.loc);
            return nullptr;
        }
    }
    apply_function_abi_attributes(function, abi);
    // C functions cannot unwind through exceptions. A C++ function that can
    // unwind has this attribute removed later by apply_eh_function_setup;
    // Objective-C exceptions unwind through the C++ ABI, so the blanket
    // does not apply there either.
    if (!options_.cxx_mangling && !options_.objc) {
        function->addFnAttr(llvm::Attribute::NoUnwind);
    }

    if (options_.keep_frame_pointer) {
        function->addFnAttr("frame-pointer", "all");
    }

    if (options_.branch_target_enforcement) {
        function->addFnAttr("branch-target-enforcement");
    }
    if (options_.sign_return_address) {
        function->addFnAttr("sign-return-address", "non-leaf");
        function->addFnAttr("sign-return-address-key", "a_key");
    }

    if (!options_.pic) {
        function->setDSOLocal(true);
    }
    const cir::EntityAttributeFacts& attrs = entity.attr_facts;
    cir::LinkageKind linkage = resolved_linkage(entity);

    // A reference can name an earlier declaration entity after the matching
    // definition has already created the LLVM function. Applying the
    // declaration's default ExternalLinkage at that point would erase the
    // definition's internal, weak, linkonce, or available-externally policy.
    const bool declaration_would_downgrade =
        !emits_definition && function_already_existed;
    if (!declaration_would_downgrade) {
        function->setLinkage(
            !emits_definition
                ? llvm::GlobalValue::ExternalLinkage
            : linkage == cir::LinkageKind::Internal
                ? llvm::GlobalValue::InternalLinkage
            : entity.suppressed_by_explicit_instantiation_declaration
                ? llvm::GlobalValue::ExternalLinkage
            : linkage == cir::LinkageKind::LinkOnceODR
                ? llvm::GlobalValue::LinkOnceODRLinkage
                : llvm::GlobalValue::ExternalLinkage);
    }
    if (emits_definition && entity.inline_definition_only &&
        linkage != cir::LinkageKind::Internal) {

        function->setLinkage(llvm::GlobalValue::AvailableExternallyLinkage);
    }
    if (attrs.is_weak) {

        function->setLinkage(emits_definition
                                 ? llvm::GlobalValue::WeakAnyLinkage
                                 : llvm::GlobalValue::ExternalWeakLinkage);
    }
    if (!attrs.section.empty()) {
        function->setSection(attrs.section);
    }
    apply_symbol_policy(module(), *function, entity, file_, emits_definition);
    if (attrs.requested_alignment > 0) {
        function->setAlignment(llvm::Align(attrs.requested_alignment));
    }
    if (entity.decl_flags.is_inline) {
        function->addFnAttr(llvm::Attribute::InlineHint);
    }
    if (attrs.is_noreturn) {
        function->addFnAttr(llvm::Attribute::NoReturn);
    }
    if (attrs.is_noinline) {
        function->addFnAttr(llvm::Attribute::NoInline);
    } else if (attrs.is_always_inline) {
        function->addFnAttr(llvm::Attribute::AlwaysInline);
    }
    if (attrs.is_cold) {
        function->addFnAttr(llvm::Attribute::Cold);
    } else if (attrs.is_hot) {
        function->addFnAttr(llvm::Attribute::Hot);
    }
    if (attrs.is_nothrow) {
        function->addFnAttr(llvm::Attribute::NoUnwind);
    }
    if (const auto* fn_payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(entity.type)));
        fn_payload &&
        fn_payload->exception_spec.kind ==
            cir::FunctionExceptionSpecKind::NonThrowing) {

        function->addFnAttr(llvm::Attribute::NoUnwind);
    }
    auto passed_in_memory = [](const AbiArgInfo& arg) {
        return arg.kind == AbiArgKind::Indirect || arg.is_sret || arg.is_byval;
    };
    auto abi_touches_argument_memory = [&] {
        if (passed_in_memory(abi.result)) {
            return true;
        }
        return std::any_of(abi.params.begin(), abi.params.end(), passed_in_memory);
    };
    auto with_indirect_argument_memory = [&](llvm::MemoryEffects effects) {
        if (abi_touches_argument_memory()) {
            effects = effects.getWithModRef(llvm::IRMemLocation::ArgMem,
                                            llvm::ModRefInfo::ModRef);
        }
        return effects;
    };
    if (attrs.is_pure) {
        function->addFnAttr(llvm::Attribute::NoUnwind);
        function->setMemoryEffects(
            with_indirect_argument_memory(llvm::MemoryEffects::readOnly()));
    }
    if (attrs.is_const_function) {
        function->addFnAttr(llvm::Attribute::NoUnwind);
        function->setMemoryEffects(
            with_indirect_argument_memory(llvm::MemoryEffects::none()));
    }
    if (attrs.is_malloc) {
        function->addRetAttr(llvm::Attribute::NoAlias);
    }
    if (attrs.returns_nonnull) {
        function->addRetAttr(llvm::Attribute::NonNull);
    }
    if (attrs.nonnull_all_pointer_params) {
        const auto* payload =
            std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(entity.type)));
        if (payload) {
            for (unsigned i = 0; i < payload->parameters.size() && i < function->arg_size(); ++i) {
                cir::TypeId param_type = file_.resolved_type(payload->parameters[i].type);
                if (file_.valid(param_type) &&
                    file_.type(param_type).kind == cir::TypeKind::Pointer) {
                    function->addParamAttr(i, llvm::Attribute::NonNull);
                }
            }
        }
    }
    for (uint32_t one_based_index : attrs.nonnull_params) {
        if (one_based_index == 0) {
            continue;
        }
        unsigned index = one_based_index - 1;
        if (index < function->arg_size()) {
            function->addParamAttr(index, llvm::Attribute::NonNull);
        }
    }

    bool registers_here =
        entity.is_definition &&
        definition_required(entity) &&
        !(entity.symbol_policy.imported_definition &&
          entity.symbol_policy.emission != cir::LinkageKind::LinkOnceODR);
    if (attrs.constructor_priority >= 0 && registers_here) {
        llvm::appendToGlobalCtors(module(), function, attrs.constructor_priority);
    }
    if (attrs.destructor_priority >= 0 && registers_here) {
        llvm::appendToGlobalDtors(module(), function, attrs.destructor_priority);
    }
    if (attrs.is_used) {
        llvm::appendToCompilerUsed(module(), {function});
    }
    entity_values_[id_key(entity_id)] = function;
    return function;
}

llvm::GlobalValue* Lowerer::get_or_create_global(cir::EntityId entity_id) {
    auto found = entity_values_.find(id_key(entity_id));
    if (found != entity_values_.end()) {
        return llvm::dyn_cast<llvm::GlobalValue>(found->second);
    }

    const cir::Entity& entity = file_.entity(entity_id);
    llvm::Type* storage_type = llvm_type(entity.type);

    if (storage_type && storage_type->isVoidTy()) {
        storage_type = llvm::Type::getInt8Ty(context());
    }
    if (!storage_type || storage_type->isFunctionTy()) {
        error("cannot lower global storage type for " + file_.format_entity(entity_id),
              entity.loc);
        return nullptr;
    }

    std::string name = linkage_name(entity_id);
    if (!entity.attr_facts.asm_label.empty()) {

        name = "\x01" + entity.attr_facts.asm_label;
    }
    if (!entity.attr_facts.weakref_target.empty()) {

        llvm::GlobalValue* target = resolve_weakref_target(
            entity.attr_facts.weakref_target, entity_id, entity.loc);
        if (!target) {
            return nullptr;
        }
        llvm::GlobalAlias* alias = llvm::GlobalAlias::create(
            storage_type, 0,
            entity.attr_facts.is_weak ? llvm::GlobalValue::WeakAnyLinkage
                                      : llvm::GlobalValue::InternalLinkage,
            name, target, &module());
        entity_values_[id_key(entity_id)] = alias;
        return alias;
    }
    if (!entity.attr_facts.alias_target.empty()) {

        llvm::GlobalValue* target = resolve_weakref_target(
            entity.attr_facts.alias_target, entity_id, entity.loc);
        if (!target) {
            return nullptr;
        }
        llvm::GlobalValue::LinkageTypes linkage =
            entity.linkage == cir::LinkageKind::Internal
                ? llvm::GlobalValue::InternalLinkage
            : entity.attr_facts.is_weak ? llvm::GlobalValue::WeakAnyLinkage
                                        : llvm::GlobalValue::ExternalLinkage;
        llvm::GlobalAlias* alias = llvm::GlobalAlias::create(
            storage_type, 0, linkage, name, target, &module());
        entity_values_[id_key(entity_id)] = alias;
        return alias;
    }

    auto default_initializer = [&]() -> llvm::Constant* {
        cir::TypeId resolved = file_.resolved_type(entity.type);
        if (is_nullptr_type(resolved)) {
            return llvm_nullptr_carrier_value();
        }
        if (file_.valid(resolved) &&
            file_.type(resolved).kind == cir::TypeKind::MemberPointer &&
            !file_.member_pointer_points_to_function(resolved)) {
            if (auto* integer_type = llvm::dyn_cast<llvm::IntegerType>(storage_type)) {
                return llvm::ConstantInt::get(integer_type,
                                             static_cast<uint64_t>(-1),
                                             true);
            }
        }
        return llvm::Constant::getNullValue(storage_type);
    };

    bool emits_definition =
        entity.is_definition &&
        definition_required(entity) &&
        !entity.suppressed_by_explicit_instantiation_declaration &&
        !(entity.symbol_policy.imported_definition &&
          entity.symbol_policy.emission != cir::LinkageKind::LinkOnceODR);
    auto qualifiers_are_read_only = [](uint8_t qualifiers) {
        return (qualifiers & cir::QualConst) != 0 &&
            (qualifiers & cir::QualVolatile) == 0;
    };
    auto array_elements_are_read_only = [&](cir::TypeId type) {
        for (int depth = 0; depth < 64; ++depth) {
            cir::TypeId resolved_type = file_.resolved_type(type);
            if (!file_.valid(resolved_type) ||
                file_.type(resolved_type).kind != cir::TypeKind::Array) {
                return false;
            }
            cir::TypeRef element = file_.array_element_ref(resolved_type);
            if (qualifiers_are_read_only(element.qualifiers)) {
                return true;
            }
            type = element.type;
        }
        return false;
    };

    const bool declared_read_only =
        entity.attr_facts.section.empty() &&
        (qualifiers_are_read_only(entity.qualifiers) ||
         array_elements_are_read_only(entity.type));
    bool read_only_object =
        entity.object_origin ==
            cir::EntityObjectOrigin::TemplateParameterObject ||
        (emits_definition && entity.has_static_initializer &&
         declared_read_only &&
         !cir::type_has_mutable_subobject(file_, entity.type));
    llvm::Constant* initializer = emits_definition ? default_initializer() : nullptr;

    llvm::GlobalVariable* global = module().getNamedGlobal(name);
    cir::LinkageKind resolved = resolved_linkage(entity);
    llvm::GlobalValue::LinkageTypes linkage =
        !emits_definition
            ? llvm::GlobalValue::ExternalLinkage
        : resolved == cir::LinkageKind::Internal
            ? llvm::GlobalValue::InternalLinkage
            : resolved == cir::LinkageKind::LinkOnceODR
                  ? llvm::GlobalValue::LinkOnceODRLinkage
                  : llvm::GlobalValue::ExternalLinkage;
    if (!global) {
        global = new llvm::GlobalVariable(module(),
                                          storage_type,
                                          read_only_object,
                                          linkage,
                                          initializer,
                                          name);
    } else if (emits_definition) {
        global->setInitializer(initializer);
        global->setLinkage(linkage);
        global->setConstant(read_only_object);
    }

    entity_values_[id_key(entity_id)] = global;

    if (emits_definition && entity.has_static_initializer) {
        if (llvm::Constant* constant =
                constant_from_static_bytes(entity.type,
                                           entity.static_initializer_bytes,
                                           entity.loc,
                                           entity.static_initializer_relocations)) {
            if (constant->getType() != global->getValueType()) {

                llvm::GlobalVariable* replacement =
                    new llvm::GlobalVariable(module(),
                                             constant->getType(),
                                             global->isConstant(),
                                             global->getLinkage(),
                                             constant,
                                             "");
                global->replaceAllUsesWith(replacement);
                for (auto& cached : entity_values_) {
                    if (cached.second == global) {
                        cached.second = replacement;
                    }
                }
                replacement->takeName(global);
                global->eraseFromParent();
                global = replacement;
            } else {
                global->setInitializer(constant);
            }
        }
    }
    if (entity.storage_duration == cir::StorageDuration::Thread) {
        global->setThreadLocalMode(llvm::GlobalValue::GeneralDynamicTLSModel);
    }
    if (!options_.pic) {
        global->setDSOLocal(true);
    }
    const cir::EntityAttributeFacts& attrs = entity.attr_facts;
    if (attrs.is_weak) {
        global->setLinkage(emits_definition
                               ? llvm::GlobalValue::WeakAnyLinkage
                               : llvm::GlobalValue::ExternalWeakLinkage);
    }

    const bool fcommon_tentative =
        options_.fcommon && emits_definition &&
        !entity.declared_with_extern &&
        entity.linkage == cir::LinkageKind::External &&
        !entity.has_static_initializer &&
        !qualifiers_are_read_only(entity.qualifiers) &&
        !array_elements_are_read_only(entity.type) &&
        entity.attr_facts.section.empty() &&
        entity.storage_duration != cir::StorageDuration::Thread &&
        !attrs.is_weak && attrs.alias_target.empty() &&
        attrs.weakref_target.empty() && !attrs.is_named_register;
    if ((attrs.is_common || fcommon_tentative) && emits_definition) {
        global->setLinkage(llvm::GlobalValue::CommonLinkage);
        if (!global->hasInitializer()) {
            global->setInitializer(llvm::Constant::getNullValue(global->getValueType()));
        }
    }

    uint64_t alignment = attrs.requested_alignment;
    if (attrs.section.empty()) {
        if (std::optional<size_t> natural = cir::align_of_type(file_, entity.type)) {
            alignment = std::max<uint64_t>(alignment, *natural);
        }
    }
    if (alignment > 0) {
        global->setAlignment(llvm::Align(alignment));
    }
    if (!attrs.section.empty()) {
        global->setSection(attrs.section);
    }
    apply_symbol_policy(module(), *global, entity, file_, emits_definition);
    if (attrs.is_used) {
        llvm::appendToCompilerUsed(module(), {global});
    }
    entity_values_[id_key(entity_id)] = global;
    return global;
}

llvm::BlockAddress* Lowerer::block_address_constant(cir::EntityId entity_id,
                                                    cir::BlockId block,
                                                    SrcLoc loc) {
    llvm::Function* fn = get_or_declare_function(entity_id);
    if (!fn) {
        error("block-address relocation references a non-function", loc);
        return nullptr;
    }
    llvm::BasicBlock*& bb = label_address_blocks_[id_key(block)];
    if (!bb) {
        bb = llvm::BasicBlock::Create(
            context(), "labeladdr." + std::to_string(block.index), fn);
    }
    return llvm::BlockAddress::get(fn, bb);
}

llvm::Constant* Lowerer::constant_from_static_bytes(cir::TypeId type_id,
                                                    const std::vector<uint8_t>& bytes,
                                                    SrcLoc loc,
                                                    const std::vector<cir::StaticInitializerRelocation>& relocations) {
    if (!file_.valid(type_id)) {
        error("cannot lower static initializer for invalid type", loc);
        return nullptr;
    }
    type_id = file_.resolved_type(type_id);
    llvm::Type* target_type = llvm_type(type_id);
    if (!target_type) {
        return nullptr;
    }

    const cir::Type& type = file_.type(type_id);
    const cir::TypePayload& payload = file_.type_payload(type_id);
    auto relocation_base_constant =
        [&](const cir::StaticInitializerRelocation& relocation) -> llvm::Constant* {
            llvm::Constant* base = nullptr;
            if (relocation.block.valid()) {

                base = block_address_constant(relocation.entity,
                                              relocation.block, loc);
                if (!base) {
                    return nullptr;
                }
                if (relocation.addend != 0) {
                    llvm::Constant* index = llvm::ConstantInt::get(
                        llvm::Type::getInt64Ty(context()), relocation.addend, true);
                    base = llvm::ConstantExpr::getGetElementPtr(
                        llvm::Type::getInt8Ty(context()), base, index);
                }
                return base;
            }
            cir::EntityKind relocation_kind = file_.valid(relocation.entity)
                ? file_.entity(relocation.entity).kind
                : cir::EntityKind::Invalid;
            if (relocation_kind == cir::EntityKind::Function ||
                relocation_kind == cir::EntityKind::Method ||
                relocation_kind == cir::EntityKind::Constructor ||
                relocation_kind == cir::EntityKind::Destructor) {
                base = function_symbol(relocation.entity);
            } else if (relocation_kind == cir::EntityKind::Variable) {
                base = get_or_create_global(relocation.entity);
            }
            if (!base) {
                error("static initializer relocation references unsupported entity", loc);
                return nullptr;
            }
            if (relocation.addend != 0) {
                llvm::Constant* index = llvm::ConstantInt::get(
                    llvm::Type::getInt64Ty(context()), relocation.addend, true);
                base = llvm::ConstantExpr::getGetElementPtr(
                    llvm::Type::getInt8Ty(context()), base, index);
            }
            return base;
        };

    switch (type.kind) {
        case cir::TypeKind::Builtin: {
            if (!relocations.empty()) {

                auto* integer_type = llvm::dyn_cast<llvm::IntegerType>(target_type);
                const cir::StaticInitializerRelocation& rel = relocations.front();
                if (integer_type && relocations.size() == 1 &&
                    rel.offset == 0 && rel.block.valid() &&
                    rel.subtract_block.valid()) {
                    llvm::Constant* to =
                        block_address_constant(rel.entity, rel.block, loc);
                    llvm::Constant* from =
                        block_address_constant(rel.entity, rel.subtract_block, loc);
                    if (!to || !from) {
                        return nullptr;
                    }
                    llvm::IntegerType* intptr = llvm::Type::getInt64Ty(context());
                    llvm::Constant* diff = llvm::ConstantExpr::getSub(
                        llvm::ConstantExpr::getPtrToInt(to, intptr),
                        llvm::ConstantExpr::getPtrToInt(from, intptr));
                    if (rel.addend != 0) {
                        diff = llvm::ConstantExpr::getAdd(
                            diff,
                            llvm::ConstantInt::get(intptr, rel.addend, true));
                    }
                    unsigned dst_bits = integer_type->getBitWidth();
                    if (dst_bits < 64) {
                        return llvm::ConstantExpr::getTrunc(diff, integer_type);
                    }
                    if (dst_bits == 64) {
                        return diff;
                    }

                    error("label-difference initializer into an oversized "
                          "integer is not supported",
                          loc);
                    return nullptr;
                }

                if (integer_type && relocations.size() == 1 &&
                    rel.offset == 0 && !rel.block.valid() &&
                    !rel.subtract_block.valid()) {
                    llvm::Constant* base = relocation_base_constant(rel);
                    if (!base) {
                        return nullptr;
                    }
                    const unsigned pointer_bits =
                        file_.target_info().pointer_width;
                    llvm::IntegerType* intptr =
                        llvm::IntegerType::get(context(), pointer_bits);
                    llvm::Constant* addr =
                        llvm::ConstantExpr::getPtrToInt(base, intptr);
                    unsigned dst_bits = integer_type->getBitWidth();
                    if (dst_bits == pointer_bits) {
                        return addr;
                    }

                    error("relocation cannot initialize an integer that is "
                          "not pointer-width",
                          loc);
                    return nullptr;
                }
                error("relocation cannot initialize builtin static object", loc);
                return nullptr;
            }
            if (is_nullptr_type(type_id)) {
                if (!bytes_are_zero(bytes)) {
                    error("nonzero nullptr_t static initializer is not supported",
                          loc);
                    return nullptr;
                }
                return llvm_nullptr_carrier_value();
            }
            if (auto* integer_type = llvm::dyn_cast<llvm::IntegerType>(target_type)) {
                return integer_constant_from_bytes(integer_type, bytes);
            }
            if (target_type->isFloatingPointTy()) {
                if (target_type->isFloatTy() && bytes.size() >= sizeof(float)) {
                    float value = 0.0f;
                    std::memcpy(&value, bytes.data(), sizeof(float));
                    return llvm::ConstantFP::get(target_type, value);
                }
                if (target_type->isDoubleTy() && bytes.size() >= sizeof(double)) {
                    double value = 0.0;
                    std::memcpy(&value, bytes.data(), sizeof(double));
                    return llvm::ConstantFP::get(target_type, value);
                }
                if (!bytes_are_zero(bytes)) {
                    error("nonzero floating-point static initializer is not supported yet", loc);
                    return nullptr;
                }
                return llvm::Constant::getNullValue(target_type);
            }
            return llvm::Constant::getNullValue(target_type);
        }
        case cir::TypeKind::MemberPointer: {
            if (file_.member_pointer_points_to_function(type_id)) {
                llvm::StructType* struct_type =
                    llvm::dyn_cast<llvm::StructType>(target_type);
                if (!struct_type || struct_type != llvm_member_function_pointer_type()) {
                    error("member function pointer static initializer requires pair storage",
                          loc);
                    return nullptr;
                }
                size_t pointer_size = static_cast<size_t>(pointer_bytes());
                if (!relocations.empty() &&
                    (relocations.size() != 1 || relocations.front().offset != 0)) {
                    error("unsupported member function pointer static initializer relocation",
                          loc);
                    return nullptr;
                }
                std::vector<uint8_t> callee_bytes;
                if (bytes.size() >= pointer_size) {
                    callee_bytes.assign(bytes.begin(),
                                        bytes.begin() +
                                            static_cast<std::ptrdiff_t>(pointer_size));
                }
                llvm::Constant* callee = nullptr;
                if (relocations.empty()) {
                    if (bytes_are_zero(callee_bytes)) {
                        callee = llvm::ConstantPointerNull::get(
                            llvm::PointerType::get(context(), 0));
                    } else {
                        llvm::IntegerType* intptr_type = llvm::IntegerType::get(
                            context(), static_cast<unsigned>(pointer_bits()));
                        callee = llvm::ConstantExpr::getIntToPtr(
                            integer_constant_from_bytes(intptr_type,
                                                        callee_bytes),
                            llvm::PointerType::get(context(), 0));
                    }
                } else {
                    callee = relocation_base_constant(relocations.front());
                    if (!callee) {
                        return nullptr;
                    }
                    callee = llvm::ConstantExpr::getPointerCast(
                        callee, llvm::PointerType::get(context(), 0));
                }

                std::vector<uint8_t> adjust_bytes(pointer_size, 0);
                if (bytes.size() > pointer_size) {
                    size_t available = std::min(pointer_size,
                                                bytes.size() - pointer_size);
                    std::copy_n(bytes.begin() +
                                    static_cast<std::ptrdiff_t>(pointer_size),
                                available,
                                adjust_bytes.begin());
                }
                llvm::IntegerType* adjust_type = llvm::IntegerType::get(
                    context(), static_cast<unsigned>(pointer_bits()));
                llvm::Constant* adjust =
                    integer_constant_from_bytes(adjust_type, adjust_bytes);
                return llvm::ConstantStruct::get(struct_type, {callee, adjust});
            }
            if (!relocations.empty()) {
                error("relocation cannot initialize data member pointer static object",
                      loc);
                return nullptr;
            }
            auto* integer_type = llvm::dyn_cast<llvm::IntegerType>(target_type);
            if (!integer_type) {
                error("data member pointer static initializer requires integer storage",
                      loc);
                return nullptr;
            }
            return integer_constant_from_bytes(integer_type, bytes);
        }
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:

        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {
            if (!relocations.empty()) {
                if (relocations.size() != 1 || relocations.front().offset != 0) {
                    error("unsupported pointer static initializer relocation", loc);
                    return nullptr;
                }
                const cir::StaticInitializerRelocation& relocation = relocations.front();
                llvm::Constant* base = relocation_base_constant(relocation);
                if (!base) {
                    return nullptr;
                }
                return llvm::ConstantExpr::getPointerCast(
                    base, llvm::cast<llvm::PointerType>(target_type));
            }
            if (!bytes_are_zero(bytes)) {
                llvm::IntegerType* intptr_type = llvm::IntegerType::get(
                    context(), static_cast<unsigned>(pointer_bits()));
                llvm::Constant* raw = integer_constant_from_bytes(intptr_type, bytes);
                return llvm::ConstantExpr::getIntToPtr(
                    raw, llvm::cast<llvm::PointerType>(target_type));
            }
            return llvm::ConstantPointerNull::get(
                llvm::cast<llvm::PointerType>(target_type));
        }
        case cir::TypeKind::Array: {
            const auto& array = std::get<cir::ArrayTypePayload>(payload);
            if (!array.size.has_value()) {
                error("cannot lower static initializer for incomplete array", loc);
                return nullptr;
            }
            std::optional<uint64_t> element_size = size_of_type(array.element_type.type, loc);
            auto* array_type = llvm::dyn_cast<llvm::ArrayType>(target_type);
            if (!element_size.has_value() || !array_type) {
                return nullptr;
            }
            std::vector<llvm::Constant*> elements;
            elements.reserve(*array.size);
            for (size_t index = 0; index < *array.size; ++index) {
                size_t begin = index * static_cast<size_t>(*element_size);
                size_t end = begin < bytes.size()
                    ? std::min(bytes.size(), begin + static_cast<size_t>(*element_size))
                    : begin;
                std::vector<uint8_t> slice;
                if (begin < bytes.size()) {
                    slice.assign(bytes.begin() + static_cast<std::ptrdiff_t>(begin),
                                 bytes.begin() + static_cast<std::ptrdiff_t>(end));
                }
                if (slice.size() < *element_size) {
                    slice.resize(static_cast<size_t>(*element_size), 0);
                }
                std::vector<cir::StaticInitializerRelocation> element_relocations;
                for (cir::StaticInitializerRelocation relocation : relocations) {
                    if (relocation.offset < begin || relocation.offset >= begin + *element_size) {
                        continue;
                    }
                    relocation.offset -= begin;
                    element_relocations.push_back(relocation);
                }
                llvm::Constant* element =
                    constant_from_static_bytes(array.element_type.type,
                                               slice,
                                               loc,
                                               element_relocations);
                if (!element) {
                    return nullptr;
                }
                elements.push_back(element);
            }

            bool elements_match_array = std::all_of(
                elements.begin(), elements.end(), [&](llvm::Constant* element) {
                    return element->getType() == array_type->getElementType();
                });
            if (!elements_match_array) {
                return llvm::ConstantStruct::getAnon(context(), elements, true);
            }
            return llvm::ConstantArray::get(array_type, elements);
        }
        case cir::TypeKind::Record: {
            if (relocations.empty()) {
                return llvm::ConstantDataArray::get(context(), llvm::ArrayRef<uint8_t>(bytes));
            }
            std::vector<cir::StaticInitializerRelocation> sorted_relocations = relocations;
            std::sort(sorted_relocations.begin(),
                      sorted_relocations.end(),
                      [](const cir::StaticInitializerRelocation& lhs,
                         const cir::StaticInitializerRelocation& rhs) {
                          return lhs.offset < rhs.offset;
                      });
            size_t pointer_size = static_cast<size_t>(pointer_bytes());
            size_t object_size = bytes.size();
            std::vector<llvm::Constant*> fields;
            size_t cursor = 0;
            auto append_byte_chunk = [&](size_t begin, size_t end) {
                if (begin >= end) {
                    return;
                }
                std::vector<uint8_t> chunk(bytes.begin() + static_cast<std::ptrdiff_t>(begin),
                                           bytes.begin() + static_cast<std::ptrdiff_t>(end));
                fields.push_back(
                    llvm::ConstantDataArray::get(context(), llvm::ArrayRef<uint8_t>(chunk)));
            };

            for (const cir::StaticInitializerRelocation& relocation : sorted_relocations) {
                if (relocation.offset < cursor) {
                    error("overlapping static initializer relocations are not supported", loc);
                    return nullptr;
                }
                if (relocation.offset + pointer_size > object_size) {
                    error("static initializer relocation writes outside record object", loc);
                    return nullptr;
                }
                append_byte_chunk(cursor, relocation.offset);
                llvm::Constant* base = relocation_base_constant(relocation);
                if (!base) {
                    return nullptr;
                }
                fields.push_back(llvm::ConstantExpr::getPointerCast(
                    base, llvm::PointerType::get(context(), 0)));
                cursor = relocation.offset + pointer_size;
            }
            append_byte_chunk(cursor, object_size);
            std::vector<llvm::Type*> field_types;
            field_types.reserve(fields.size());
            for (llvm::Constant* field : fields) {
                field_types.push_back(field->getType());
            }
            llvm::StructType* struct_type = llvm::StructType::get(
                context(),
                llvm::ArrayRef<llvm::Type*>(field_types),
                true);
            return llvm::ConstantStruct::get(struct_type, fields);
        }
        case cir::TypeKind::Enum: {
            const auto& enum_payload = std::get<cir::EnumTypePayload>(payload);
            return enum_payload.underlying_type.valid()
                ? constant_from_static_bytes(enum_payload.underlying_type.type,
                                             bytes,
                                             loc,
                                             relocations)
                : integer_constant_from_bytes(llvm::cast<llvm::IntegerType>(target_type), bytes);
        }
        case cir::TypeKind::BitInt: {
            if (!relocations.empty()) {
                error("relocation cannot initialize _BitInt static object", loc);
                return nullptr;
            }
            if (auto* integer_type = llvm::dyn_cast<llvm::IntegerType>(target_type)) {
                return integer_constant_from_bytes(integer_type, bytes);
            }
            return llvm::Constant::getNullValue(target_type);
        }
        case cir::TypeKind::Complex: {
            if (!relocations.empty()) {
                error("relocation cannot initialize complex static object", loc);
                return nullptr;
            }
            const auto& complex = std::get<cir::ComplexTypePayload>(payload);
            std::optional<size_t> element_size =
                cir::size_of_type(file_, complex.element_type.type);
            auto* array_type = llvm::dyn_cast<llvm::ArrayType>(target_type);
            if (!element_size.has_value() || !array_type) {
                return llvm::Constant::getNullValue(target_type);
            }
            auto element_at = [&](size_t index) -> llvm::Constant* {
                size_t at = index * *element_size;
                llvm::Type* element_type = array_type->getElementType();
                if (auto* integer_type = llvm::dyn_cast<llvm::IntegerType>(element_type)) {
                    std::vector<uint8_t> lane(
                        bytes.begin() + std::min(at, bytes.size()),
                        bytes.begin() + std::min(at + *element_size, bytes.size()));
                    return integer_constant_from_bytes(integer_type, lane);
                }
                if (*element_size == sizeof(float) && at + sizeof(float) <= bytes.size()) {
                    float value = 0.0f;
                    std::memcpy(&value, bytes.data() + at, sizeof(float));
                    return llvm::ConstantFP::get(element_type, value);
                }
                if (at + sizeof(double) <= bytes.size()) {
                    double value = 0.0;
                    std::memcpy(&value, bytes.data() + at, sizeof(double));
                    return llvm::ConstantFP::get(element_type, value);
                }
                return llvm::Constant::getNullValue(element_type);
            };
            return llvm::ConstantArray::get(array_type, {element_at(0), element_at(1)});
        }
        case cir::TypeKind::Vector: {
            if (!relocations.empty()) {
                error("relocation cannot initialize vector static object", loc);
                return nullptr;
            }
            const auto& vector = std::get<cir::VectorTypePayload>(payload);
            auto* vector_type = llvm::dyn_cast<llvm::FixedVectorType>(target_type);
            if (!vector_type) {
                return llvm::Constant::getNullValue(target_type);
            }
            std::optional<size_t> element_size =
                cir::size_of_type(file_, vector.element_type.type);
            if (!element_size.has_value() || *element_size == 0) {
                error("vector static initializer element has no layout", loc);
                return nullptr;
            }
            std::vector<llvm::Constant*> lanes;
            lanes.reserve(vector.element_count);
            for (uint32_t lane = 0; lane < vector.element_count; ++lane) {
                size_t offset = static_cast<size_t>(lane) * *element_size;
                std::vector<uint8_t> lane_bytes(
                    bytes.begin() + std::min(offset, bytes.size()),
                    bytes.begin() + std::min(offset + *element_size, bytes.size()));
                llvm::Constant* lane_value =
                    constant_from_static_bytes(vector.element_type.type,
                                               lane_bytes,
                                               loc,
                                               {});
                if (!lane_value) {
                    return nullptr;
                }
                lanes.push_back(lane_value);
            }
            return llvm::ConstantVector::get(lanes);
        }
        case cir::TypeKind::Typedef:
            return constant_from_static_bytes(
                std::get<cir::TypedefTypePayload>(payload).underlying_type.type,
                bytes,
                loc,
                relocations);
        default:
            error("unsupported static initializer type", loc);
            return nullptr;
    }
}

} // namespace aburi::cir2llvm
