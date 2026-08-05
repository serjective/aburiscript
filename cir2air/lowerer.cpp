#include "lowerer.h"

#include <algorithm>
#include <utility>
#include <variant>

#include "../abi/aarch64_call_classify.h"
#include "../abi/mangle_cir.h"
#include "../cir/layout.h"

namespace aburi::cir2air {

Lowerer::Lowerer(const cir::File& file, AirLoweringOptions options)
    : file_(file), options_(std::move(options)) {}

AirLoweringResult Lowerer::run() {
    if (!options_.target) {
        options_.target = file_.target_info_ptr();
    }
    if (!options_.target) {
        options_.target = TargetInfo::create_host();
    }

    result_.module = std::make_unique<air::Module>(options_.target);
    mod_ = result_.module.get();

    for (const std::string& module_asm : file_.module_asm()) {
        mod_->add_module_asm(module_asm);
    }

    declare_entities();
    for (cir::FunctionId function_id : file_.function_ids()) {
        const cir::Function& function = file_.function(function_id);
        if (file_.valid(function.entity)) {
            const cir::Entity& entity = file_.entity(function.entity);

            if (entity.is_template_pattern ||
                entity.result_type_only_definition ||
                entity.decl_flags.is_consteval ||
                entity.suppressed_by_explicit_instantiation_declaration ||
                entity.suppressed_as_unselected_template_candidate) {
                continue;
            }
        }
        if (!file_.valid(function.entity)) {
            continue;
        }
        lower_function(function_id);
    }
    collect_static_ctors();

    return std::move(result_);
}

void Lowerer::error(std::string message, SrcLoc loc) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "cir2air: " + std::move(message);
    diag.location = loc;
    result_.diagnostics.push_back(std::move(diag));
}

bool Lowerer::has_errors() const {
    return error_count() > 0;
}

size_t Lowerer::error_count() const {
    size_t count = 0;
    for (const Diagnostic& diag : result_.diagnostics) {
        if (diag.level == DiagnosticLevel::Error) {
            ++count;
        }
    }
    return count;
}

uint64_t Lowerer::pointer_bytes() const {
    int width = options_.target ? options_.target->pointer_width : 64;
    return std::max<uint64_t>(1, static_cast<uint64_t>((width + 7) / 8));
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

bool Lowerer::is_unsigned_domain(cir::TypeId type_id) const {
    if (!file_.valid(type_id)) {
        return false;
    }
    cir::OperatorValueDomain domain =
        file_.operator_value_domain(file_.type_ref(type_id));
    return domain == cir::OperatorValueDomain::UnsignedInteger ||
           domain == cir::OperatorValueDomain::Bool;
}

bool Lowerer::is_memory_only_type(cir::TypeId type_id) const {
    type_id = file_.resolved_type(type_id);
    if (!file_.valid(type_id)) {
        return false;
    }
    switch (file_.type(type_id).kind) {
        case cir::TypeKind::Record:
        case cir::TypeKind::Array:
        case cir::TypeKind::Complex:
        case cir::TypeKind::Vector:
            return true;
        case cir::TypeKind::Builtin: {
            cir::BuiltinTypeKind kind = std::get<cir::BuiltinTypePayload>(
                file_.type_payload(type_id)).kind;
            return kind == cir::BuiltinTypeKind::Int128 ||
                   kind == cir::BuiltinTypeKind::UInt128;
        }
        case cir::TypeKind::BitInt:
            return std::get<cir::BitIntTypePayload>(
                       file_.type_payload(type_id)).bits > 64;
        default:
            return false;
    }
}

std::optional<air::TypeId> Lowerer::air_type(cir::TypeId type_id) {
    if (!file_.valid(type_id)) {
        return std::nullopt;
    }
    type_id = file_.resolved_type(type_id);
    const cir::Type& type = file_.type(type_id);
    const cir::TypePayload& payload = file_.type_payload(type_id);
    air::TypeTable& types = mod_->types();
    switch (type.kind) {
        case cir::TypeKind::Builtin:
            switch (std::get<cir::BuiltinTypePayload>(payload).kind) {
                case cir::BuiltinTypeKind::Void:
                    return air::types::VOID;
                case cir::BuiltinTypeKind::NullPtr:
                    return air_nullptr_carrier_type();
                case cir::BuiltinTypeKind::MetaInfo:

                    return types.get_int(
                        static_cast<uint16_t>(options_.target->pointer_width));
                case cir::BuiltinTypeKind::Bool:
                case cir::BuiltinTypeKind::Char:
                case cir::BuiltinTypeKind::SChar:
                case cir::BuiltinTypeKind::UChar:
                case cir::BuiltinTypeKind::Char8:
                    return air::types::I8;
                case cir::BuiltinTypeKind::WChar:
                    return types.get_int(
                        static_cast<uint16_t>(options_.target->wchar_width));
                case cir::BuiltinTypeKind::Char16:
                case cir::BuiltinTypeKind::Short:
                case cir::BuiltinTypeKind::UShort:
                    return air::types::I16;
                case cir::BuiltinTypeKind::Char32:
                case cir::BuiltinTypeKind::Int:
                case cir::BuiltinTypeKind::UInt:
                    return air::types::I32;
                case cir::BuiltinTypeKind::Long:
                case cir::BuiltinTypeKind::ULong:
                    return types.get_int(
                        static_cast<uint16_t>(options_.target->long_width));
                case cir::BuiltinTypeKind::LongLong:
                case cir::BuiltinTypeKind::ULongLong:
                    return air::types::I64;
                case cir::BuiltinTypeKind::Int128:
                case cir::BuiltinTypeKind::UInt128:

                    return std::nullopt;
                case cir::BuiltinTypeKind::USize:
                    return types.get_int(
                        static_cast<uint16_t>(pointer_bytes() * 8));
                case cir::BuiltinTypeKind::Float:
                    return air::types::F32;
                case cir::BuiltinTypeKind::Double:
                    return air::types::F64;
                case cir::BuiltinTypeKind::LongDouble:
                    if (options_.target->long_double_format ==
                        LongDoubleFormat::IEEE_DOUBLE) {
                        return air::types::F64;
                    }
                    if (options_.target->long_double_format ==
                        LongDoubleFormat::IEEE_QUAD) {
                        return air::types::F128;
                    }
                    if (options_.target->long_double_format ==
                        LongDoubleFormat::X87_EXTENDED) {
                        return air::types::F80;
                    }
                    return std::nullopt;
                case cir::BuiltinTypeKind::Float16:
                case cir::BuiltinTypeKind::Other:
                    return std::nullopt;
            }
            return std::nullopt;
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
        case cir::TypeKind::Place:

        case cir::TypeKind::Function:
            return air::types::PTR;
        case cir::TypeKind::Enum: {
            const auto& enum_payload = std::get<cir::EnumTypePayload>(payload);
            return enum_payload.underlying_type.valid()
                ? air_type(enum_payload.underlying_type.type)
                : std::optional<air::TypeId>(air::types::I32);
        }
        case cir::TypeKind::BitInt: {
            uint16_t bits = std::get<cir::BitIntTypePayload>(payload).bits;
            switch (bits) {
                case 8:
                case 16:
                case 32:
                case 64:
                    return types.get_int(bits);
                default:
                    return std::nullopt;
            }
        }
        case cir::TypeKind::Typedef:
            return air_type(
                std::get<cir::TypedefTypePayload>(payload).underlying_type.type);
        default:
            return std::nullopt;
    }
}

bool Lowerer::is_nullptr_type(cir::TypeId type_id) const {
    type_id = file_.resolved_type(type_id);
    if (!file_.valid(type_id) ||
        file_.type(type_id).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* builtin =
        std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(type_id));
    return builtin && builtin->kind == cir::BuiltinTypeKind::NullPtr;
}

air::TypeId Lowerer::air_nullptr_carrier_type() const {

    return air::types::PTR;
}

Lowerer::SignatureInfo Lowerer::signature_for_function_type(cir::TypeId function_type,
                                                            SrcLoc loc) {
    if (!file_.valid(function_type)) {
        SignatureInfo info;
        error("cannot lower invalid function type", loc);
        return info;
    }
    cir::TypeId resolved = file_.resolved_type(function_type);
    auto found = signatures_.find(id_key(resolved));
    if (found != signatures_.end()) {
        return found->second;
    }

    SignatureInfo info;
    if (!file_.valid(resolved) ||
        file_.type(resolved).kind != cir::TypeKind::Function) {
        error("cannot lower non-function type as a function", loc);
        signatures_[id_key(resolved)] = info;
        return info;
    }
    const auto& payload =
        std::get<cir::FunctionTypePayload>(file_.type_payload(resolved));
    if (payload.exception_spec.kind ==
        cir::FunctionExceptionSpecKind::Dependent) {
        error("cannot lower a function type with an unresolved dependent "
              "exception specification",
              loc);
        signatures_[id_key(resolved)] = info;
        return info;
    }
    info.return_type = payload.return_type;
    info.is_variadic = payload.is_variadic;
    info.has_prototype = payload.has_prototype;
    info.may_throw =
        payload.exception_spec.kind !=
            cir::FunctionExceptionSpecKind::NonThrowing;

    air::SigData sig;
    sig.is_variadic = payload.is_variadic;

    const TargetInfo* target = options_.target.get();
    info.ret_class =
        abi::classify_argument_native(file_, payload.return_type, target);
    switch (info.ret_class.pass) {
        case abi::AggregatePass::UseSourceType: {
            std::optional<air::TypeId> ret_type = air_type(payload.return_type);
            if (!ret_type) {
                error("not supported by the air backend yet: return type " +
                          std::string(cir::type_kind_name(
                              file_.type(file_.resolved_type(payload.return_type.type)).kind)),
                      loc);
                signatures_[id_key(resolved)] = info;
                return info;
            }
            if (*ret_type == air::types::VOID) {
                sig.ret_class = air::RetClass::Void;
            } else {
                sig.ret_class = air::RetClass::Scalar;
                sig.ret_type = *ret_type;
                sig.ret_count = 1;
            }
            break;
        }
        case abi::AggregatePass::Ignore:

            sig.ret_class = air::RetClass::Void;
            break;
        case abi::AggregatePass::CoerceIntSlots: {
            air::TypeId slot_type = info.ret_class.slot_bytes == 4
                ? air::types::I32
                : air::types::I64;
            if (info.ret_class.int_slot_count <= 1) {
                sig.ret_class = air::RetClass::Scalar;
                sig.ret_type = slot_type;
                sig.ret_count = 1;
            } else {
                sig.ret_class = air::RetClass::IntPair;
                sig.ret_type = slot_type;
                sig.ret_count = 2;
            }
            break;
        }
        case abi::AggregatePass::CoerceClassedSlots:
            if (info.ret_class.int_slot_count <= 1) {
                sig.ret_class = air::RetClass::Scalar;
                sig.ret_type = (info.ret_class.sse_slot_mask & 1)
                    ? air::types::F64
                    : air::types::I64;
                sig.ret_count = 1;
            } else {
                sig.ret_class = air::RetClass::IntPair;
                sig.ret_type = air::types::I64;
                sig.ret_count = 2;
                sig.ret_sse_mask = info.ret_class.sse_slot_mask;
            }
            break;
        case abi::AggregatePass::CoerceHfa: {
            std::optional<air::TypeId> element =
                hfa_element_type(info.ret_class.hfa_element, loc);
            if (!element) {
                signatures_[id_key(resolved)] = info;
                return info;
            }
            if (info.ret_class.hfa_count <= 1) {
                sig.ret_class = air::RetClass::Scalar;
                sig.ret_type = *element;
                sig.ret_count = 1;
            } else {
                sig.ret_class = air::RetClass::Hfa;
                sig.ret_type = *element;
                sig.ret_count = info.ret_class.hfa_count;
            }
            break;
        }
        case abi::AggregatePass::Indirect:
        case abi::AggregatePass::MemoryByval:

            sig.ret_class = air::RetClass::IndirectSret;
            sig.params.push_back({air::types::PTR, air::ParamRole::Sret});
            break;
    }

    for (cir::TypeRef param : payload.parameters) {
        abi::AggregateClass param_class =
            abi::classify_argument_native(file_, param, target);
        info.param_types.push_back(param);
        info.param_classes.push_back(param_class);
        switch (param_class.pass) {
            case abi::AggregatePass::UseSourceType: {
                std::optional<air::TypeId> param_type = air_type(param);
                if (!param_type || *param_type == air::types::VOID) {
                    error("not supported by the air backend yet: parameter type",
                          loc);
                    signatures_[id_key(resolved)] = info;
                    return info;
                }
                sig.params.push_back({*param_type, air::ParamRole::Normal});
                break;
            }
            case abi::AggregatePass::Ignore:

                break;
            case abi::AggregatePass::CoerceIntSlots: {
                air::TypeId slot_type = param_class.slot_bytes == 4
                    ? air::types::I32
                    : air::types::I64;
                for (uint8_t slot = 0; slot < param_class.int_slot_count; ++slot) {
                    air::SigParam slot_param{slot_type, air::ParamRole::Normal};
                    if (slot == 0 && param_class.int_slot_count > 1) {
                        slot_param.coerce_group = param_class.int_slot_count;
                    }
                    sig.params.push_back(slot_param);
                }
                break;
            }
            case abi::AggregatePass::CoerceHfa: {
                std::optional<air::TypeId> element =
                    hfa_element_type(param_class.hfa_element, loc);
                if (!element) {
                    signatures_[id_key(resolved)] = info;
                    return info;
                }
                for (uint8_t lane = 0; lane < param_class.hfa_count; ++lane) {
                    sig.params.push_back({*element, air::ParamRole::Normal});
                }
                break;
            }
            case abi::AggregatePass::CoerceClassedSlots:
                for (uint8_t slot = 0; slot < param_class.int_slot_count;
                     ++slot) {
                    bool sse = (param_class.sse_slot_mask >> slot) & 1;
                    air::SigParam slot_param{
                        sse ? air::types::F64 : air::types::I64,
                        air::ParamRole::Normal};
                    if (slot == 0 && param_class.int_slot_count > 1) {
                        slot_param.coerce_group = param_class.int_slot_count;
                    }
                    sig.params.push_back(slot_param);
                }
                break;
            case abi::AggregatePass::Indirect:
                sig.params.push_back({air::types::PTR, air::ParamRole::IndirectByval});
                break;
            case abi::AggregatePass::MemoryByval: {
                air::SigParam byval;
                byval.type = air::types::PTR;
                byval.role = air::ParamRole::StackByval;
                byval.byval_size = static_cast<uint32_t>(
                    std::max<uint64_t>(1, param_class.byte_size));
                byval.byval_align = std::max<uint32_t>(1, param_class.byte_align);
                sig.params.push_back(byval);
                break;
            }
        }
    }
    sig.fixed_param_count = static_cast<uint32_t>(sig.params.size());

    info.sig = mod_->types().get_signature(std::move(sig));
    info.ok = true;
    signatures_[id_key(resolved)] = info;
    return info;
}

std::optional<air::TypeId> Lowerer::hfa_element_type(cir::BuiltinTypeKind kind,
                                                     SrcLoc loc) {
    switch (kind) {
        case cir::BuiltinTypeKind::Float:
            return air::types::F32;
        case cir::BuiltinTypeKind::Double:
            return air::types::F64;
        default:
            error("not supported by the air backend yet: _Float16 aggregates",
                  loc);
            return std::nullopt;
    }
}

void Lowerer::declare_entities() {
    for (cir::EntityId entity_id : file_.entity_ids()) {
        const cir::Entity& entity = file_.entity(entity_id);
        if (entity.is_template_pattern ||
            entity.result_type_only_definition ||
            entity.suppressed_by_explicit_instantiation_declaration ||
            entity.suppressed_as_unselected_template_candidate) {
            continue;
        }
        if (!entity.is_definition) {
            if (!entity.attr_facts.weakref_target.empty() &&
                entity.attr_facts.is_weak) {
                error("not supported by the air backend yet: weak symbol aliases",
                      entity.loc);
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

air::FuncId Lowerer::declare_runtime_helper(const std::string& name,
                                            air::SigId sig) {
    auto found = runtime_helpers_.find(name);
    if (found != runtime_helpers_.end()) {
        return found->second;
    }
    air::FuncId func = mod_->find_function(name);
    if (!func.is_valid()) {
        func = mod_->create_function(name, sig, air::Linkage::External);
    }
    runtime_helpers_[name] = func;
    return func;
}

air::FuncId Lowerer::get_or_declare_function(cir::EntityId entity_id) {
    auto found = function_ids_.find(id_key(entity_id));
    if (found != function_ids_.end()) {
        return found->second;
    }

    const cir::Entity& entity = file_.entity(entity_id);
    bool emits_definition = false;
    if (entity.is_definition && !entity.decl_flags.is_consteval &&
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
    if (!entity.attr_facts.weakref_target.empty()) {
        error("not supported by the air backend yet: weakref function aliases",
              entity.loc);
        function_ids_[id_key(entity_id)] = air::FuncId{};
        return air::FuncId{};
    }
    SignatureInfo sig_info = signature_for_function_type(entity.type, entity.loc);
    if (!sig_info.ok) {
        function_ids_[id_key(entity_id)] = air::FuncId{};
        return air::FuncId{};
    }

    std::string name = linkage_name(entity_id);
    air::Linkage linkage = air::Linkage::External;
    cir::LinkageKind resolved_linkage = entity.symbol_policy.finalized
        ? entity.symbol_policy.emission
        : entity.linkage;
    if (!emits_definition) {
        linkage = air::Linkage::External;
    } else if (resolved_linkage == cir::LinkageKind::Internal) {
        linkage = air::Linkage::Internal;
    } else if (resolved_linkage == cir::LinkageKind::LinkOnceODR) {
        linkage = air::Linkage::LinkOnceODR;
    }
    if (entity.attr_facts.is_weak && emits_definition) {
        linkage = air::Linkage::Weak;
    }

    air::FuncId func = mod_->find_function(name);
    if (!func.is_valid()) {
        func = mod_->create_function(name, sig_info.sig, linkage);
    } else if (emits_definition) {
        mod_->function(func).set_linkage(linkage);
    }
    air::Function& air_func = mod_->function(func);
    if (entity.symbol_policy.finalized) {
        switch (entity.symbol_policy.visibility) {
            case cir::SymbolVisibilityKind::Default:
                air_func.attrs().visibility = air::SymbolVisibility::Default;
                break;
            case cir::SymbolVisibilityKind::Hidden:
                air_func.attrs().visibility = air::SymbolVisibility::Hidden;
                air_func.attrs().hidden = true;
                break;
            case cir::SymbolVisibilityKind::Protected:
                air_func.attrs().visibility = air::SymbolVisibility::Protected;
                break;
        }
        if (emits_definition && entity.symbol_policy.comdat_key.valid()) {
            air_func.attrs().comdat_key = std::string(
                file_.name(entity.symbol_policy.comdat_key));
        }
    } else if (entity.attr_facts.visibility == "hidden") {
        air_func.attrs().hidden = true;
        air_func.attrs().visibility = air::SymbolVisibility::Hidden;
    }
    air_func.set_loc(entity.loc);
    if (entity.attr_facts.destructor_priority >= 0 && entity.is_definition) {
        error("not supported by the air backend yet: destructor attribute",
              entity.loc);
    }
    function_ids_[id_key(entity_id)] = func;
    return func;
}

air::GlobalId Lowerer::get_or_create_global(cir::EntityId entity_id) {
    auto found = global_ids_.find(id_key(entity_id));
    if (found != global_ids_.end()) {
        return found->second;
    }

    const cir::Entity& entity = file_.entity(entity_id);
    bool emits_definition =
        entity.is_definition &&
        !entity.suppressed_by_explicit_instantiation_declaration;
    if (!entity.attr_facts.weakref_target.empty()) {
        error("not supported by the air backend yet: weakref variable aliases",
              entity.loc);
        global_ids_[id_key(entity_id)] = air::GlobalId{};
        return air::GlobalId{};
    }
    air::GlobalData data;
    data.name = linkage_name(entity_id);
    if (!entity.attr_facts.asm_label.empty()) {
        data.name = entity.attr_facts.asm_label;
        data.attrs.no_prefix = true;
    }
    data.loc = entity.loc;
    data.is_thread_local =
        entity.storage_duration == cir::StorageDuration::Thread;

    auto size_align = cir::size_align_of_type(file_, entity.type);
    if (size_align) {
        data.size_bytes = static_cast<uint64_t>(size_align->size_bytes);
        data.align_bytes = static_cast<uint32_t>(std::max<size_t>(
            1, std::max(size_align->alignment_bytes,
                        entity.attr_facts.requested_alignment)));
    } else if (entity.is_definition) {
        error("cannot lower global storage type for " +
                  file_.format_entity(entity_id),
              entity.loc);
        global_ids_[id_key(entity_id)] = air::GlobalId{};
        return air::GlobalId{};
    }

    data.linkage = air::Linkage::External;
    cir::LinkageKind resolved_linkage = entity.symbol_policy.finalized
        ? entity.symbol_policy.emission
        : entity.linkage;
    if (!emits_definition) {
        data.linkage = air::Linkage::External;
    } else if (resolved_linkage == cir::LinkageKind::Internal) {
        data.linkage = air::Linkage::Internal;
    } else if (resolved_linkage == cir::LinkageKind::LinkOnceODR) {
        data.linkage = air::Linkage::LinkOnceODR;
    }
    if (entity.attr_facts.is_weak && emits_definition) {
        data.linkage = air::Linkage::Weak;
    }
    if (entity.attr_facts.is_common && emits_definition) {
        data.linkage = air::Linkage::Common;
    }
    if (entity.symbol_policy.finalized) {
        switch (entity.symbol_policy.visibility) {
            case cir::SymbolVisibilityKind::Default:
                data.attrs.visibility = air::SymbolVisibility::Default;
                break;
            case cir::SymbolVisibilityKind::Hidden:
                data.attrs.visibility = air::SymbolVisibility::Hidden;
                data.attrs.hidden = true;
                break;
            case cir::SymbolVisibilityKind::Protected:
                data.attrs.visibility = air::SymbolVisibility::Protected;
                break;
        }
        if (entity.symbol_policy.comdat_key.valid()) {
            data.attrs.comdat_key = std::string(
                file_.name(entity.symbol_policy.comdat_key));
        }
    } else if (entity.attr_facts.visibility == "hidden") {
        data.attrs.hidden = true;
        data.attrs.visibility = air::SymbolVisibility::Hidden;
    }
    if (!entity.attr_facts.section.empty()) {
        data.section = air::SectionKind::Custom;
        data.custom_section = entity.attr_facts.section;
    }

    bool needs_init_image = false;
    bool read_only_object =
        entity.object_origin ==
            cir::EntityObjectOrigin::TemplateParameterObject ||
        ((entity.qualifiers & cir::QualConst) != 0 &&
         entity.has_static_initializer &&
         !cir::type_has_mutable_subobject(file_, entity.type));
    if (!emits_definition) {
        data.init = air::GlobalInit::none();
    } else if (entity.has_static_initializer &&
               (!entity.static_initializer_relocations.empty() ||
                std::any_of(entity.static_initializer_bytes.begin(),
                            entity.static_initializer_bytes.end(),
                            [](uint8_t byte) { return byte != 0; }))) {
        needs_init_image = true;
        if (data.section == air::SectionKind::Data &&
            entity.attr_facts.section.empty() &&
            read_only_object) {

            data.section = air::SectionKind::Const;
        }
    } else {
        data.init = air::GlobalInit::zero();
        if (entity.attr_facts.section.empty()) {
            data.section = air::SectionKind::Zerofill;
        }
    }
    if (emits_definition && read_only_object &&
        entity.attr_facts.section.empty() &&
        (data.section == air::SectionKind::Data ||
         data.section == air::SectionKind::Zerofill)) {
        data.section = air::SectionKind::Const;
    }

    air::GlobalId global = mod_->find_global(data.name);
    if (global.is_valid()) {
        air::GlobalData& existing = mod_->global(global);
        bool existing_defined = existing.init.kind != air::GlobalInitKind::None;
        if (emits_definition && existing_defined) {
            error("duplicate global definition for " + data.name, entity.loc);
            global_ids_[id_key(entity_id)] = air::GlobalId{};
            return air::GlobalId{};
        }
        if (emits_definition) {
            existing.size_bytes = data.size_bytes;
            existing.align_bytes = data.align_bytes;
            existing.linkage = data.linkage;
            existing.section = data.section;
            existing.custom_section = data.custom_section;
            existing.attrs = data.attrs;
            existing.init = data.init;
            existing.loc = data.loc;
        }
        global_ids_[id_key(entity_id)] = global;
        if (!emits_definition || !needs_init_image) {
            return global;
        }
    } else {

        global = mod_->create_global(std::move(data));
        global_ids_[id_key(entity_id)] = global;
    }

    if (needs_init_image) {
        std::vector<uint8_t> bytes = entity.static_initializer_bytes;
        if (bytes.size() < mod_->global(global).size_bytes) {
            bytes.resize(mod_->global(global).size_bytes, 0);
        }
        std::vector<air::InitReloc> relocs;
        bool relocs_ok = true;
        for (const cir::StaticInitializerRelocation& relocation :
             entity.static_initializer_relocations) {
            air::InitReloc out;
            out.offset = relocation.offset;
            out.addend = relocation.addend;
            if (relocation.block.valid()) {

                error("block-address static initializer (a GNU label address) "
                      "is not supported on the AIR backend yet",
                      entity.loc);
                relocs_ok = false;
                break;
            }
            cir::EntityKind kind = file_.valid(relocation.entity)
                ? file_.entity(relocation.entity).kind
                : cir::EntityKind::Invalid;
            if (kind == cir::EntityKind::Function ||
                kind == cir::EntityKind::Method ||
                kind == cir::EntityKind::Constructor ||
                kind == cir::EntityKind::Destructor) {
                air::FuncId target = get_or_declare_function(relocation.entity);
                if (!target.is_valid()) {
                    relocs_ok = false;
                    break;
                }
                out.is_function = true;
                out.target_index = target.index;
            } else if (kind == cir::EntityKind::Variable) {
                air::GlobalId target = get_or_create_global(relocation.entity);
                if (!target.is_valid()) {
                    relocs_ok = false;
                    break;
                }
                out.is_function = false;
                out.target_index = target.index;
            } else {
                error("static initializer relocation references unsupported entity",
                      entity.loc);
                relocs_ok = false;
                break;
            }
            relocs.push_back(out);
        }
        if (relocs_ok) {
            mod_->global(global).init =
                air::GlobalInit::data(std::move(bytes), std::move(relocs));
        }
    }
    return global;
}

air::GlobalId Lowerer::intern_string_literal(const std::vector<uint8_t>& bytes,
                                             uint64_t element_size,
                                             SrcLoc loc) {
    std::string key(reinterpret_cast<const char*>(bytes.data()), bytes.size());
    key.push_back(static_cast<char>('0' + (element_size & 0xF)));
    auto found = string_globals_.find(key);
    if (found != string_globals_.end()) {
        return air::GlobalId{found->second};
    }

    bool cstring_shape = element_size == 1 && !bytes.empty() &&
                         bytes.back() == 0 &&
                         std::find(bytes.begin(), bytes.end() - 1, 0) ==
                             bytes.end() - 1;
    air::GlobalData data;
    data.name = "l_.str." + std::to_string(string_counter_++);
    data.size_bytes = bytes.size();
    data.align_bytes = static_cast<uint32_t>(std::max<uint64_t>(1, element_size));
    data.linkage = air::Linkage::Internal;
    data.section = cstring_shape ? air::SectionKind::Cstring
                                 : air::SectionKind::Const;
    data.attrs.no_prefix = true;
    data.init = air::GlobalInit::data(bytes);
    data.loc = loc;
    air::GlobalId global = mod_->create_global(std::move(data));
    string_globals_[key] = global.index;
    return global;
}

void Lowerer::collect_static_ctors() {
    struct CtorRecord {
        uint32_t priority;
        air::FuncId func;
    };
    std::vector<CtorRecord> ctors;
    for (cir::EntityId entity_id : file_.entity_ids()) {
        const cir::Entity& entity = file_.entity(entity_id);
        if (entity.kind != cir::EntityKind::Function || !entity.is_definition ||
            entity.attr_facts.constructor_priority < 0) {
            continue;
        }

        if (entity.symbol_policy.imported_definition &&
            entity.symbol_policy.emission != cir::LinkageKind::LinkOnceODR) {
            continue;
        }
        air::FuncId func = get_or_declare_function(entity_id);
        if (!func.is_valid()) {
            continue;
        }
        ctors.push_back({static_cast<uint32_t>(
                             entity.attr_facts.constructor_priority),
                         func});
    }
    std::stable_sort(ctors.begin(), ctors.end(),
                     [](const CtorRecord& lhs, const CtorRecord& rhs) {
                         return lhs.priority < rhs.priority;
                     });
    for (const CtorRecord& ctor : ctors) {
        mod_->add_ctor(ctor.priority, ctor.func);
    }
}

} // namespace aburi::cir2air
