#include "lowerer.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstring>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>

#include "../abi/aarch64_call_classify.h"
#include "../cir/layout.h"
#include "../cir/inst_schema.h"

namespace aburi::cir2llvm {
namespace {

uint64_t integer_from_bytes(const cir::LiteralByteArray& bytes) {
    uint64_t value = 0;
    for (uint8_t byte : bytes) {
        value = (value << 8) | byte;
    }
    return value;
}

std::optional<llvm::APFloat> exact_apfloat(cir::FloatingValue value) {
    const llvm::fltSemantics* semantics = nullptr;
    switch (value.semantics) {
        case cir::FloatingSemantics::IEEEBinary16:
            semantics = &llvm::APFloat::IEEEhalf();
            break;
        case cir::FloatingSemantics::IEEEBinary32:
            semantics = &llvm::APFloat::IEEEsingle();
            break;
        case cir::FloatingSemantics::IEEEBinary64:
            semantics = &llvm::APFloat::IEEEdouble();
            break;
        case cir::FloatingSemantics::X87Extended80:
            semantics = &llvm::APFloat::x87DoubleExtended();
            break;
        case cir::FloatingSemantics::IEEEBinary128:
            semantics = &llvm::APFloat::IEEEquad();
            break;
        case cir::FloatingSemantics::Invalid:
            break;
    }
    if (!semantics || !value.canonical()) {
        return std::nullopt;
    }
    uint64_t words[2] = {value.low_bits, value.high_bits};
    llvm::APInt bits(value.bit_width(),
                     llvm::ArrayRef<uint64_t>(
                         words, value.bit_width() > 64 ? 2 : 1));
    return llvm::APFloat(*semantics, bits);
}

std::string translate_gcc_to_llvm_asm(const std::string& tmpl) {
    std::string result;
    result.reserve(tmpl.size());
    for (size_t index = 0; index < tmpl.size(); ++index) {
        if (tmpl[index] == '$') {
            result += "$$";
            continue;
        }
        if (tmpl[index] != '%') {
            result += tmpl[index];
            continue;
        }
        if (index + 1 >= tmpl.size()) {
            result += '%';
            continue;
        }
        char next = tmpl[index + 1];
        if (next == '%') {
            result += '%';
            ++index;
            continue;
        }
        if (std::isdigit(static_cast<unsigned char>(next))) {
            result += '$';
            ++index;
            while (index < tmpl.size() &&
                   std::isdigit(static_cast<unsigned char>(tmpl[index]))) {
                result += tmpl[index];
                ++index;
            }
            --index;
            continue;
        }
        if (std::isalpha(static_cast<unsigned char>(next)) &&
            index + 2 < tmpl.size() &&
            std::isdigit(static_cast<unsigned char>(tmpl[index + 2]))) {
            char modifier = next;
            index += 2;
            std::string number;
            while (index < tmpl.size() &&
                   std::isdigit(static_cast<unsigned char>(tmpl[index]))) {
                number += tmpl[index];
                ++index;
            }
            --index;
            result += "${" + number + ":" + modifier + "}";
            continue;
        }
        result += '%';
    }
    return result;
}

std::string normalize_gcc_constraint_for_llvm(std::string constraint) {
    for (char& ch : constraint) {
        if (ch == 'g' || ch == 'X') {
            ch = 'r';
        } else if (ch == 'Q') {
            ch = 'm';
        }
    }
    return constraint;
}

bool constraint_uses_memory_operand(const std::string& constraint) {
    return constraint.find('m') != std::string::npos;
}

bool constraint_is_memory_only(const std::string& constraint) {
    bool has_memory = false;
    bool has_other = false;
    for (char ch : constraint) {
        switch (ch) {
            case 'm': case 'o': case 'V':
                has_memory = true;
                break;
            case '=': case '+': case '&': case '%': case '#': case '*':
            case ' ':
                break;
            default:
                has_other = true;
                break;
        }
    }
    return has_memory && !has_other;
}

std::string strip_memory_alternatives(std::string constraint) {
    std::string out;
    for (char ch : constraint) {
        if (ch != 'm' && ch != 'o' && ch != 'V') {
            out += ch;
        }
    }
    return out;
}

std::string add_llvm_indirect_memory_marker(std::string constraint) {
    size_t m_pos = constraint.find('m');
    if (m_pos != std::string::npos &&
        (m_pos == 0 || constraint[m_pos - 1] != '*')) {
        constraint.insert(m_pos, "*");
    }
    return constraint;
}

std::string strip_output_constraint_prefix(std::string constraint) {
    if (!constraint.empty() && (constraint[0] == '=' || constraint[0] == '+')) {
        constraint.erase(0, 1);
    }
    return constraint;
}

std::string constraint_with_register_binding(const std::string& constraint,
                                             const std::string& reg) {
    std::string prefix;
    size_t pos = 0;
    while (pos < constraint.size() &&
           (constraint[pos] == '=' || constraint[pos] == '+' ||
            constraint[pos] == '&' || constraint[pos] == '%')) {
        prefix += constraint[pos];
        ++pos;
    }
    return prefix + "{" + reg + "}";
}

unsigned asm_operand_bit_width(llvm::Type* type) {
    if (type && type->isIntegerTy()) {
        return type->getIntegerBitWidth();
    }

    return 64;
}

std::string normalize_asm_register_for_target(std::string reg, TargetArch arch,
                                              unsigned operand_bits) {
    if (arch != TargetArch::AARCH64 || reg.size() < 2) {
        return reg;
    }
    if (reg[0] != 'r' && reg[0] != 'x' && reg[0] != 'w') {
        return reg;
    }
    std::string digits = reg.substr(1);
    if (digits.empty() ||
        digits.find_first_not_of("0123456789") != std::string::npos) {
        return reg;
    }
    int number = std::atoi(digits.c_str());
    if (number < 0 || number > 30) {
        return reg;
    }
    if (number == 30) {
        return "lr";
    }
    if (number == 29) {
        return "fp";
    }

    if (reg[0] == 'r') {
        return (operand_bits > 32 ? "x" : "w") + digits;
    }
    return reg;
}

bool template_has_non_whitespace(const std::string& text) {
    return text.find_first_not_of(" \t\r\n") != std::string::npos;
}

cir::ValueRef value_operand_at(const std::vector<cir::Operand>& operands, size_t index) {
    if (index >= operands.size()) {
        return {};
    }
    const auto* value = std::get_if<cir::ValueRef>(&operands[index].data);
    return value ? *value : cir::ValueRef{};
}

cir::EntityId entity_operand_at(const std::vector<cir::Operand>& operands, size_t index) {
    if (index >= operands.size()) {
        return {};
    }
    const auto* entity = std::get_if<cir::EntityId>(&operands[index].data);
    return entity ? *entity : cir::EntityId{};
}

cir::TypeRef type_operand_at(const std::vector<cir::Operand>& operands, size_t index) {
    if (index >= operands.size()) {
        return {};
    }
    const auto* type = std::get_if<cir::TypeRef>(&operands[index].data);
    return type ? *type : cir::TypeRef{};
}

cir::EntityId parameter_argument_object(const cir::File& file,
                                        cir::InstId value) {
    if (!file.valid(value) ||
        file.inst(value).kind != cir::InstKind::LValueToRValue) {
        return {};
    }
    std::vector<cir::Operand> value_operands =
        file.operands(file.inst(value).operands);
    cir::ValueRef place = value_operand_at(value_operands, 0);
    if (!file.valid(place.inst)) {
        return {};
    }
    const cir::Inst& place_inst = file.inst(place.inst);
    if (!place_inst.place_fact.valid()) {
        return {};
    }
    cir::EntityId entity = file.place_fact(place_inst.place_fact).entity;
    return file.valid(entity) && file.entity(entity).is_parameter_argument_object
        ? entity
        : cir::EntityId{};
}

} // namespace

const char* Lowerer::named_register_for_place(cir::ValueRef place) {
    if (!file_.valid(place.inst)) {
        return nullptr;
    }
    const cir::Inst& inst = file_.inst(place.inst);
    if (inst.kind != cir::InstKind::GlobalPlace) {
        return nullptr;
    }
    const std::vector<cir::Operand>& operands = file_.operands(inst.operands);
    cir::EntityId entity_id = entity_operand_at(operands, 0);
    if (!file_.valid(entity_id)) {
        return nullptr;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (!entity.attr_facts.is_named_register) {
        return nullptr;
    }
    return entity.attr_facts.asm_label.c_str();
}

llvm::Value* Lowerer::lower_named_register_read(const char* reg,
                                                llvm::Type* type,
                                                SrcLoc loc) {

    if (!type || !(type->isIntegerTy() || type->isPointerTy())) {
        error("global register variables must have integer or pointer type",
              loc);
        return nullptr;
    }
    llvm::Type* reg_type =
        type->isPointerTy() ? module().getDataLayout().getIntPtrType(type)
                            : type;
    llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
        &module(), llvm::Intrinsic::read_register, {reg_type});
    llvm::Value* reg_md = llvm::MetadataAsValue::get(
        context(),
        llvm::MDNode::get(context(), llvm::MDString::get(context(), reg)));
    llvm::Value* raw = builder().CreateCall(fn, {reg_md}, "named.reg.read");
    if (type->isPointerTy()) {
        return builder().CreateIntToPtr(raw, type, "named.reg.ptr");
    }
    return raw;
}

void Lowerer::lower_named_register_write(const char* reg,
                                         llvm::Value* value,
                                         SrcLoc loc) {
    llvm::Type* type = value->getType();
    if (!(type->isIntegerTy() || type->isPointerTy())) {
        error("global register variables must have integer or pointer type",
              loc);
        return;
    }

    llvm::Value* reg_value = value;
    if (type->isPointerTy()) {
        reg_value = builder().CreatePtrToInt(
            value, module().getDataLayout().getIntPtrType(type),
            "named.reg.int");
    }
    llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
        &module(), llvm::Intrinsic::write_register, {reg_value->getType()});
    llvm::Value* reg_md = llvm::MetadataAsValue::get(
        context(),
        llvm::MDNode::get(context(), llvm::MDString::get(context(), reg)));
    builder().CreateCall(fn, {reg_md, reg_value});
}

void Lowerer::lower_function(cir::FunctionId function_id) {
    const cir::Function& function = file_.function(function_id);
    llvm::Function* llvm_function = get_or_declare_function(function.entity);
    if (!llvm_function) {
        return;
    }
    current_function_ = llvm_function;
    current_abi_ = classify_function_abi(function.type);
    has_current_abi_ = true;
    current_sret_pointer_ = nullptr;
    current_result_object_pointer_ = nullptr;
    inst_values_.clear();
    local_places_.clear();
    block_values_.clear();
    address_taken_blocks_.clear();
    landingpad_values_.clear();
    current_cir_block_ = {};
    if (function_uses_eh(function)) {
        bool non_throwing = false;
        if (const auto* fn_payload = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(file_.resolved_type(function.type)))) {
            non_throwing = fn_payload->exception_spec.kind ==
                           cir::FunctionExceptionSpecKind::NonThrowing;
        }
        apply_eh_function_setup(llvm_function, non_throwing);
    }

    for (cir::BlockId block_id : function.blocks) {
        const cir::Block& block = file_.block(block_id);
        std::string block_name = block.name.valid()
            ? file_.name(block.name)
            : "block" + std::to_string(block_id.index);

        auto pre = label_address_blocks_.find(id_key(block_id));
        if (pre != label_address_blocks_.end() &&
            pre->second->getParent() == llvm_function) {
            pre->second->setName(block_name);
            block_values_[id_key(block_id)] = pre->second;
        } else {
            block_values_[id_key(block_id)] =
                llvm::BasicBlock::Create(context(), block_name, llvm_function);
        }
    }

    if (function.entry_block.valid()) {
        llvm::BasicBlock* entry_bb = block_values_[id_key(function.entry_block)];
        if (entry_bb && entry_bb != &llvm_function->front()) {
            entry_bb->moveBefore(&llvm_function->front());
        }
    }

    {
        auto add_target = [&](cir::BlockId block_id) {
            auto found = block_values_.find(id_key(block_id));
            if (found == block_values_.end()) {
                return;
            }
            if (std::find(address_taken_blocks_.begin(), address_taken_blocks_.end(),
                          found->second) == address_taken_blocks_.end()) {
                address_taken_blocks_.push_back(found->second);
            }
        };
        for (cir::BlockId block_id : function.blocks) {
            for (cir::InstId inst_id : file_.block(block_id).instructions) {
                const cir::Inst& inst = file_.inst(inst_id);
                if (inst.kind != cir::InstKind::LabelAddress) {
                    continue;
                }
                if (const auto* label = std::get_if<cir::LabelAddressPayload>(
                        &file_.payload(inst.payload_index));
                    label && label->target.valid()) {
                    add_target(label->target);
                }
            }
        }
        for (cir::EntityId entity_id : file_.entity_ids()) {
            const cir::Entity& entity = file_.entity(entity_id);
            if (entity.kind != cir::EntityKind::Variable) {
                continue;
            }
            for (const cir::StaticInitializerRelocation& reloc :
                 entity.static_initializer_relocations) {
                if (reloc.block.valid()) {
                    add_target(reloc.block);
                }
            }
        }
    }

    for (cir::BlockId block_id : function.blocks) {
        const cir::Block& block = file_.block(block_id);
        builder().SetInsertPoint(block_values_[id_key(block_id)]);
        for (cir::InstId param_id : block.parameters) {
            if (inst_values_.contains(id_key(param_id))) {
                continue;
            }
            const cir::Inst& param = file_.inst(param_id);
            std::string name = "block_param";
            std::vector<cir::Operand> operands = file_.operands(param.operands);
            if (!operands.empty()) {
                const auto* entity = std::get_if<cir::EntityId>(&operands[0].data);
                if (entity && file_.valid(*entity)) {
                    const cir::Entity& entity_record = file_.entity(*entity);
                    if (entity_record.name.valid()) {
                        name = file_.name(entity_record.name);
                    }
                }
            }
            llvm::PHINode* phi =
                builder().CreatePHI(llvm_type(param.result_type), 0, name);
            inst_values_[id_key(param_id)] = phi;
        }
    }

    if (!function.blocks.empty()) {
        builder().SetInsertPoint(block_values_[id_key(function.blocks.front())]);
    }

    auto arg_it = llvm_function->arg_begin();
    if (current_abi_.result.kind == AbiArgKind::Indirect) {
        if (arg_it == llvm_function->arg_end()) {
            error("LLVM function has too few parameters for indirect result", function.loc);
            return;
        }
        arg_it->setName("sret");
        current_sret_pointer_ = &*arg_it;
        ++arg_it;
    }
    for (size_t param_index = 0; param_index < function.parameters.size(); ++param_index) {
        const cir::FunctionParameter& parameter = function.parameters[param_index];
        const AbiArgInfo* param_abi = param_index < current_abi_.params.size()
            ? &current_abi_.params[param_index]
            : nullptr;
        if (param_abi && param_abi->is_ignored) {
            inst_values_[id_key(parameter.value.inst)] =
                llvm::Constant::getNullValue(
                    llvm_type(file_.inst(parameter.value.inst).result_type));
            continue;
        }
        if (arg_it == llvm_function->arg_end()) {
            error("LLVM function has too few parameters", function.loc);
            return;
        }
        if (file_.valid(parameter.entity)) {
            const cir::Entity& param_entity = file_.entity(parameter.entity);
            if (param_entity.name.valid()) {
                arg_it->setName(file_.name(param_entity.name));
            }
        }
        llvm::Value* source_value = &*arg_it;
        if (param_abi) {
            if (param_abi->kind == AbiArgKind::Indirect) {
                cir::TypeId parameter_type = file_.resolved_type(
                    file_.entity(parameter.entity).type);
                const cir::RecordFacts* record =
                    file_.record_facts_for_type(parameter_type);
                if (record && record->is_non_trivial_for_calls) {
                    local_places_[id_key(parameter.entity)] = &*arg_it;
                }
                source_value = materialize_indirect_abi_value_to_source(
                    source_value,
                    param_abi->source_type,
                    function.loc,
                    "abi.param.load");
            } else if (param_abi->is_direct_aggregate) {
                source_value = materialize_abi_value_to_source(source_value,
                                                               param_abi->source_type,
                                                               function.loc,
                                                               "abi.param");
            } else {
                source_value = cast_value(source_value,
                                          llvm_type(file_.inst(parameter.value.inst).result_type),
                                          function.loc,
                                          "param.cast");
            }
        }
        if (!source_value) {
            return;
        }
        inst_values_[id_key(parameter.value.inst)] = source_value;
        ++arg_it;
    }

    for (cir::BlockId block_id : function.blocks) {
        for (cir::InstId inst_id : file_.block(block_id).instructions) {
            const cir::Inst& inst = file_.inst(inst_id);
            if (inst.kind != cir::InstKind::EhAllocException) {
                continue;
            }
            builder().SetInsertPoint(block_values_[id_key(block_id)]);
            remember(inst_id, lower_eh_alloc_exception(inst));
            if (has_errors()) {
                return;
            }
        }
    }

    for (cir::BlockId block_id : function.blocks) {
        for (cir::InstId inst_id : file_.block(block_id).instructions) {
            const cir::Inst& inst = file_.inst(inst_id);
            if (inst.kind != cir::InstKind::LocalPlace) {
                continue;
            }
            std::vector<cir::Operand> operands = file_.operands(inst.operands);
            cir::EntityId entity_id = entity_operand_at(operands, 0);
            if (!file_.valid(entity_id) ||
                file_.entity(entity_id).object_storage_alias_place.valid()) {
                continue;
            }
            builder().SetInsertPoint(block_values_[id_key(block_id)]);
            remember(inst_id, storage_for_entity(entity_id, inst.loc));
            if (has_errors()) {
                return;
            }
        }
    }

    for (cir::BlockId block_id : function.blocks) {
        builder().SetInsertPoint(block_values_[id_key(block_id)]);
        const cir::Block& block = file_.block(block_id);
        current_cir_block_ = block_id;
        for (cir::InstId inst_id : block.instructions) {
            if (file_.inst(inst_id).kind == cir::InstKind::Param) {
                continue;
            }
            lower_inst(inst_id);
            if (has_errors()) {
                return;
            }
        }
        lower_terminator(block.terminator);
        if (has_errors()) {
            return;
        }
    }
    current_function_ = nullptr;
    has_current_abi_ = false;
    current_sret_pointer_ = nullptr;
    current_result_object_pointer_ = nullptr;
    current_cir_block_ = {};
}

llvm::AllocaInst* Lowerer::create_entry_alloca(llvm::Type* type, std::string_view name) {
    llvm::BasicBlock& entry_block = current_function_->getEntryBlock();
    llvm::IRBuilder<> entry_builder(&entry_block, entry_block.getFirstInsertionPt());
    return entry_builder.CreateAlloca(type, nullptr, llvm::StringRef(name.data(), name.size()));
}

llvm::Value* Lowerer::value_for(cir::ValueRef value, SrcLoc loc) {
    return value_for(value.inst, loc);
}

llvm::Value* Lowerer::value_for(cir::InstId inst_id, SrcLoc loc) {
    auto found = inst_values_.find(id_key(inst_id));
    if (found == inst_values_.end()) {
        error("missing lowered value for " + file_.format_inst(inst_id), loc);
        return nullptr;
    }
    return found->second;
}

llvm::Value* Lowerer::storage_for_place(cir::InstId place_id, SrcLoc loc) {
    if (!place_id.valid() || !file_.valid(place_id)) {
        return nullptr;
    }
    auto lowered = inst_values_.find(id_key(place_id));
    if (lowered != inst_values_.end()) {
        return lowered->second;
    }
    const cir::Inst& place = file_.inst(place_id);
    std::vector<cir::Operand> operands = file_.operands(place.operands);
    std::vector<cir::ValueRef> values = file_.value_operands(place.operands);
    auto entity_at = [&](size_t index) -> cir::EntityId {
        if (index < operands.size()) {
            if (const auto* entity =
                    std::get_if<cir::EntityId>(&operands[index].data)) {
                return *entity;
            }
        }
        return {};
    };
    switch (place.kind) {
        case cir::InstKind::LocalPlace:
        case cir::InstKind::GlobalPlace: {
            cir::EntityId entity = entity_at(0);
            return entity.valid() ? storage_for_entity(entity, loc) : nullptr;
        }
        case cir::InstKind::Deref:
        case cir::InstKind::AddrOf:
            return values.empty() ? nullptr
                                  : storage_for_place(values[0].inst, loc);
        case cir::InstKind::FieldAddr: {
            if (values.empty()) {
                return nullptr;
            }
            llvm::Value* base = storage_for_place(values[0].inst, loc);
            const cir::RecordFieldFact* field = file_.field_fact(entity_at(1));
            if (!base || !field) {
                return nullptr;
            }
            llvm::Value* offset = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(context()), field->offset);
            return builder().CreateInBoundsGEP(
                llvm::Type::getInt8Ty(context()), base, offset,
                "result.field");
        }
        case cir::InstKind::ArrayElementPlace: {
            if (values.size() != 2 || !file_.valid(values[1].inst)) {
                return nullptr;
            }
            const cir::Inst& index_inst = file_.inst(values[1].inst);
            const auto* literal = index_inst.kind == cir::InstKind::IntegerLiteral
                ? std::get_if<cir::LiteralPayload>(
                      &file_.payload(index_inst.payload_index))
                : nullptr;
            const cir::IntegerValue* index_value = literal
                ? std::get_if<cir::IntegerValue>(&literal->value)
                : nullptr;
            std::optional<int64_t> index = index_value
                ? index_value->try_as_int64()
                : std::nullopt;
            std::optional<size_t> element_size = cir::size_of_type(
                file_, file_.place_object_type(place.result_type));
            llvm::Value* base = storage_for_place(values[0].inst, loc);
            if (!base || !index.has_value() || !element_size.has_value()) {
                return nullptr;
            }
            llvm::Value* offset = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(context()),
                *index * static_cast<int64_t>(*element_size));
            return builder().CreateInBoundsGEP(
                llvm::Type::getInt8Ty(context()), base, offset,
                "result.element");
        }
        default:
            return nullptr;
    }
}

llvm::Value* Lowerer::storage_for_entity(cir::EntityId entity_id,
                                         SrcLoc loc) {
    if (!entity_id.valid() || !file_.valid(entity_id)) {
        error("invalid result-object entity", loc);
        return nullptr;
    }
    auto found = local_places_.find(id_key(entity_id));
    if (found != local_places_.end()) {
        return found->second;
    }
    const cir::Entity& entity = file_.entity(entity_id);
    if (entity.object_storage_alias.valid()) {
        llvm::Value* aliased =
            storage_for_entity(entity.object_storage_alias, loc);
        if (aliased) {
            local_places_[id_key(entity_id)] = aliased;
        }
        return aliased;
    }
    if (entity.object_storage_alias_place.valid() &&
        file_.valid(entity.object_storage_alias_place)) {
        const cir::Inst& place =
            file_.inst(entity.object_storage_alias_place);
        if (place.kind == cir::InstKind::LocalPlace ||
            place.kind == cir::InstKind::GlobalPlace) {
            std::vector<cir::Operand> operands = file_.operands(place.operands);
            if (!operands.empty()) {
                if (const auto* target =
                        std::get_if<cir::EntityId>(&operands.front().data)) {
                    llvm::Value* aliased = storage_for_entity(*target, loc);
                    if (aliased) {
                        local_places_[id_key(entity_id)] = aliased;
                    }
                    return aliased;
                }
            }
        }
        llvm::Value* aliased =
            storage_for_place(entity.object_storage_alias_place, loc);

        return aliased;
    }
    if (entity.is_function_result_object) {
        if (!current_result_object_pointer_) {
            if (current_sret_pointer_) {
                current_result_object_pointer_ = current_sret_pointer_;
            } else {
                current_result_object_pointer_ = create_entry_alloca(
                    llvm_type(entity.type), "result.object");
            }
        }
        local_places_[id_key(entity_id)] = current_result_object_pointer_;
        return current_result_object_pointer_;
    }
    if (entity.storage_duration == cir::StorageDuration::Static ||
        entity.storage_duration == cir::StorageDuration::Thread) {
        return get_or_create_global(entity_id);
    }

    llvm::AllocaInst* alloca = create_entry_alloca(
        llvm_type(entity.type),
        entity.name.valid() ? file_.name(entity.name) : "local");
    size_t alignment = entity.attr_facts.requested_alignment;
    if (auto size_align = cir::size_align_of_type(file_, entity.type)) {
        alignment = std::max(alignment, size_align->alignment_bytes);
    }
    alloca->setAlignment(llvm::Align(std::max<size_t>(1, alignment)));
    local_places_[id_key(entity_id)] = alloca;
    return alloca;
}

void Lowerer::remember(cir::InstId inst_id, llvm::Value* value) {
    if (value) {
        inst_values_[id_key(inst_id)] = value;
    }
}

void Lowerer::lower_inst(cir::InstId inst_id) {
    const cir::Inst& inst = file_.inst(inst_id);
    const cir::InstPayload& payload = file_.payload(inst.payload_index);
    std::vector<cir::Operand> operands = file_.operands(inst.operands);
    std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);

    switch (inst.kind) {
        case cir::InstKind::ReflectValue:
            error("'std::meta::info' values exist only during constant "
                  "evaluation and cannot be lowered to runtime code",
                  inst.loc);
            return;
        case cir::InstKind::CoroBegin:
        case cir::InstKind::CoroFrameSize:
        case cir::InstKind::CoroFrameAlign:
        case cir::InstKind::CoroPromisePlace:
        case cir::InstKind::CoroSave:
        case cir::InstKind::CoroTransfer:
            error("pre-split coroutine CIR reached the LLVM backend; the "
                  "coroutine split pass must run first",
                  inst.loc);
            return;
        case cir::InstKind::ObjCMessageSend:
        case cir::InstKind::ObjCIvarAddr:
        case cir::InstKind::ObjCSelectorLiteral:
        case cir::InstKind::ObjCStringLiteral:
        case cir::InstKind::ObjCArcOp:
            error("Objective-C CIR reached the LLVM backend; the Objective-C "
                  "lowering pass must expand it first",
                  inst.loc);
            return;
        case cir::InstKind::IntegerLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* value = literal
                ? std::get_if<cir::IntegerValue>(&literal->value)
                : nullptr;
            llvm::Type* type = llvm_type(inst.result_type);
            if (type->isPointerTy()) {
                uint64_t raw = value ? value->low_bits : 0;
                if (raw == 0 && (!value || value->high_bits == 0)) {
                    remember(inst_id, llvm::ConstantPointerNull::get(
                                          llvm::cast<llvm::PointerType>(type)));
                } else {
                    auto* intptr_type =
                        llvm::IntegerType::get(context(),
                                               static_cast<unsigned>(pointer_bits()));
                    remember(inst_id,
                             llvm::ConstantExpr::getIntToPtr(
                                 llvm::ConstantInt::get(intptr_type, raw, false),
                                 type));
                }
                return;
            }
            if (!type->isIntegerTy()) {
                error("integer literal has a non-integer LLVM type", inst.loc);
                return;
            }
            unsigned target_width = type->getIntegerBitWidth();
            uint64_t words[2] = {
                value ? value->low_bits : 0,
                value ? value->high_bits : 0,
            };
            unsigned source_width = value ? value->bit_width : target_width;
            llvm::APInt bits(source_width,
                             llvm::ArrayRef<uint64_t>(
                                 words, source_width > 64 ? 2 : 1));
            remember(inst_id,
                     llvm::ConstantInt::get(context(),
                                            bits.zextOrTrunc(target_width)));
            return;
        }
        case cir::InstKind::BooleanLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* value = literal ? std::get_if<bool>(&literal->value) : nullptr;
            remember(inst_id, llvm::ConstantInt::get(llvm_type(inst.result_type),
                                                     value && *value));
            return;
        }
        case cir::InstKind::NullptrLiteral: {
            if (!is_nullptr_type(inst.result_type)) {
                error("nullptr literal result type must be nullptr_t", inst.loc);
                return;
            }
            remember(inst_id, llvm_nullptr_carrier_value());
            return;
        }
        case cir::InstKind::FloatingLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* value = literal
                ? std::get_if<cir::FloatingValue>(&literal->value)
                : nullptr;
            std::optional<llvm::APFloat> exact =
                value ? exact_apfloat(*value) : std::nullopt;
            if (!exact) {
                error("floating literal payload is invalid", inst.loc);
                return;
            }
            remember(inst_id,
                     llvm::ConstantFP::get(llvm_type(inst.result_type), *exact));
            return;
        }
        case cir::InstKind::CharacterLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* bytes = literal ? std::get_if<cir::LiteralByteArray>(&literal->value) : nullptr;
            remember(inst_id, llvm::ConstantInt::get(llvm_type(inst.result_type),
                                                     bytes ? integer_from_bytes(*bytes) : 0,
                                                     false));
            return;
        }
        case cir::InstKind::StringLiteral: {
            const auto* literal = std::get_if<cir::LiteralPayload>(&payload);
            const auto* bytes = literal ? std::get_if<cir::LiteralByteArray>(&literal->value) : nullptr;

            cir::TypeId object_type_id =
                file_.place_object_type(inst.result_type);
            size_t element_width = 1;
            if (const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(file_.resolved_type(object_type_id)))) {
                if (auto sa =
                        cir::size_align_of_type(file_, array->element_type.type)) {
                    element_width = std::max<size_t>(1, sa->size_bytes);
                }
            }
            if (element_width <= 1) {
                std::string text;
                if (bytes) {
                    text.assign(reinterpret_cast<const char*>(bytes->data()),
                                bytes->size());
                }
                llvm::Value* ptr = builder().CreateGlobalString(
                    llvm::StringRef(text.data(), text.size()), ".str", 0, &module());
                remember(inst_id, ptr);
                return;
            }
            std::vector<uint8_t> data;
            if (auto object_size =
                    cir::size_align_of_type(file_, object_type_id)) {
                data.assign(object_size->size_bytes, 0);
            } else if (bytes) {
                data.assign(bytes->size() + element_width, 0);
            }
            if (bytes && !data.empty()) {
                std::copy(bytes->begin(),
                          bytes->begin() + static_cast<std::ptrdiff_t>(
                                               std::min(bytes->size(), data.size())),
                          data.begin());
            }
            llvm::Constant* init = llvm::ConstantDataArray::get(
                context(), llvm::ArrayRef<uint8_t>(data));
            auto* global = new llvm::GlobalVariable(
                module(), init->getType(), /*isConstant=*/true,
                llvm::GlobalValue::PrivateLinkage, init, ".wstr");
            global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
            remember(inst_id, global);
            return;
        }
        case cir::InstKind::LocalPlace: {
            cir::EntityId entity_id = entity_operand_at(operands, 0);
            remember(inst_id, storage_for_entity(entity_id, inst.loc));
            return;
        }
        case cir::InstKind::GlobalPlace: {
            cir::EntityId entity_id = entity_operand_at(operands, 0);
            if (file_.valid(entity_id) &&
                file_.entity(entity_id).attr_facts.is_named_register) {

                return;
            }
            remember(inst_id, get_or_create_global(entity_id));
            return;
        }
        case cir::InstKind::Load:
        case cir::InstKind::LValueToRValue: {
            if (file_.valid(values[0].inst) &&
                file_.inst(values[0].inst).kind == cir::InstKind::VectorElementPlace) {
                remember(inst_id, lower_vector_element_load(values[0].inst, inst.loc));
                return;
            }
            if (const cir::RecordFieldFact* field = field_fact_for_place(values[0].inst);
                field && field->is_bitfield) {
                remember(inst_id, lower_bitfield_load(values[0].inst, *field, inst.loc));
                return;
            }
            if (const char* reg = named_register_for_place(values[0])) {
                remember(inst_id, lower_named_register_read(
                                      reg, llvm_type(inst.result_type), inst.loc));
                return;
            }
            llvm::Value* place = value_for(values[0], inst.loc);
            if (!place) {
                return;
            }
            llvm::LoadInst* load = builder().CreateLoad(
                llvm_type(inst.result_type), place,
                inst.kind == cir::InstKind::Load ? "load" : "lvalue");
            if (place_access_is_volatile(values[0].inst)) {
                load->setVolatile(true);
            }
            remember(inst_id, load);
            return;
        }
        case cir::InstKind::FunctionToPointer:
            remember(inst_id, function_symbol(entity_operand_at(operands, 0)));
            return;
        case cir::InstKind::MemberPointerValue: {
            cir::EntityId entity = entity_operand_at(operands, 0);
            const cir::RecordFieldFact* field = file_.field_fact(entity);
            if (!field) {
                const cir::RecordMethodFact* method = file_.method_fact(entity);
                if (!method || method->is_static) {
                    error("member_pointer_value requires a field or non-static method",
                          inst.loc);
                    return;
                }
                llvm::StructType* type = llvm::dyn_cast<llvm::StructType>(
                    llvm_type(inst.result_type));
                if (!type || type != llvm_member_function_pointer_type()) {
                    error("member function pointer value requires pair ABI storage",
                          inst.loc);
                    return;
                }
                llvm::Constant* function = nullptr;
                if (method->is_virtual) {
                    if (method->vtable_slot < 0) {
                        error("virtual member function pointer value is missing a vtable slot",
                              inst.loc);
                        return;
                    }
                    llvm::IntegerType* intptr_type = llvm::IntegerType::get(
                        context(), static_cast<unsigned>(pointer_bits()));
                    uint64_t encoded_slot =
                        1 + pointer_bytes() *
                                static_cast<uint64_t>(method->vtable_slot);
                    function = llvm::ConstantExpr::getIntToPtr(
                        llvm::ConstantInt::get(intptr_type, encoded_slot),
                        llvm::PointerType::get(context(), 0));
                } else {
                    function = function_symbol(entity);
                    if (!function) {
                        return;
                    }
                }
                remember(inst_id,
                         llvm::ConstantStruct::get(
                             type,
                             {function,
                              llvm::ConstantInt::get(
                                  llvm::IntegerType::get(
                                      context(),
                                      static_cast<unsigned>(pointer_bits())),
                                  0,
                                  true)}));
                return;
            }
            if (field->is_bitfield) {
                error("bit-field member pointer values cannot be lowered", inst.loc);
                return;
            }
            llvm::Type* type = llvm_type(inst.result_type);
            if (!type || !type->isIntegerTy()) {
                error("data member pointer value requires integer ABI storage",
                      inst.loc);
                return;
            }
            size_t byte_offset = field->offset;
            const cir::Entity& member_entity = file_.entity(entity);
            if (member_entity.declaring_record.valid() &&
                member_entity.declaring_record != member_entity.parent) {
                if (const cir::RecordFacts* owner =
                        file_.record_facts(member_entity.declaring_record)) {
                    for (const cir::VariantMemberFact& variant :
                         owner->variant_members) {
                        if (variant.member != entity) {
                            continue;
                        }
                        byte_offset = 0;
                        for (cir::EntityId step : variant.path) {
                            if (const cir::RecordFieldFact* path_field =
                                    file_.field_fact(step)) {
                                byte_offset += path_field->offset;
                            }
                        }
                        break;
                    }
                }
            }
            remember(inst_id,
                     llvm::ConstantInt::get(type,
                                            static_cast<uint64_t>(byte_offset),
                                            true));
            return;
        }
        case cir::InstKind::LabelAddress: {
            const auto* label = std::get_if<cir::LabelAddressPayload>(&payload);
            if (!label || !current_function_ || !file_.valid(label->target)) {
                error("label_address instruction is missing label metadata", inst.loc);
                return;
            }
            auto found = block_values_.find(id_key(label->target));
            if (found == block_values_.end()) {
                error("label_address target block was not lowered", inst.loc);
                return;
            }
            llvm::Constant* address =
                llvm::BlockAddress::get(current_function_, found->second);
            remember(inst_id,
                     llvm::ConstantExpr::getBitCast(address, llvm_type(inst.result_type)));
            return;
        }
        case cir::InstKind::Store: {
            if (inst.runtime_elided_object_operation) {
                return;
            }
            llvm::Value* value = value_for(values[1], inst.loc);
            if (file_.valid(values[0].inst) &&
                file_.inst(values[0].inst).kind == cir::InstKind::VectorElementPlace) {
                if (value) {
                    lower_vector_element_store(values[0].inst, value, inst.loc);
                }
                return;
            }
            if (const char* reg = named_register_for_place(values[0])) {
                if (value) {
                    lower_named_register_write(reg, value, inst.loc);
                }
                return;
            }
            llvm::Value* place = value_for(values[0], inst.loc);
            if (const cir::RecordFieldFact* field = field_fact_for_place(values[0].inst);
                field && field->is_bitfield) {
                if (place && value) {
                    lower_bitfield_store(values[0].inst, value, *field, inst.loc);
                }
                return;
            }
            cir::TypeId object_type_id =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            llvm::Type* object_type = llvm_type(object_type_id);
            cir::TypeId source_type = values.size() > 1 && file_.valid(values[1].inst)
                ? file_.inst(values[1].inst).result_type
                : cir::TypeId{};
            value = cast_value(value, source_type, object_type_id, inst.loc, "store.cast");
            if (place && value) {
                llvm::StoreInst* store = builder().CreateStore(value, place);
                if (place_access_is_volatile(values[0].inst)) {
                    store->setVolatile(true);
                }
            }
            return;
        }
        case cir::InstKind::ZeroObject: {
            llvm::Value* place = value_for(values[0], inst.loc);
            if (!place) {
                return;
            }
            cir::TypeId place_type = file_.inst(values[0].inst).result_type;
            cir::TypeId object_type_id = file_.place_object_type(place_type);
            auto size_align = cir::size_align_of_type(file_, object_type_id);
            if (!size_align) {
                error("zero_object requires a complete object type", inst.loc);
                return;
            }
            llvm::Value* zero = llvm::ConstantInt::get(llvm::Type::getInt8Ty(context()), 0);
            builder().CreateMemSet(place,
                                   zero,
                                   static_cast<uint64_t>(size_align->size_bytes),
                                   llvm::MaybeAlign(std::max<size_t>(
                                       1,
                                       size_align->alignment_bytes)));
            return;
        }
        case cir::InstKind::AddrOf:
        case cir::InstKind::Deref:
            remember(inst_id, value_for(values[0], inst.loc));
            return;
        case cir::InstKind::ArrayElementPlace:
            remember(inst_id, lower_array_element_place(inst, values));
            return;
        case cir::InstKind::StackAlloc: {
            llvm::Value* total_bytes = value_for(values[0], inst.loc);
            if (!total_bytes) {
                remember(inst_id, nullptr);
                return;
            }
            llvm::AllocaInst* storage = builder().CreateAlloca(
                llvm::Type::getInt8Ty(context()), total_bytes, "vla");
            storage->setAlignment(llvm::Align(16));
            remember(inst_id, storage);
            return;
        }
        case cir::InstKind::StackSave: {
            llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
                &module(), llvm::Intrinsic::stacksave,
                {llvm::PointerType::get(context(), 0)});
            remember(inst_id, builder().CreateCall(fn, {}, "stacksave"));
            return;
        }
        case cir::InstKind::LifetimeStart:
        case cir::InstKind::LifetimeEnd: {
            remember(inst_id, nullptr);
            if (values.empty()) {
                return;
            }
            llvm::Value* place = value_for(values[0], inst.loc);
            auto* storage = place
                ? llvm::dyn_cast<llvm::AllocaInst>(place->stripPointerCasts())
                : nullptr;

            if (!storage || !storage->isStaticAlloca()) {
                return;
            }

            std::optional<llvm::TypeSize> size =
                storage->getAllocationSize(module().getDataLayout());
            if (!size || size->isScalable()) {
                return;
            }
            if (inst.kind == cir::InstKind::LifetimeStart) {
                builder().CreateLifetimeStart(storage);
            } else {
                builder().CreateLifetimeEnd(storage);
            }
            return;
        }
        case cir::InstKind::StackRestore: {
            llvm::Value* saved = value_for(values[0], inst.loc);
            if (saved) {
                llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
                    &module(), llvm::Intrinsic::stackrestore,
                    {llvm::PointerType::get(context(), 0)});
                builder().CreateCall(fn, {saved});
            }
            remember(inst_id, nullptr);
            return;
        }
        case cir::InstKind::AtomicLoad: {
            const auto* payload =
                std::get_if<cir::AtomicPayload>(&file_.payload(inst.payload_index));
            llvm::Value* place = value_for(values[0], inst.loc);
            if (!place || !payload) {
                return;
            }

            llvm::Type* value_type = llvm_type(inst.result_type);
            bool is_bool = value_type->isIntegerTy(1);
            llvm::Type* memory_type =
                is_bool ? llvm::Type::getInt8Ty(context()) : value_type;
            llvm::LoadInst* load =
                builder().CreateLoad(memory_type, place, "atomic.load");
            load->setAlignment(atomic_alignment(inst.result_type));
            load->setAtomic(atomic_ordering(payload->order,
                                            /*is_store=*/false,
                                            /*is_load=*/true));
            llvm::Value* result = load;
            if (is_bool) {
                result = builder().CreateTrunc(result, value_type, "atomic.load.bool");
            }
            remember(inst_id, result);
            return;
        }
        case cir::InstKind::AtomicStore: {
            const auto* payload =
                std::get_if<cir::AtomicPayload>(&file_.payload(inst.payload_index));
            llvm::Value* place = value_for(values[0], inst.loc);
            llvm::Value* value = value_for(values[1], inst.loc);
            if (!place || !value || !payload) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            value = cast_value(value,
                               file_.inst(values[1].inst).result_type,
                               object_type,
                               inst.loc,
                               "atomic.store.cast");
            if (value->getType()->isIntegerTy(1)) {
                value = builder().CreateZExt(value,
                                             llvm::Type::getInt8Ty(context()),
                                             "atomic.store.bool");
            }
            llvm::StoreInst* store = builder().CreateStore(value, place);
            store->setAlignment(atomic_alignment(object_type));
            store->setAtomic(atomic_ordering(payload->order,
                                             /*is_store=*/true,
                                             /*is_load=*/false));
            remember(inst_id, nullptr);
            return;
        }
        case cir::InstKind::AtomicRmw: {
            const auto* payload =
                std::get_if<cir::AtomicPayload>(&file_.payload(inst.payload_index));
            llvm::Value* place = value_for(values[0], inst.loc);
            llvm::Value* value = value_for(values[1], inst.loc);
            if (!place || !value || !payload) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            llvm::AtomicRMWInst::BinOp op = llvm::AtomicRMWInst::Xchg;
            switch (payload->rmw_op) {
                case cir::AtomicRmwOp::Xchg: op = llvm::AtomicRMWInst::Xchg; break;
                case cir::AtomicRmwOp::Add: op = llvm::AtomicRMWInst::Add; break;
                case cir::AtomicRmwOp::Sub: op = llvm::AtomicRMWInst::Sub; break;
                case cir::AtomicRmwOp::And: op = llvm::AtomicRMWInst::And; break;
                case cir::AtomicRmwOp::Or: op = llvm::AtomicRMWInst::Or; break;
                case cir::AtomicRmwOp::Xor: op = llvm::AtomicRMWInst::Xor; break;
                case cir::AtomicRmwOp::Nand: op = llvm::AtomicRMWInst::Nand; break;
            }
            cir::TypeId resolved_object = file_.resolved_type(object_type);
            bool pointer_arithmetic =
                file_.valid(resolved_object) &&
                file_.type(resolved_object).kind == cir::TypeKind::Pointer &&
                (payload->rmw_op == cir::AtomicRmwOp::Add ||
                 payload->rmw_op == cir::AtomicRmwOp::Sub);
            if (pointer_arithmetic) {
                value = cast_value(
                    value,
                    llvm::IntegerType::get(
                        context(), static_cast<unsigned>(pointer_bits())),
                    inst.loc,
                    "atomic.rmw.pointer.delta");
            } else {
                value = cast_value(value,
                                   file_.inst(values[1].inst).result_type,
                                   object_type,
                                   inst.loc,
                                   "atomic.rmw.cast");
            }
            if (!value) {
                return;
            }
            bool rmw_bool = value->getType()->isIntegerTy(1);
            if (rmw_bool) {
                value = builder().CreateZExt(value,
                                             llvm::Type::getInt8Ty(context()),
                                             "atomic.rmw.bool");
            }
            llvm::Value* rmw_result =
                builder().CreateAtomicRMW(op,
                                          place,
                                          value,
                                          atomic_alignment(object_type),
                                          atomic_ordering(payload->order,
                                                          false,
                                                          false));
            if (rmw_bool) {
                rmw_result = builder().CreateTrunc(rmw_result,
                                                   llvm::Type::getInt1Ty(context()),
                                                   "atomic.rmw.old");
            } else if (pointer_arithmetic) {
                rmw_result = builder().CreateIntToPtr(
                    rmw_result,
                    llvm_type(object_type),
                    "atomic.rmw.pointer.old");
            }
            remember(inst_id, rmw_result);
            return;
        }
        case cir::InstKind::AtomicCmpXchg: {
            const auto* payload =
                std::get_if<cir::AtomicPayload>(&file_.payload(inst.payload_index));
            llvm::Value* place = value_for(values[0], inst.loc);
            llvm::Value* expected_place = value_for(values[1], inst.loc);
            llvm::Value* desired = value_for(values[2], inst.loc);
            if (!place || !expected_place || !desired || !payload) {
                return;
            }
            cir::TypeId object_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            llvm::Type* value_type = llvm_type(object_type);
            desired = cast_value(desired,
                                 file_.inst(values[2].inst).result_type,
                                 object_type,
                                 inst.loc,
                                 "atomic.cmpxchg.cast");
            bool cas_bool = value_type->isIntegerTy(1);
            llvm::Type* memory_type =
                cas_bool ? llvm::Type::getInt8Ty(context()) : value_type;
            if (cas_bool && desired) {
                desired = builder().CreateZExt(desired, memory_type, "cmpxchg.bool");
            }
            llvm::Align align = atomic_alignment(object_type);
            llvm::LoadInst* expected =
                builder().CreateLoad(memory_type, expected_place, "cmpxchg.expected");
            llvm::AtomicOrdering failure_order =
                atomic_ordering(payload->failure_order, false, true);
            if (failure_order == llvm::AtomicOrdering::Release ||
                failure_order == llvm::AtomicOrdering::AcquireRelease) {
                failure_order = llvm::AtomicOrdering::SequentiallyConsistent;
            }
            llvm::AtomicCmpXchgInst* cmpxchg = builder().CreateAtomicCmpXchg(
                place,
                expected,
                desired,
                align,
                atomic_ordering(payload->order, false, false),
                failure_order);
            cmpxchg->setWeak(payload->is_weak);
            llvm::Value* old_value =
                builder().CreateExtractValue(cmpxchg, 0, "cmpxchg.old");
            llvm::Value* success =
                builder().CreateExtractValue(cmpxchg, 1, "cmpxchg.ok");
            builder().CreateStore(old_value, expected_place);
            remember(inst_id, success);
            return;
        }
        case cir::InstKind::AtomicFence: {
            const auto* payload =
                std::get_if<cir::AtomicPayload>(&file_.payload(inst.payload_index));
            if (payload) {
                builder().CreateFence(atomic_ordering(payload->order, false, false));
            }
            remember(inst_id, nullptr);
            return;
        }
        case cir::InstKind::ComplexMake: {
            llvm::Value* real = value_for(values[0], inst.loc);
            llvm::Value* imag = value_for(values[1], inst.loc);
            llvm::Type* complex_type = llvm_type(inst.result_type);
            if (!real || !imag || !complex_type) {
                return;
            }
            llvm::Type* element_type = complex_type->getArrayElementType();
            real = cast_value(real, element_type, inst.loc, "complex.re");
            imag = cast_value(imag, element_type, inst.loc, "complex.im");
            llvm::Value* value = llvm::UndefValue::get(complex_type);
            value = builder().CreateInsertValue(value, real, {0});
            value = builder().CreateInsertValue(value, imag, {1}, "complex.make");
            remember(inst_id, value);
            return;
        }
        case cir::InstKind::ComplexReal:
        case cir::InstKind::ComplexImag: {
            llvm::Value* operand = value_for(values[0], inst.loc);
            if (!operand) {
                return;
            }
            unsigned index = inst.kind == cir::InstKind::ComplexImag ? 1 : 0;
            remember(inst_id,
                     builder().CreateExtractValue(operand, {index}, "complex.elem"));
            return;
        }
        case cir::InstKind::ComplexRealPlace:
        case cir::InstKind::ComplexImagPlace: {
            llvm::Value* place = value_for(values[0], inst.loc);
            if (!place) {
                return;
            }
            cir::TypeId base_type =
                file_.place_object_type(file_.inst(values[0].inst).result_type);
            llvm::Type* complex_type = llvm_type(base_type);
            unsigned index = inst.kind == cir::InstKind::ComplexImagPlace ? 1 : 0;
            remember(inst_id,
                     builder().CreateConstInBoundsGEP2_32(complex_type,
                                                          place,
                                                          0,
                                                          index,
                                                          "complex.place"));
            return;
        }
        case cir::InstKind::VectorElementPlace:
            remember(inst_id, nullptr);
            return;
        case cir::InstKind::VectorExtract:
            remember(inst_id, lower_vector_extract(values[0], values[1], inst.loc));
            return;
        case cir::InstKind::FieldAddr:
            remember(inst_id, lower_field_addr(inst, operands, values));
            return;
        case cir::InstKind::DataMemberPointerPlace:
            remember(inst_id, lower_data_member_pointer_place(inst, values));
            return;
        case cir::InstKind::MemberFunctionPointerCallee:
            remember(inst_id, lower_member_function_pointer_callee(inst, values));
            return;
        case cir::InstKind::MemberFunctionPointerThis:
            remember(inst_id, lower_member_function_pointer_this(inst, values));
            return;
        case cir::InstKind::SizeofType:
            remember(inst_id,
                     constant_usize(size_of_type(type_operand_at(operands, 0).type,
                                                 inst.loc).value_or(0)));
            return;
        case cir::InstKind::AlignofType:
            remember(inst_id,
                     constant_usize(align_of_type(type_operand_at(operands, 0).type,
                                                  inst.loc).value_or(0)));
            return;
        case cir::InstKind::UnaryOp:
            if (const auto* descriptor =
                    std::get_if<cir::UnaryOpDescriptor>(&payload)) {
                remember(inst_id, lower_unary(inst, *descriptor, values));
            } else {
                error("unary instruction is missing a descriptor", inst.loc);
            }
            return;
        case cir::InstKind::BinaryOp:
            if (const auto* descriptor =
                    std::get_if<cir::BinaryOpDescriptor>(&payload)) {
                remember(inst_id, lower_binary(inst, *descriptor, values));
            } else {
                error("binary instruction is missing a descriptor", inst.loc);
            }
            return;
        case cir::InstKind::Cast:
        {
            cir::ValueRef source = values.empty() ? cir::ValueRef{} : values[0];
            cir::TypeId source_type = file_.valid(source.inst)
                ? file_.inst(source.inst).result_type
                : cir::TypeId{};

            if (const auto* cast_payload = std::get_if<cir::CastPayload>(&payload);
                cast_payload && cast_payload->kind == "vector_reinterpret") {
                llvm::Value* src = value_for(source, inst.loc);
                llvm::Type* target = llvm_type(inst.result_type);
                if (src && target &&
                    module().getDataLayout().getTypeSizeInBits(src->getType()) ==
                        module().getDataLayout().getTypeSizeInBits(target)) {
                    remember(inst_id,
                             builder().CreateBitCast(src, target, "vector.reinterpret"));
                    return;
                }
            }
            remember(inst_id,
                     cast_value(value_for(source, inst.loc),
                                source_type,
                                inst.result_type,
                                inst.loc,
                                "cast"));
            return;
        }
        case cir::InstKind::Call:
            if (inst.runtime_elided_object_operation) {
                return;
            }
            remember(inst_id, lower_call(inst, operands));
            return;
        case cir::InstKind::VaStart:
            remember(inst_id, lower_va_start(inst, values));
            return;
        case cir::InstKind::VaArg:
            remember(inst_id, lower_va_arg(inst, operands));
            return;
        case cir::InstKind::VaEnd:
            remember(inst_id, lower_va_end(inst, values));
            return;
        case cir::InstKind::VaCopy:
            remember(inst_id, lower_va_copy(inst, values));
            return;
        case cir::InstKind::BuiltinCall:
            if (const auto* builtin =
                    std::get_if<cir::BuiltinCallPayload>(&payload)) {
                remember(inst_id, lower_builtin_call(inst, *builtin, values));
            } else {
                error("builtin call instruction is missing builtin metadata", inst.loc);
            }
            return;
        case cir::InstKind::InlineAsm: {
            const auto* asm_ref = std::get_if<cir::InlineAsmPayloadRef>(&payload);
            if (!asm_ref || !file_.valid(asm_ref->payload)) {
                error("inline asm instruction is missing asm metadata", inst.loc);
                return;
            }
            lower_inline_asm(file_.inline_asm_payload(asm_ref->payload),
                             values,
                             nullptr,
                             {},
                             inst.loc);
            return;
        }
        case cir::InstKind::Param:
            return;
        case cir::InstKind::ConstructInPlace:
            if (inst.runtime_elided_object_operation) {
                return;
            }
            lower_construct_in_place(inst, operands);
            return;
        case cir::InstKind::Destroy:
            lower_destroy(inst, operands);
            return;
        case cir::InstKind::EhAllocException:
            if (!inst_values_.contains(id_key(inst_id))) {
                remember(inst_id, lower_eh_alloc_exception(inst));
            }
            return;
        case cir::InstKind::EhLandingPad:
            remember(inst_id, lower_eh_landing_pad(inst_id, inst));
            return;
        case cir::InstKind::EhSelector:
            remember(inst_id, lower_eh_selector(inst, values));
            return;
        case cir::InstKind::EhTypeId:
            remember(inst_id, lower_eh_typeid_for(inst, operands));
            return;
        case cir::InstKind::CatchBegin:
            remember(inst_id, lower_catch_begin(inst, values));
            return;
        case cir::InstKind::CatchEnd:
            lower_catch_end(inst);
            return;
        case cir::InstKind::Invalid:
        case cir::InstKind::NameRef:
        case cir::InstKind::DependentCall:
        case cir::InstKind::DependentRegion:
        case cir::InstKind::Error:
            error("unsupported instruction reached lowering: " +
                      std::string(cir::inst_mnemonic(inst.kind)),
                  inst.loc);
            return;
    }
}

void Lowerer::lower_construct_in_place(const cir::Inst& inst,
                                       const std::vector<cir::Operand>& operands) {
    if (operands.size() < 2) {
        error("construct_in_place expects a place and a constructor", inst.loc);
        return;
    }
    cir::ValueRef place_ref = value_operand_at(operands, 0);
    llvm::Value* place = value_for(place_ref, inst.loc);
    const auto* constructor = std::get_if<cir::EntityId>(&operands[1].data);
    if (!place || !constructor || !constructor->valid()) {
        error("construct_in_place has invalid operands", inst.loc);
        return;
    }
    if (file_.valid(*constructor) &&
        file_.entity(*constructor).decl_flags.is_consteval) {
        error("call to consteval constructor is not a constant expression",
              inst.loc);
        return;
    }
    llvm::Function* callee = get_or_declare_function(*constructor);
    if (!callee) {
        return;
    }

    FunctionAbiInfo abi = classify_function_abi(file_.entity(*constructor).type);
    if (!abi.llvm_type) {
        return;
    }
    std::vector<llvm::Value*> args;
    args.reserve(operands.size() - 1);
    args.push_back(place);
    for (size_t i = 2; i < operands.size(); ++i) {
        llvm::Value* arg = value_for(value_operand_at(operands, i), inst.loc);
        if (!arg) {
            return;
        }
        size_t param_index = i - 1;
        if (param_index < abi.params.size()) {
            const AbiArgInfo& param_abi = abi.params[param_index];
            if (param_abi.is_ignored) {
                continue;
            }
            if (param_abi.kind == AbiArgKind::Indirect) {
                cir::EntityId argument_object =
                    parameter_argument_object(file_,
                                              value_operand_at(operands, i).inst);
                arg = argument_object.valid()
                    ? storage_for_entity(argument_object, inst.loc)
                    : materialize_source_value_to_indirect_abi(
                          arg, param_abi.source_type, inst.loc,
                          "ctor.indirect");
            } else if (param_abi.is_direct_aggregate) {
                arg = materialize_source_value_to_abi(arg,
                                                      param_abi.source_type,
                                                      param_abi.abi_type,
                                                      inst.loc,
                                                      "ctor.abi");
            } else {
                arg = cast_value(arg, param_abi.abi_type, inst.loc, "ctor.cast");
            }
        }
        if (!arg) {
            return;
        }
        args.push_back(arg);
    }
    size_t fixed_params = callee->getFunctionType()->getNumParams();
    if ((!callee->isVarArg() && fixed_params != args.size()) ||
        (callee->isVarArg() && args.size() < fixed_params)) {
        error("constructor call arity does not match its signature", inst.loc);
        return;
    }
    emit_call_or_invoke(callee->getFunctionType(), callee, args,
                        /*can_throw=*/!callee->doesNotThrow(), "", inst.loc);
}

void Lowerer::lower_destroy(const cir::Inst& inst,
                            const std::vector<cir::Operand>& operands) {
    if (operands.empty()) {
        error("destroy expects a place operand", inst.loc);
        return;
    }
    const cir::EntityId* destructor = operands.size() > 1
        ? std::get_if<cir::EntityId>(&operands[1].data)
        : nullptr;
    if (!destructor || !destructor->valid()) {

        return;
    }
    cir::ValueRef place_ref = value_operand_at(operands, 0);
    llvm::Value* place = value_for(place_ref, inst.loc);
    if (!place) {
        return;
    }
    llvm::Function* callee = get_or_declare_function(*destructor);
    if (!callee) {
        return;
    }
    emit_call_or_invoke(callee->getFunctionType(), callee, {place},
                        /*can_throw=*/!callee->doesNotThrow(), "", inst.loc);
}

bool Lowerer::function_uses_eh(const cir::Function& function) const {
    for (cir::BlockId block_id : function.blocks) {
        const cir::Block& block = file_.block(block_id);
        if (block.unwind_target.valid()) {
            return true;
        }
        switch (block.terminator.kind) {
            case cir::TerminatorKind::Throw:
            case cir::TerminatorKind::Rethrow:
            case cir::TerminatorKind::Resume:
                return true;
            default:
                break;
        }
        for (cir::InstId inst_id : block.instructions) {
            if (file_.valid(inst_id) &&
                file_.inst(inst_id).kind == cir::InstKind::EhLandingPad) {
                return true;
            }
        }
    }
    return false;
}

void Lowerer::apply_eh_function_setup(llvm::Function* function,
                                      bool non_throwing_type) {
    if (!function->hasPersonalityFn()) {
        const EhRuntimeHooks& hooks = file_.abi_policy().eh_runtime_hooks;
        llvm::FunctionType* personality_type = llvm::FunctionType::get(
            llvm::Type::getInt32Ty(context()), /*isVarArg=*/true);
        llvm::FunctionCallee personality =
            module().getOrInsertFunction(hooks.personality, personality_type);
        function->setPersonalityFn(
            llvm::cast<llvm::Constant>(personality.getCallee()));
    }
    function->setUWTableKind(llvm::UWTableKind::Sync);

    if (!non_throwing_type) {
        function->removeFnAttr(llvm::Attribute::NoUnwind);
    }
}

llvm::FunctionCallee Lowerer::eh_runtime_callee(std::string_view name,
                                                llvm::FunctionType* type,
                                                bool is_noreturn,
                                                bool is_nounwind) {
    llvm::FunctionCallee callee = module().getOrInsertFunction(
        llvm::StringRef(name.data(), name.size()), type);
    if (auto* function = llvm::dyn_cast<llvm::Function>(callee.getCallee())) {
        if (is_noreturn) {
            function->addFnAttr(llvm::Attribute::NoReturn);
        }
        if (is_nounwind) {
            function->addFnAttr(llvm::Attribute::NoUnwind);
        }
    }
    return callee;
}

llvm::BasicBlock* Lowerer::llvm_block_for(cir::BlockId block, SrcLoc loc) {
    auto found = block_values_.find(id_key(block));
    if (found == block_values_.end()) {
        error("missing lowered block for unwind target", loc);
        return nullptr;
    }
    return found->second;
}

llvm::CallBase* Lowerer::emit_call_or_invoke(llvm::FunctionType* fn_type,
                                             llvm::Value* callee,
                                             llvm::ArrayRef<llvm::Value*> args,
                                             bool can_throw,
                                             const llvm::Twine& name,
                                             SrcLoc loc) {
    const cir::Block* block = file_.valid(current_cir_block_)
        ? &file_.block(current_cir_block_)
        : nullptr;
    if (can_throw && block && block->unwind_target.valid()) {
        if (auto* function = llvm::dyn_cast<llvm::Function>(callee);
            !function || !function->doesNotThrow()) {
            llvm::BasicBlock* unwind_dest =
                llvm_block_for(block->unwind_target, loc);
            if (!unwind_dest) {
                return nullptr;
            }
            llvm::BasicBlock* normal_dest = llvm::BasicBlock::Create(
                context(), "invoke.cont", current_function_);
            llvm::InvokeInst* invoke = builder().CreateInvoke(
                fn_type, callee, normal_dest, unwind_dest, args, name);
            builder().SetInsertPoint(normal_dest);
            return invoke;
        }
    }
    return builder().CreateCall(fn_type, callee, args, name);
}

llvm::Value* Lowerer::lower_eh_alloc_exception(const cir::Inst& inst) {
    cir::TypeId object_type = file_.place_object_type(inst.result_type);
    std::optional<uint64_t> size = size_of_type(object_type, inst.loc);
    if (!size) {
        error("cannot size the exception object type", inst.loc);
        return nullptr;
    }
    const EhRuntimeHooks& hooks = file_.abi_policy().eh_runtime_hooks;
    llvm::Type* ptr = llvm::PointerType::get(context(), 0);
    llvm::FunctionType* type = llvm::FunctionType::get(
        ptr, {llvm::Type::getInt64Ty(context())}, false);
    llvm::FunctionCallee callee = eh_runtime_callee(
        hooks.allocate_exception, type, false, /*is_nounwind=*/true);
    return builder().CreateCall(
        type, callee.getCallee(),
        {llvm::ConstantInt::get(llvm::Type::getInt64Ty(context()), *size)},
        "exn.alloc");
}

llvm::Value* Lowerer::lower_eh_landing_pad(cir::InstId inst_id,
                                           const cir::Inst& inst) {
    const auto* clause_payload = std::get_if<cir::EhLandingPadPayload>(
        &file_.payload(inst.payload_index));
    if (!clause_payload) {
        error("landing pad instruction is missing clause metadata", inst.loc);
        return nullptr;
    }
    llvm::Type* ptr = llvm::PointerType::get(context(), 0);
    llvm::StructType* pad_type =
        llvm::StructType::get(ptr, llvm::Type::getInt32Ty(context()));
    unsigned clause_count =
        static_cast<unsigned>(clause_payload->clause_typeinfos.size()) +
        (clause_payload->has_catch_all ? 1u : 0u);
    llvm::LandingPadInst* pad =
        builder().CreateLandingPad(pad_type, clause_count, "lpad");
    pad->setCleanup(clause_payload->is_cleanup);
    for (cir::EntityId clause : clause_payload->clause_typeinfos) {
        llvm::GlobalValue* typeinfo = get_or_create_global(clause);
        if (!typeinfo) {
            error("landing pad clause has no typeinfo global", inst.loc);
            return nullptr;
        }
        pad->addClause(typeinfo);
    }
    if (clause_payload->has_catch_all) {
        pad->addClause(llvm::Constant::getNullValue(ptr));
    }
    landingpad_values_[id_key(inst_id)] = pad;
    return builder().CreateExtractValue(pad, 0, "exn.ptr");
}

llvm::Value* Lowerer::lower_eh_selector(
    const cir::Inst& inst,
    const std::vector<cir::ValueRef>& operands) {
    if (operands.empty()) {
        error("eh_selector is missing its landing pad operand", inst.loc);
        return nullptr;
    }
    auto found = landingpad_values_.find(id_key(operands[0].inst));
    if (found == landingpad_values_.end()) {
        error("eh_selector operand is not a lowered landing pad", inst.loc);
        return nullptr;
    }
    return builder().CreateExtractValue(found->second, 1, "exn.sel");
}

llvm::Value* Lowerer::lower_eh_typeid_for(
    const cir::Inst& inst,
    const std::vector<cir::Operand>& operands) {
    cir::EntityId typeinfo = entity_operand_at(operands, 0);
    llvm::GlobalValue* global = get_or_create_global(typeinfo);
    if (!global) {
        error("eh_typeid_for operand has no typeinfo global", inst.loc);
        return nullptr;
    }
    llvm::Function* intrinsic = llvm::Intrinsic::getOrInsertDeclaration(
        &module(), llvm::Intrinsic::eh_typeid_for,
        {llvm::PointerType::get(context(), 0)});
    return builder().CreateCall(intrinsic, {global}, "typeid");
}

llvm::Value* Lowerer::lower_catch_begin(
    const cir::Inst& inst,
    const std::vector<cir::ValueRef>& operands) {
    if (operands.empty()) {
        error("catch_begin is missing the exception pointer", inst.loc);
        return nullptr;
    }
    llvm::Value* exception = value_for(operands[0], inst.loc);
    if (!exception) {
        return nullptr;
    }
    const EhRuntimeHooks& hooks = file_.abi_policy().eh_runtime_hooks;
    llvm::Type* ptr = llvm::PointerType::get(context(), 0);
    llvm::FunctionType* type = llvm::FunctionType::get(ptr, {ptr}, false);
    llvm::FunctionCallee callee =
        eh_runtime_callee(hooks.begin_catch, type, false, /*is_nounwind=*/true);
    return builder().CreateCall(type, callee.getCallee(), {exception},
                                "catch.obj");
}

void Lowerer::lower_catch_end(const cir::Inst& inst) {
    const EhRuntimeHooks& hooks = file_.abi_policy().eh_runtime_hooks;
    llvm::FunctionType* type =
        llvm::FunctionType::get(llvm::Type::getVoidTy(context()), false);
    llvm::FunctionCallee callee = eh_runtime_callee(hooks.end_catch, type);

    emit_call_or_invoke(type, callee.getCallee(), {}, /*can_throw=*/true, "",
                        inst.loc);
}

void Lowerer::lower_throw_terminator(const cir::Terminator& terminator) {
    const EhRuntimeHooks& hooks = file_.abi_policy().eh_runtime_hooks;
    llvm::Type* void_type = llvm::Type::getVoidTy(context());
    if (terminator.kind == cir::TerminatorKind::Rethrow) {
        llvm::FunctionType* type = llvm::FunctionType::get(void_type, false);
        llvm::FunctionCallee callee =
            eh_runtime_callee(hooks.rethrow_exception, type,
                              /*is_noreturn=*/true);
        emit_call_or_invoke(type, callee.getCallee(), {}, /*can_throw=*/true,
                            "", terminator.loc);
        builder().CreateUnreachable();
        return;
    }
    std::vector<cir::Operand> operands = file_.operands(terminator.operands);
    llvm::Value* exception =
        value_for(value_operand_at(operands, 0), terminator.loc);
    cir::EntityId typeinfo = entity_operand_at(operands, 1);
    llvm::GlobalValue* typeinfo_global = get_or_create_global(typeinfo);
    if (!exception || !typeinfo_global) {
        error("throw terminator has invalid operands", terminator.loc);
        return;
    }
    llvm::Type* ptr = llvm::PointerType::get(context(), 0);
    llvm::Value* destructor = llvm::Constant::getNullValue(ptr);
    if (operands.size() > 2) {
        if (cir::EntityId dtor = entity_operand_at(operands, 2);
            dtor.valid()) {
            if (llvm::GlobalValue* dtor_symbol = function_symbol(dtor)) {
                destructor = dtor_symbol;
            }
        }
    }
    llvm::FunctionType* type =
        llvm::FunctionType::get(void_type, {ptr, ptr, ptr}, false);
    llvm::FunctionCallee callee =
        eh_runtime_callee(hooks.throw_exception, type, /*is_noreturn=*/true);
    emit_call_or_invoke(type, callee.getCallee(),
                        {exception, typeinfo_global, destructor},
                        /*can_throw=*/true, "", terminator.loc);
    builder().CreateUnreachable();
}

void Lowerer::lower_resume_terminator(const cir::Terminator& terminator) {
    std::vector<cir::ValueRef> operands =
        file_.value_operands(terminator.operands);
    if (operands.size() != 2) {
        error("resume terminator must carry exception pointer and selector",
              terminator.loc);
        return;
    }
    llvm::Value* exception = value_for(operands[0], terminator.loc);
    llvm::Value* selector = value_for(operands[1], terminator.loc);
    if (!exception || !selector) {
        return;
    }
    llvm::Type* ptr = llvm::PointerType::get(context(), 0);
    llvm::StructType* pad_type =
        llvm::StructType::get(ptr, llvm::Type::getInt32Ty(context()));
    llvm::Value* aggregate = llvm::UndefValue::get(pad_type);
    aggregate = builder().CreateInsertValue(aggregate, exception, 0);
    aggregate = builder().CreateInsertValue(aggregate, selector, 1);
    builder().CreateResume(aggregate);
}

llvm::Value* Lowerer::lower_va_start(const cir::Inst& inst,
                                     const std::vector<cir::ValueRef>& operands) {
    if (operands.empty()) {
        error("va_start is missing a va_list operand", inst.loc);
        return nullptr;
    }
    llvm::Value* va_list_ptr = value_for(operands[0], inst.loc);
    if (!va_list_ptr) {
        return nullptr;
    }
    llvm::Function* intrinsic =
        llvm::Intrinsic::getOrInsertDeclaration(&module(),
                                                llvm::Intrinsic::vastart,
                                                {va_list_ptr->getType()});
    return builder().CreateCall(intrinsic, {va_list_ptr});
}

llvm::Value* Lowerer::lower_va_arg(const cir::Inst& inst,
                                   const std::vector<cir::Operand>& operands) {
    cir::TypeRef target = type_operand_at(operands, 0);
    cir::ValueRef list_ref = value_operand_at(operands, 1);
    llvm::Value* va_list_ptr = value_for(list_ref, inst.loc);
    if (!va_list_ptr) {
        return nullptr;
    }
    llvm::Type* arg_type = llvm_type(target.type.valid() ? target.type : inst.result_type);
    if (!arg_type) {
        error("va_arg has invalid result type", inst.loc);
        return nullptr;
    }

    if (options_.target && options_.target->va_list_kind == VaListKind::CHAR_PTR) {
        const llvm::DataLayout& layout = module().getDataLayout();
        uint64_t arg_size = layout.getTypeAllocSize(arg_type);
        uint64_t arg_align = layout.getABITypeAlign(arg_type).value();
        bool indirect_aggregate = arg_type->isAggregateType() && arg_size > 16;
        uint64_t slot_align = indirect_aggregate ? 8 : std::max<uint64_t>(8, arg_align);
        uint64_t slot_size = indirect_aggregate ? 8 : ((arg_size + 7) / 8) * 8;
        if (!indirect_aggregate && slot_size == 0) {
            slot_size = 8;
        }

        llvm::Type* ptr_type = llvm::PointerType::get(context(), 0);
        llvm::IntegerType* intptr_type =
            llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()));
        llvm::Value* current_ptr = builder().CreateLoad(ptr_type, va_list_ptr, "va.cur");
        llvm::Value* current_int = builder().CreatePtrToInt(current_ptr, intptr_type, "va.cur.i");

        uint64_t align_mask = slot_align - 1;
        llvm::Value* aligned_int = current_int;
        if (align_mask != 0) {
            llvm::Value* plus = builder().CreateAdd(
                current_int,
                llvm::ConstantInt::get(intptr_type, align_mask),
                "va.align.add");
            llvm::Value* mask = llvm::ConstantInt::get(intptr_type, ~align_mask);
            aligned_int = builder().CreateAnd(plus, mask, "va.aligned.i");
        }

        llvm::Value* aligned_ptr =
            builder().CreateIntToPtr(aligned_int, ptr_type, "va.aligned.ptr");
        llvm::Value* next_int = builder().CreateAdd(
            aligned_int,
            llvm::ConstantInt::get(intptr_type, slot_size),
            "va.next.i");
        llvm::Value* next_ptr = builder().CreateIntToPtr(next_int, ptr_type, "va.next.ptr");
        builder().CreateStore(next_ptr, va_list_ptr);

        if (indirect_aggregate) {
            llvm::Value* indirect_ptr =
                builder().CreateLoad(ptr_type, aligned_ptr, "va.indirect.ptr");
            auto* load = builder().CreateLoad(arg_type, indirect_ptr, "va.arg");
            if (arg_align > 0) {
                load->setAlignment(llvm::Align(arg_align));
            }
            return load;
        }

        auto* load = builder().CreateLoad(arg_type, aligned_ptr, "va.arg");
        if (arg_align > 0) {
            load->setAlignment(llvm::Align(arg_align));
        }
        return load;
    }

    if (options_.target &&
        options_.target->va_list_kind == VaListKind::AARCH64_VA_LIST) {
        return lower_va_arg_aapcs64(
            file_.resolved_type(target.type.valid() ? target.type
                                                    : inst.result_type),
            va_list_ptr,
            arg_type);
    }

    return builder().CreateVAArg(va_list_ptr, arg_type, "va.arg");
}

llvm::Value* Lowerer::lower_va_arg_aapcs64(cir::TypeId value_type,
                                           llvm::Value* va_list_ptr,
                                           llvm::Type* arg_type) {
    const llvm::DataLayout& layout = module().getDataLayout();
    llvm::Type* ptr_type = llvm::PointerType::get(context(), 0);
    llvm::Type* i8_type = llvm::Type::getInt8Ty(context());
    llvm::IntegerType* i32_type = llvm::Type::getInt32Ty(context());
    llvm::IntegerType* i64_type = llvm::Type::getInt64Ty(context());

    uint64_t size = layout.getTypeAllocSize(arg_type);
    uint64_t align = layout.getABITypeAlign(arg_type).value();
    if (auto size_align = cir::size_align_of_type(file_, value_type)) {
        size = size_align->size_bytes;
        align = size_align->alignment_bytes;
    }

    auto vr_element_size = [](cir::BuiltinTypeKind kind) -> uint64_t {
        switch (kind) {
            case cir::BuiltinTypeKind::Float16: return 2;
            case cir::BuiltinTypeKind::Float: return 4;
            case cir::BuiltinTypeKind::Double: return 8;
            default: return 16;
        }
    };

    bool use_vr = false;
    bool indirect = false;
    unsigned reg_count = 1;
    uint64_t elem_size = size;

    abi::AggregateClass cls =
        abi::classify_aarch64_vararg(file_, file_.type_ref(value_type),
                                     options_.target.get());
    switch (cls.pass) {
        case abi::AggregatePass::Ignore:
            return llvm::UndefValue::get(arg_type);
        case abi::AggregatePass::Indirect:
            indirect = true;
            break;
        case abi::AggregatePass::CoerceHfa:
            use_vr = true;
            reg_count = cls.hfa_count;
            elem_size = vr_element_size(cls.hfa_element);
            break;
        case abi::AggregatePass::CoerceIntSlots:
        case abi::AggregatePass::CoerceClassedSlots:
        case abi::AggregatePass::MemoryByval:
            reg_count = cls.int_slot_count;
            break;
        case abi::AggregatePass::UseSourceType: {
            const cir::Type& type = file_.type(value_type);
            cir::BuiltinTypeKind kind = cir::BuiltinTypeKind::Other;
            if (type.kind == cir::TypeKind::Complex) {
                const auto& payload = std::get<cir::ComplexTypePayload>(
                    file_.type_payload(value_type));
                cir::TypeId element =
                    file_.resolved_type(payload.element_type.type);
                if (file_.valid(element) &&
                    file_.type(element).kind == cir::TypeKind::Builtin) {
                    kind = std::get<cir::BuiltinTypePayload>(
                               file_.type_payload(element))
                               .kind;
                }
                switch (kind) {
                    case cir::BuiltinTypeKind::Float16:
                    case cir::BuiltinTypeKind::Float:
                    case cir::BuiltinTypeKind::Double:
                    case cir::BuiltinTypeKind::LongDouble:
                        use_vr = true;
                        reg_count = 2;
                        elem_size = vr_element_size(kind);
                        break;
                    default:
                        if (size > 16) {
                            indirect = true;
                        } else {
                            reg_count =
                                static_cast<unsigned>((size + 7) / 8);
                        }
                        break;
                }
                break;
            }
            if (type.kind == cir::TypeKind::Builtin) {
                kind = std::get<cir::BuiltinTypePayload>(
                           file_.type_payload(value_type))
                           .kind;
            }
            switch (kind) {
                case cir::BuiltinTypeKind::Float16:
                case cir::BuiltinTypeKind::Float:
                case cir::BuiltinTypeKind::Double:
                case cir::BuiltinTypeKind::LongDouble:
                    use_vr = true;
                    reg_count = 1;
                    elem_size = vr_element_size(kind);
                    break;
                case cir::BuiltinTypeKind::Int128:
                case cir::BuiltinTypeKind::UInt128:
                    reg_count = 2;
                    break;
                default:
                    reg_count = static_cast<unsigned>(
                        std::max<uint64_t>(1, (size + 7) / 8));
                    break;
            }
            break;
        }
    }

    const uint64_t offs_offset = use_vr ? 28 : 24;
    const uint64_t top_offset = use_vr ? 16 : 8;
    const uint64_t reg_area_bytes =
        indirect ? 8 : (use_vr ? 16u * reg_count : 8u * reg_count);

    llvm::Function* function = builder().GetInsertBlock()->getParent();
    llvm::BasicBlock* try_reg =
        llvm::BasicBlock::Create(context(), "va.maybe_reg", function);
    llvm::BasicBlock* in_reg =
        llvm::BasicBlock::Create(context(), "va.in_reg", function);
    llvm::BasicBlock* on_stack =
        llvm::BasicBlock::Create(context(), "va.on_stack", function);
    llvm::BasicBlock* cont =
        llvm::BasicBlock::Create(context(), "va.cont", function);

    llvm::Value* offs_ptr = builder().CreateConstInBoundsGEP1_64(
        i8_type, va_list_ptr, offs_offset, "va.offs.ptr");
    llvm::Value* reg_offs =
        builder().CreateLoad(i32_type, offs_ptr, "va.offs");
    llvm::Value* regs_exhausted = builder().CreateICmpSGE(
        reg_offs, llvm::ConstantInt::get(i32_type, 0), "va.regs_used");
    builder().CreateCondBr(regs_exhausted, on_stack, try_reg);

    builder().SetInsertPoint(try_reg);
    llvm::Value* aligned_offs = reg_offs;
    if (!use_vr && !indirect && align > 8) {

        aligned_offs = builder().CreateAdd(
            reg_offs, llvm::ConstantInt::get(i32_type, 15), "va.offs.pad");
        aligned_offs = builder().CreateAnd(
            aligned_offs, llvm::ConstantInt::get(i32_type, -16),
            "va.offs.aligned");
    }
    llvm::Value* new_offs = builder().CreateAdd(
        aligned_offs,
        llvm::ConstantInt::get(i32_type, static_cast<uint32_t>(reg_area_bytes)),
        "va.offs.next");
    builder().CreateStore(new_offs, offs_ptr);
    llvm::Value* fits = builder().CreateICmpSLE(
        new_offs, llvm::ConstantInt::get(i32_type, 0), "va.fits");
    builder().CreateCondBr(fits, in_reg, on_stack);

    builder().SetInsertPoint(in_reg);
    llvm::Value* top_ptr = builder().CreateConstInBoundsGEP1_64(
        i8_type, va_list_ptr, top_offset, "va.top.ptr");
    llvm::Value* reg_top = builder().CreateLoad(ptr_type, top_ptr, "va.top");
    llvm::Value* reg_base = builder().CreateGEP(
        i8_type, reg_top,
        builder().CreateSExt(aligned_offs, i64_type, "va.offs.wide"),
        "va.reg.addr");
    llvm::Value* in_reg_addr = reg_base;
    if (indirect) {
        in_reg_addr =
            builder().CreateLoad(ptr_type, reg_base, "va.reg.indirect");
    } else if (use_vr && reg_count > 1 && elem_size < 16) {

        llvm::Value* repacked =
            builder().CreateAlloca(arg_type, nullptr, "va.hfa");
        llvm::Type* elem_type =
            elem_size == 2 ? llvm::Type::getHalfTy(context())
            : elem_size == 4 ? llvm::Type::getFloatTy(context())
                             : llvm::Type::getDoubleTy(context());
        for (unsigned i = 0; i < reg_count; ++i) {
            llvm::Value* src = builder().CreateConstInBoundsGEP1_64(
                i8_type, reg_base, 16u * i, "va.hfa.src");
            llvm::Value* dst = builder().CreateConstInBoundsGEP1_64(
                i8_type, repacked, elem_size * i, "va.hfa.dst");
            builder().CreateStore(
                builder().CreateLoad(elem_type, src, "va.hfa.elem"), dst);
        }
        in_reg_addr = repacked;
    }
    llvm::BasicBlock* in_reg_end = builder().GetInsertBlock();
    builder().CreateBr(cont);

    builder().SetInsertPoint(on_stack);
    llvm::Value* stack_slot_ptr = va_list_ptr;
    llvm::Value* stack =
        builder().CreateLoad(ptr_type, stack_slot_ptr, "va.stack");
    if (!indirect && align > 8) {
        llvm::Value* stack_int =
            builder().CreatePtrToInt(stack, i64_type, "va.stack.i");
        stack_int = builder().CreateAdd(
            stack_int, llvm::ConstantInt::get(i64_type, 15), "va.stack.pad");
        stack_int = builder().CreateAnd(
            stack_int, llvm::ConstantInt::get(i64_type, -16),
            "va.stack.aligned");
        stack = builder().CreateIntToPtr(stack_int, ptr_type, "va.stack.ptr");
    }
    const uint64_t stack_slot_bytes =
        indirect ? 8 : std::max<uint64_t>(8, (size + 7) & ~uint64_t{7});
    llvm::Value* new_stack = builder().CreateConstInBoundsGEP1_64(
        i8_type, stack, stack_slot_bytes, "va.stack.next");
    builder().CreateStore(new_stack, stack_slot_ptr);
    llvm::Value* on_stack_addr = stack;
    if (indirect) {
        on_stack_addr =
            builder().CreateLoad(ptr_type, stack, "va.stack.indirect");
    }
    llvm::BasicBlock* on_stack_end = builder().GetInsertBlock();
    builder().CreateBr(cont);

    builder().SetInsertPoint(cont);
    llvm::PHINode* addr = builder().CreatePHI(ptr_type, 2, "va.addr");
    addr->addIncoming(in_reg_addr, in_reg_end);
    addr->addIncoming(on_stack_addr, on_stack_end);
    auto* load = builder().CreateLoad(arg_type, addr, "va.arg");
    load->setAlignment(llvm::Align(std::max<uint64_t>(1, std::min<uint64_t>(align, 16))));
    return load;
}

llvm::Value* Lowerer::lower_va_end(const cir::Inst& inst,
                                   const std::vector<cir::ValueRef>& operands) {
    if (operands.empty()) {
        error("va_end is missing a va_list operand", inst.loc);
        return nullptr;
    }
    llvm::Value* va_list_ptr = value_for(operands[0], inst.loc);
    if (!va_list_ptr) {
        return nullptr;
    }
    llvm::Function* intrinsic =
        llvm::Intrinsic::getOrInsertDeclaration(&module(),
                                                llvm::Intrinsic::vaend,
                                                {va_list_ptr->getType()});
    return builder().CreateCall(intrinsic, {va_list_ptr});
}

llvm::Value* Lowerer::lower_va_copy(const cir::Inst& inst,
                                    const std::vector<cir::ValueRef>& operands) {
    if (operands.size() < 2) {
        error("va_copy is missing operands", inst.loc);
        return nullptr;
    }
    llvm::Value* dest = value_for(operands[0], inst.loc);
    llvm::Value* src = value_for(operands[1], inst.loc);
    if (!dest || !src) {
        return nullptr;
    }
    llvm::Function* intrinsic =
        llvm::Intrinsic::getOrInsertDeclaration(&module(),
                                                llvm::Intrinsic::vacopy,
                                                {dest->getType()});
    return builder().CreateCall(intrinsic, {dest, src});
}

const cir::RecordFieldFact* Lowerer::field_fact_for_place(cir::InstId place_inst) const {
    if (!file_.valid(place_inst)) {
        return nullptr;
    }
    const cir::Inst& place = file_.inst(place_inst);
    if (!place.place_fact.valid() || !file_.valid(place.place_fact)) {
        return nullptr;
    }
    const cir::PlaceFact& fact = file_.place_fact(place.place_fact);
    if (!fact.entity.valid() || file_.entity(fact.entity).kind != cir::EntityKind::Field) {
        return nullptr;
    }
    return file_.field_fact(fact.entity);
}

bool Lowerer::place_access_is_volatile(cir::InstId place_inst) const {
    if (!file_.valid(place_inst)) {
        return false;
    }
    cir::TypeId place_type = file_.inst(place_inst).result_type;
    if (!file_.valid(place_type) ||
        file_.type(place_type).kind != cir::TypeKind::Place) {
        return false;
    }

    return (file_.place_object_ref(place_type).qualifiers & cir::QualVolatile) !=
           0;
}

llvm::Value* Lowerer::lower_field_addr(const cir::Inst& inst,
                                       const std::vector<cir::Operand>& operands,
                                       const std::vector<cir::ValueRef>& values) {
    llvm::Value* base = value_for(values[0], inst.loc);
    if (!base) {
        return nullptr;
    }
    cir::EntityId field_entity = entity_operand_at(operands, 1);
    const cir::RecordFieldFact* field = file_.field_fact(field_entity);
    if (!field) {
        error("field_addr references a field without record layout facts", inst.loc);
        return nullptr;
    }
    llvm::Value* offset = llvm::ConstantInt::get(
        llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits())),
        static_cast<uint64_t>(field->offset));
    return builder().CreateInBoundsGEP(llvm::Type::getInt8Ty(context()),
                                       base,
                                       offset,
                                       "field.addr");
}

llvm::Value* Lowerer::lower_data_member_pointer_place(
    const cir::Inst& inst,
    const std::vector<cir::ValueRef>& values) {
    if (values.size() < 2) {
        error("data_member_pointer_place is missing operands", inst.loc);
        return nullptr;
    }
    llvm::Value* base = value_for(values[0], inst.loc);
    llvm::Value* offset = value_for(values[1], inst.loc);
    if (!base || !offset) {
        return nullptr;
    }
    llvm::Type* offset_type =
        llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()));
    offset = cast_value(offset, offset_type, inst.loc, "member.ptr.offset");
    if (!offset) {
        return nullptr;
    }
    return builder().CreateGEP(llvm::Type::getInt8Ty(context()),
                               base,
                               offset,
                               "member.ptr.addr");
}

llvm::Value* Lowerer::lower_member_function_pointer_callee(
    const cir::Inst& inst,
    const std::vector<cir::ValueRef>& values) {
    if (values.size() != 2) {
        error("member_function_pointer_callee expects two operands", inst.loc);
        return nullptr;
    }
    llvm::Value* object = value_for(values[0], inst.loc);
    llvm::Value* member_pointer = value_for(values[1], inst.loc);
    if (!object || !member_pointer) {
        return nullptr;
    }
    if (!member_pointer->getType()->isStructTy()) {
        error("member_function_pointer_callee requires pair ABI storage", inst.loc);
        return nullptr;
    }
    llvm::Value* encoded =
        builder().CreateExtractValue(member_pointer, {0}, "member.fn.ptr");
    llvm::Type* intptr_type =
        llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()));
    llvm::Value* raw = builder().CreatePtrToInt(encoded, intptr_type, "member.fn.raw");
    llvm::Value* tag = builder().CreateAnd(
        raw, llvm::ConstantInt::get(intptr_type, 1), "member.fn.tag");
    llvm::Value* is_virtual = builder().CreateICmpNE(
        tag, llvm::ConstantInt::get(intptr_type, 0), "member.fn.is.virtual");

    llvm::Function* function = builder().GetInsertBlock()->getParent();
    llvm::BasicBlock* direct_block =
        llvm::BasicBlock::Create(context(), "member.fn.direct", function);
    llvm::BasicBlock* virtual_block =
        llvm::BasicBlock::Create(context(), "member.fn.virtual", function);
    llvm::BasicBlock* join_block =
        llvm::BasicBlock::Create(context(), "member.fn.join", function);

    builder().CreateCondBr(is_virtual, virtual_block, direct_block);

    builder().SetInsertPoint(direct_block);
    builder().CreateBr(join_block);
    llvm::BasicBlock* direct_end = builder().GetInsertBlock();

    builder().SetInsertPoint(virtual_block);
    llvm::Value* vtable = builder().CreateLoad(
        llvm::PointerType::get(context(), 0), object, "member.fn.vptr");
    llvm::Value* slot_offset = builder().CreateSub(
        raw, llvm::ConstantInt::get(intptr_type, 1), "member.fn.slot.offset");
    llvm::Value* slot_address = builder().CreateGEP(
        llvm::Type::getInt8Ty(context()), vtable, slot_offset,
        "member.fn.slot.addr");
    llvm::Value* virtual_callee = builder().CreateLoad(
        llvm::PointerType::get(context(), 0), slot_address, "member.fn.virtual.ptr");
    builder().CreateBr(join_block);
    llvm::BasicBlock* virtual_end = builder().GetInsertBlock();

    builder().SetInsertPoint(join_block);
    llvm::PHINode* callee = builder().CreatePHI(
        llvm::PointerType::get(context(), 0), 2, "member.fn.resolved");
    callee->addIncoming(encoded, direct_end);
    callee->addIncoming(virtual_callee, virtual_end);
    return callee;
}

llvm::Value* Lowerer::lower_member_function_pointer_this(
    const cir::Inst& inst,
    const std::vector<cir::ValueRef>& values) {
    if (values.size() != 2) {
        error("member_function_pointer_this expects two operands", inst.loc);
        return nullptr;
    }
    llvm::Value* object = value_for(values[0], inst.loc);
    llvm::Value* member_pointer = value_for(values[1], inst.loc);
    if (!object || !member_pointer) {
        return nullptr;
    }
    if (!member_pointer->getType()->isStructTy()) {
        error("member_function_pointer_this requires pair ABI storage", inst.loc);
        return nullptr;
    }
    llvm::Value* adjustment =
        builder().CreateExtractValue(member_pointer, {1}, "member.fn.this.adjust");
    llvm::Type* intptr_type =
        llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()));
    adjustment = cast_value(adjustment, intptr_type, inst.loc, "member.fn.adj");
    if (!adjustment) {
        return nullptr;
    }
    llvm::Value* raw = builder().CreatePtrToInt(object, intptr_type, "this.raw");
    llvm::Value* adjusted =
        builder().CreateAdd(raw, adjustment, "member.fn.this.raw");
    llvm::Type* result_type = llvm_type(inst.result_type);
    if (!result_type || !result_type->isPointerTy()) {
        error("member_function_pointer_this result must be a pointer", inst.loc);
        return nullptr;
    }
    return builder().CreateIntToPtr(adjusted, result_type, "member.fn.this");
}

llvm::Value* Lowerer::lower_bitfield_load(cir::InstId place_inst,
                                          const cir::RecordFieldFact& field,
                                          SrcLoc loc) {
    llvm::Value* place = value_for(place_inst, loc);
    if (!place) {
        return nullptr;
    }
    uint32_t storage_bits = field.storage_size == 0 ? 32 : field.storage_size;
    llvm::IntegerType* storage_type = llvm::IntegerType::get(context(), storage_bits);
    llvm::Value* storage = builder().CreateLoad(storage_type, place, "bitfield.storage");
    llvm::Value* shifted = storage;
    if (field.bit_offset != 0) {
        shifted = builder().CreateLShr(
            shifted,
            llvm::ConstantInt::get(storage_type, field.bit_offset),
            "bitfield.shift");
    }
    uint32_t width = field.bit_width == 0
        ? storage_bits
        : cir::bitfield_value_width(file_, field);
    llvm::APInt mask_bits = llvm::APInt::getLowBitsSet(storage_bits, width);
    llvm::Value* masked = builder().CreateAnd(
        shifted,
        llvm::ConstantInt::get(storage_type, mask_bits),
        "bitfield.mask");

    llvm::Type* result_type = llvm_type(field.type);
    auto* result_int = llvm::dyn_cast<llvm::IntegerType>(result_type);
    if (!result_int) {
        return masked;
    }
    bool is_signed =
        file_.operator_value_domain(field.type) == cir::OperatorValueDomain::SignedInteger;
    if (is_signed && width < storage_bits) {
        llvm::Value* left = builder().CreateShl(
            masked,
            llvm::ConstantInt::get(storage_type, storage_bits - width),
            "bitfield.sign.left");
        masked = builder().CreateAShr(
            left,
            llvm::ConstantInt::get(storage_type, storage_bits - width),
            "bitfield.sign");
    }
    unsigned result_bits = result_int->getBitWidth();
    if (result_bits == storage_bits) {
        return masked;
    }
    if (result_bits < storage_bits) {
        return builder().CreateTrunc(masked, result_type, "bitfield.trunc");
    }
    return is_signed
        ? builder().CreateSExt(masked, result_type, "bitfield.sext")
        : builder().CreateZExt(masked, result_type, "bitfield.zext");
}

void Lowerer::lower_bitfield_store(cir::InstId place_inst,
                                   llvm::Value* value,
                                   const cir::RecordFieldFact& field,
                                   SrcLoc loc) {
    llvm::Value* place = value_for(place_inst, loc);
    if (!place || !value) {
        return;
    }
    uint32_t storage_bits = field.storage_size == 0 ? 32 : field.storage_size;
    uint32_t width = field.bit_width == 0
        ? storage_bits
        : cir::bitfield_value_width(file_, field);
    llvm::IntegerType* storage_type = llvm::IntegerType::get(context(), storage_bits);
    llvm::Value* storage = builder().CreateLoad(storage_type, place, "bitfield.storage");
    llvm::Value* storage_value = cast_value(value, storage_type, loc, "bitfield.value");
    if (!storage_value) {
        return;
    }

    llvm::APInt low_mask = llvm::APInt::getLowBitsSet(storage_bits, width);
    llvm::APInt shifted_mask = low_mask.shl(field.bit_offset);
    llvm::Value* clear_mask =
        llvm::ConstantInt::get(storage_type, ~shifted_mask);
    llvm::Value* cleared = builder().CreateAnd(storage, clear_mask, "bitfield.clear");
    llvm::Value* clipped = builder().CreateAnd(
        storage_value,
        llvm::ConstantInt::get(storage_type, low_mask),
        "bitfield.clip");
    llvm::Value* shifted = clipped;
    if (field.bit_offset != 0) {
        shifted = builder().CreateShl(
            clipped,
            llvm::ConstantInt::get(storage_type, field.bit_offset),
            "bitfield.store.shift");
    }
    llvm::Value* merged = builder().CreateOr(cleared, shifted, "bitfield.merge");
    builder().CreateStore(merged, place);
}

llvm::Value* Lowerer::lower_array_element_place(const cir::Inst& inst,
                                       const std::vector<cir::ValueRef>& operands) {
    llvm::Value* base = value_for(operands[0], inst.loc);
    llvm::Value* index = value_for(operands[1], inst.loc);
    if (!base || !index) {
        return nullptr;
    }

    cir::TypeId element_type = file_.place_object_type(inst.result_type);

    if (llvm::Value* stride = runtime_type_size(element_type, inst.loc);
        stride && !llvm::isa<llvm::Constant>(stride)) {
        llvm::Value* wide_index = cast_value(
            index, llvm::Type::getInt64Ty(context()), inst.loc, "vla.idx");
        llvm::Value* offset =
            builder().CreateMul(wide_index, stride, "vla.offset");
        return builder().CreateInBoundsGEP(
            llvm::Type::getInt8Ty(context()), base, offset, "vla.elem");
    }

    cir::TypeId base_type = file_.inst(operands[0].inst).result_type;
    if (file_.type(base_type).kind == cir::TypeKind::Place) {
        cir::TypeId object_type = file_.place_object_type(base_type);
        if (file_.type(object_type).kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(file_.resolved_type(object_type)));
            if (array && array->size_kind == cir::ArraySizeKind::Variable) {

                return builder().CreateInBoundsGEP(llvm_type(element_type),
                                                   base,
                                                   index,
                                                   "vla.elem");
            }
            llvm::Value* zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(context()), 0);
            return builder().CreateInBoundsGEP(llvm_type(object_type),
                                               base,
                                               {zero, index},
                                               "array.elem");
        }
    }

    return builder().CreateInBoundsGEP(llvm_type(element_type), base, index, "ptr.elem");
}

llvm::Value* Lowerer::runtime_type_size(cir::TypeId type, SrcLoc loc) {
    type = file_.resolved_type(type);
    llvm::Type* i64 = llvm::Type::getInt64Ty(context());
    if (std::optional<size_t> constant = cir::size_of_type(file_, type)) {
        return llvm::ConstantInt::get(i64, *constant);
    }
    if (!file_.valid(type) || file_.type(type).kind != cir::TypeKind::Array) {
        return nullptr;
    }
    const auto* array =
        std::get_if<cir::ArrayTypePayload>(&file_.type_payload(type));
    if (!array) {
        return nullptr;
    }
    llvm::Value* element_size =
        runtime_type_size(array->element_type.type, loc);
    if (!element_size) {
        return nullptr;
    }
    llvm::Value* count = nullptr;
    if (array->size_kind == cir::ArraySizeKind::Variable &&
        array->size_expr.valid()) {
        count = value_for(cir::ValueRef(array->size_expr), loc);
        if (count) {
            count = cast_value(count, i64, loc, "vla.extent");
        }
    } else if (array->size_kind == cir::ArraySizeKind::Constant &&
               array->size.has_value()) {
        count = llvm::ConstantInt::get(i64, *array->size);
    }
    if (!count) {
        return nullptr;
    }
    return builder().CreateMul(count, element_size, "vla.size");
}

llvm::Value* Lowerer::lower_vector_extract(cir::ValueRef vector,
                                           cir::ValueRef index_ref,
                                           SrcLoc loc) {
    llvm::Value* vector_value = value_for(vector, loc);
    llvm::Value* index = value_for(index_ref, loc);
    if (!vector_value || !index) {
        return nullptr;
    }
    index = cast_value(index, llvm::Type::getInt32Ty(context()), loc, "vector.index");
    if (!index) {
        return nullptr;
    }
    return builder().CreateExtractElement(vector_value, index, "vector.extract");
}

llvm::Value* Lowerer::lower_vector_element_load(cir::InstId place_inst, SrcLoc loc) {
    const cir::Inst& place = file_.inst(place_inst);
    std::vector<cir::ValueRef> operands = file_.value_operands(place.operands);
    if (operands.size() < 2) {
        error("vector element place is missing operands", loc);
        return nullptr;
    }
    llvm::Value* base_place = value_for(operands[0], loc);
    if (!base_place) {
        return nullptr;
    }
    cir::TypeId base_place_type = file_.inst(operands[0].inst).result_type;
    cir::TypeId vector_type = file_.place_object_type(base_place_type);
    llvm::Value* vector_value =
        builder().CreateLoad(llvm_type(vector_type), base_place, "vector.load");
    llvm::Value* index = value_for(operands[1], loc);
    if (!index) {
        return nullptr;
    }
    index = cast_value(index, llvm::Type::getInt32Ty(context()), loc, "vector.index");
    if (!index) {
        return nullptr;
    }
    return builder().CreateExtractElement(vector_value, index, "vector.extract");
}

void Lowerer::lower_vector_element_store(cir::InstId place_inst,
                                         llvm::Value* value,
                                         SrcLoc loc) {
    const cir::Inst& place = file_.inst(place_inst);
    std::vector<cir::ValueRef> operands = file_.value_operands(place.operands);
    if (operands.size() < 2) {
        error("vector element place is missing operands", loc);
        return;
    }
    llvm::Value* base_place = value_for(operands[0], loc);
    llvm::Value* index = value_for(operands[1], loc);
    if (!base_place || !index || !value) {
        return;
    }
    cir::TypeId base_place_type = file_.inst(operands[0].inst).result_type;
    cir::TypeId vector_type = file_.place_object_type(base_place_type);
    cir::TypeId element_type = file_.vector_element_type(vector_type);
    llvm::Value* vector_value =
        builder().CreateLoad(llvm_type(vector_type), base_place, "vector.load");
    value = cast_value(value,
                       llvm_type(element_type),
                       loc,
                       "vector.element.store.cast");
    index = cast_value(index, llvm::Type::getInt32Ty(context()), loc, "vector.index");
    if (!value || !index) {
        return;
    }
    llvm::Value* inserted =
        builder().CreateInsertElement(vector_value, value, index, "vector.insert");
    builder().CreateStore(inserted, base_place);
}

llvm::Value* Lowerer::lower_unary(const cir::Inst& inst,
                         const cir::UnaryOpDescriptor& descriptor,
                         const std::vector<cir::ValueRef>& operands) {
    llvm::Value* operand = value_for(operands[0], inst.loc);
    if (!operand) {
        return nullptr;
    }
    switch (descriptor.op) {
        case cir::UnaryOpKind::Plus:
            return cast_value(operand, llvm_type(inst.result_type), inst.loc, "uplus");
        case cir::UnaryOpKind::Minus: {
            cir::OperatorValueDomain minus_domain =
                file_.operator_value_domain(descriptor.computation_type);
            if (minus_domain == cir::OperatorValueDomain::Complex) {
                llvm::Value* re =
                    builder().CreateFNeg(builder().CreateExtractValue(operand, {0}), "cneg.re");
                llvm::Value* im =
                    builder().CreateFNeg(builder().CreateExtractValue(operand, {1}), "cneg.im");
                llvm::Value* value = llvm::UndefValue::get(operand->getType());
                value = builder().CreateInsertValue(value, re, {0});
                return builder().CreateInsertValue(value, im, {1}, "cneg");
            }
            if (minus_domain == cir::OperatorValueDomain::Floating) {
                return builder().CreateFNeg(operand, "fneg");
            }
            return builder().CreateNeg(operand, "neg");
        }
        case cir::UnaryOpKind::LogicalNot:
            return cast_value(builder().CreateNot(truth_value(operand, inst.loc), "not"),
                              llvm_type(inst.result_type),
                              inst.loc,
                              "not.result");
        case cir::UnaryOpKind::BitwiseNot:
            if (file_.operator_value_domain(descriptor.computation_type) ==
                cir::OperatorValueDomain::Complex) {

                llvm::Value* re = builder().CreateExtractValue(operand, {0}, "conj.re");
                llvm::Value* im = builder().CreateExtractValue(operand, {1}, "conj.im");
                im = im->getType()->isFloatingPointTy()
                    ? builder().CreateFNeg(im, "conj.neg")
                    : builder().CreateNeg(im, "conj.neg");
                llvm::Value* out = llvm::UndefValue::get(operand->getType());
                out = builder().CreateInsertValue(out, re, {0});
                return builder().CreateInsertValue(out, im, {1}, "conj");
            }
            return builder().CreateNot(operand, "bitnot");
        case cir::UnaryOpKind::Invalid:
            break;
    }
    error("unsupported unary operator '" +
              std::string(cir::unary_op_spelling(descriptor.op)) + "'",
          inst.loc);
    return nullptr;
}

llvm::Value* Lowerer::lower_complex_binary(const cir::Inst& inst,
                                           const cir::BinaryOpDescriptor& descriptor,
                                           llvm::Value* lhs,
                                           llvm::Value* rhs) {
    llvm::Type* complex_type = lhs->getType();
    llvm::Type* element_type = complex_type->getArrayElementType();
    bool fp = element_type->isFloatingPointTy();

    auto to_complex = [&](llvm::Value* value) -> llvm::Value* {
        if (value->getType() == complex_type) {
            return value;
        }
        llvm::Value* re = value;
        if (re->getType() != element_type) {
            if (fp) {
                re = re->getType()->isIntegerTy()
                    ? builder().CreateSIToFP(re, element_type, "csplat")
                    : builder().CreateFPCast(re, element_type, "csplat");
            } else {
                re = builder().CreateIntCast(re, element_type, true, "csplat");
            }
        }
        llvm::Value* out = llvm::UndefValue::get(complex_type);
        out = builder().CreateInsertValue(out, re, {0});
        return builder().CreateInsertValue(
            out,
            llvm::Constant::getNullValue(element_type),
            {1},
            "csplat.complex");
    };
    rhs = to_complex(rhs);
    llvm::Value* lhs_re = builder().CreateExtractValue(lhs, {0}, "l.re");
    llvm::Value* lhs_im = builder().CreateExtractValue(lhs, {1}, "l.im");
    llvm::Value* rhs_re = builder().CreateExtractValue(rhs, {0}, "r.re");
    llvm::Value* rhs_im = builder().CreateExtractValue(rhs, {1}, "r.im");

    auto make = [&](llvm::Value* re, llvm::Value* im) -> llvm::Value* {
        llvm::Value* value = llvm::UndefValue::get(complex_type);
        value = builder().CreateInsertValue(value, re, {0});
        return builder().CreateInsertValue(value, im, {1}, "complex.result");
    };
    auto add = [&](llvm::Value* a, llvm::Value* b) {
        return fp ? builder().CreateFAdd(a, b) : builder().CreateAdd(a, b);
    };
    auto sub = [&](llvm::Value* a, llvm::Value* b) {
        return fp ? builder().CreateFSub(a, b) : builder().CreateSub(a, b);
    };
    auto mul = [&](llvm::Value* a, llvm::Value* b) {
        return fp ? builder().CreateFMul(a, b) : builder().CreateMul(a, b);
    };
    auto div = [&](llvm::Value* a, llvm::Value* b) {
        return fp ? builder().CreateFDiv(a, b) : builder().CreateSDiv(a, b);
    };
    auto eq = [&](llvm::Value* a, llvm::Value* b) {
        return fp ? builder().CreateFCmpOEQ(a, b) : builder().CreateICmpEQ(a, b);
    };
    auto ne = [&](llvm::Value* a, llvm::Value* b) {
        return fp ? builder().CreateFCmpUNE(a, b) : builder().CreateICmpNE(a, b);
    };

    switch (descriptor.op) {
        case cir::BinaryOpKind::Add:
            return make(add(lhs_re, rhs_re), add(lhs_im, rhs_im));
        case cir::BinaryOpKind::Sub:
            return make(sub(lhs_re, rhs_re), sub(lhs_im, rhs_im));
        case cir::BinaryOpKind::Mul:
        case cir::BinaryOpKind::Div: {
            if (!fp) {

                if (descriptor.op == cir::BinaryOpKind::Mul) {
                    return make(sub(mul(lhs_re, rhs_re), mul(lhs_im, rhs_im)),
                                add(mul(lhs_re, rhs_im), mul(lhs_im, rhs_re)));
                }
                llvm::Value* denom =
                    add(mul(rhs_re, rhs_re), mul(rhs_im, rhs_im));
                return make(
                    div(add(mul(lhs_re, rhs_re), mul(lhs_im, rhs_im)), denom),
                    div(sub(mul(lhs_im, rhs_re), mul(lhs_re, rhs_im)), denom));
            }

            const char* callee = nullptr;
            if (element_type->isFloatTy()) {
                callee = descriptor.op == cir::BinaryOpKind::Mul ? "__mulsc3"
                                                                 : "__divsc3";
            } else {
                callee = descriptor.op == cir::BinaryOpKind::Mul ? "__muldc3"
                                                                 : "__divdc3";
            }
            llvm::FunctionType* helper_type = llvm::FunctionType::get(
                complex_type,
                {element_type, element_type, element_type, element_type},
                false);
            llvm::FunctionCallee helper =
                module().getOrInsertFunction(callee, helper_type);
            return builder().CreateCall(helper,
                                        {lhs_re, lhs_im, rhs_re, rhs_im},
                                        "complex.helper");
        }
        case cir::BinaryOpKind::Equal:
            return cast_value(
                builder().CreateAnd(eq(lhs_re, rhs_re), eq(lhs_im, rhs_im), "ceq"),
                llvm_type(inst.result_type), inst.loc, "ceq.cast");
        case cir::BinaryOpKind::NotEqual:
            return cast_value(
                builder().CreateOr(ne(lhs_re, rhs_re), ne(lhs_im, rhs_im), "cne"),
                llvm_type(inst.result_type), inst.loc, "cne.cast");
        default:
            error("unsupported complex binary operator", inst.loc);
            return nullptr;
    }
}

llvm::Value* Lowerer::lower_binary(const cir::Inst& inst,
                          const cir::BinaryOpDescriptor& descriptor,
                          const std::vector<cir::ValueRef>& operands) {
    llvm::Value* lhs = value_for(operands[0], inst.loc);
    llvm::Value* rhs = value_for(operands[1], inst.loc);
    if (!lhs || !rhs) {
        return nullptr;
    }
    if (descriptor.op == cir::BinaryOpKind::Comma) {
        return cast_value(rhs, llvm_type(inst.result_type), inst.loc, "comma");
    }
    if (descriptor.op == cir::BinaryOpKind::LogicalAnd) {
        return builder().CreateAnd(truth_value(lhs, inst.loc), truth_value(rhs, inst.loc), "land");
    }
    if (descriptor.op == cir::BinaryOpKind::LogicalOr) {
        return builder().CreateOr(truth_value(lhs, inst.loc), truth_value(rhs, inst.loc), "lor");
    }

    auto resolved_type_kind = [&](cir::TypeId type) -> cir::TypeKind {
        type = file_.resolved_type(type);
        return file_.valid(type) ? file_.type(type).kind : cir::TypeKind::Invalid;
    };
    if (resolved_type_kind(file_.inst(operands[0].inst).result_type) ==
        cir::TypeKind::Complex) {
        return lower_complex_binary(inst, descriptor, lhs, rhs);
    }
    auto is_pointer_type = [&](cir::TypeId type) {
        return resolved_type_kind(type) == cir::TypeKind::Pointer;
    };
    auto is_integer_type = [&](cir::TypeId type) {
        return cir::is_integer_like_type(file_, type);
    };
    auto is_comparison_op = [&]() {
        switch (descriptor.op) {
            case cir::BinaryOpKind::Less:
            case cir::BinaryOpKind::LessEqual:
            case cir::BinaryOpKind::Greater:
            case cir::BinaryOpKind::GreaterEqual:
            case cir::BinaryOpKind::Equal:
            case cir::BinaryOpKind::NotEqual:
                return true;
            default:
                return false;
        }
    };
    auto pointee_ref = [&](cir::TypeId pointer_type) {
        pointer_type = file_.resolved_type(pointer_type);
        return is_pointer_type(pointer_type)
            ? file_.pointer_pointee_ref(pointer_type)
            : cir::TypeRef{};
    };
    auto is_void_type = [&](cir::TypeId type) {
        type = file_.resolved_type(type);
        if (!file_.valid(type) || file_.type(type).kind != cir::TypeKind::Builtin) {
            return false;
        }
        const auto* builtin =
            std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(type));
        return builtin && builtin->kind == cir::BuiltinTypeKind::Void;
    };
    auto gep_element_type = [&](cir::TypeId pointer_type) -> llvm::Type* {
        cir::TypeRef pointee = pointee_ref(pointer_type);
        if (!pointee.valid() ||
            is_void_type(pointee.type) ||
            resolved_type_kind(pointee.type) == cir::TypeKind::Function) {
            return llvm::Type::getInt8Ty(context());
        }
        llvm::Type* element = llvm_type(pointee);
        return element && !element->isVoidTy() ? element : llvm::Type::getInt8Ty(context());
    };
    auto element_size = [&](cir::TypeId pointer_type) -> uint64_t {
        cir::TypeRef pointee = pointee_ref(pointer_type);
        if (!pointee.valid() ||
            is_void_type(pointee.type) ||
            resolved_type_kind(pointee.type) == cir::TypeKind::Function) {
            return 1;
        }
        std::optional<uint64_t> size = size_of_type(pointee.type, inst.loc);
        return size.value_or(1);
    };

    cir::TypeId lhs_type = file_.valid(operands[0].inst)
        ? file_.inst(operands[0].inst).result_type
        : cir::TypeId{};
    cir::TypeId rhs_type = file_.valid(operands[1].inst)
        ? file_.inst(operands[1].inst).result_type
        : cir::TypeId{};
    bool lhs_pointer = is_pointer_type(lhs_type);
    bool rhs_pointer = is_pointer_type(rhs_type);

    if (lhs_pointer && rhs_pointer && is_comparison_op()) {
        llvm::Value* out = nullptr;
        switch (descriptor.op) {
            case cir::BinaryOpKind::Less:
                out = builder().CreateICmpULT(lhs, rhs, "ptr.cmp");
                break;
            case cir::BinaryOpKind::LessEqual:
                out = builder().CreateICmpULE(lhs, rhs, "ptr.cmp");
                break;
            case cir::BinaryOpKind::Greater:
                out = builder().CreateICmpUGT(lhs, rhs, "ptr.cmp");
                break;
            case cir::BinaryOpKind::GreaterEqual:
                out = builder().CreateICmpUGE(lhs, rhs, "ptr.cmp");
                break;
            case cir::BinaryOpKind::Equal:
                out = builder().CreateICmpEQ(lhs, rhs, "ptr.cmp");
                break;
            case cir::BinaryOpKind::NotEqual:
                out = builder().CreateICmpNE(lhs, rhs, "ptr.cmp");
                break;
            default:
                break;
        }
        return cast_value(out, llvm_type(inst.result_type), inst.loc, "ptr.cmp.result");
    }

    if ((descriptor.op == cir::BinaryOpKind::Add ||
         descriptor.op == cir::BinaryOpKind::Sub) &&
        (lhs_pointer || rhs_pointer)) {
        llvm::IntegerType* intptr_type =
            llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()));

        if (descriptor.op == cir::BinaryOpKind::Sub && lhs_pointer && rhs_pointer) {
            llvm::Value* lhs_int = builder().CreatePtrToInt(lhs, intptr_type, "ptr.lhs.int");
            llvm::Value* rhs_int = builder().CreatePtrToInt(rhs, intptr_type, "ptr.rhs.int");
            llvm::Value* diff = builder().CreateSub(lhs_int, rhs_int, "ptr.diff.bytes");
            uint64_t scale = element_size(lhs_type);
            if (scale > 1) {
                diff = builder().CreateSDiv(
                    diff,
                    llvm::ConstantInt::get(intptr_type, scale, false),
                    "ptr.diff");
            }
            return cast_value(diff, llvm_type(inst.result_type), inst.loc, "ptr.diff.result");
        }

        if (descriptor.op == cir::BinaryOpKind::Sub && !lhs_pointer) {
            error("pointer subtraction requires pointer lhs", inst.loc);
            return nullptr;
        }

        llvm::Value* pointer = lhs_pointer ? lhs : rhs;
        llvm::Value* index = lhs_pointer ? rhs : lhs;
        cir::TypeId pointer_type = lhs_pointer ? lhs_type : rhs_type;
        cir::TypeId index_type = lhs_pointer ? rhs_type : lhs_type;
        if (!is_integer_type(index_type)) {
            error("pointer arithmetic requires an integer index", inst.loc);
            return nullptr;
        }
        index = cast_value(index, intptr_type, inst.loc, "ptr.index");
        if (!index) {
            return nullptr;
        }
        if (descriptor.op == cir::BinaryOpKind::Sub) {
            index = builder().CreateNeg(index, "ptr.neg_index");
        }
        llvm::Value* out =
            builder().CreateGEP(gep_element_type(pointer_type), pointer, index, "ptr.gep");
        return cast_value(out, llvm_type(inst.result_type), inst.loc, "ptr.result");
    }

    llvm::Type* computation_type = descriptor.computation_type.valid()
        ? llvm_type(descriptor.computation_type)
        : lhs->getType();
    lhs = cast_value(lhs, computation_type, inst.loc, "binary.lhs.cast");
    rhs = cast_value(rhs, computation_type, inst.loc, "binary.rhs.cast");
    if (!lhs || !rhs) {
        return nullptr;
    }

    cir::OperatorValueDomain domain = file_.operator_value_domain(descriptor.computation_type);
    bool fp = domain == cir::OperatorValueDomain::Floating ||
              lhs->getType()->isFloatingPointTy();
    bool use_unsigned =
        domain == cir::OperatorValueDomain::UnsignedInteger ||
        domain == cir::OperatorValueDomain::Bool;
    llvm::Value* out = nullptr;
    switch (descriptor.op) {
        case cir::BinaryOpKind::Add:
            out = fp ? builder().CreateFAdd(lhs, rhs, "fadd") : builder().CreateAdd(lhs, rhs, "add");
            break;
        case cir::BinaryOpKind::Sub:
            out = fp ? builder().CreateFSub(lhs, rhs, "fsub") : builder().CreateSub(lhs, rhs, "sub");
            break;
        case cir::BinaryOpKind::Mul:
            out = fp ? builder().CreateFMul(lhs, rhs, "fmul") : builder().CreateMul(lhs, rhs, "mul");
            break;
        case cir::BinaryOpKind::Div:
            out = fp ? builder().CreateFDiv(lhs, rhs, "fdiv")
                     : (use_unsigned ? builder().CreateUDiv(lhs, rhs, "udiv")
                                     : builder().CreateSDiv(lhs, rhs, "div"));
            break;
        case cir::BinaryOpKind::Mod:
            out = fp ? builder().CreateFRem(lhs, rhs, "frem")
                     : (use_unsigned ? builder().CreateURem(lhs, rhs, "urem")
                                     : builder().CreateSRem(lhs, rhs, "rem"));
            break;
        case cir::BinaryOpKind::BitAnd:
            out = builder().CreateAnd(lhs, rhs, "and");
            break;
        case cir::BinaryOpKind::BitOr:
            out = builder().CreateOr(lhs, rhs, "or");
            break;
        case cir::BinaryOpKind::BitXor:
            out = builder().CreateXor(lhs, rhs, "xor");
            break;
        case cir::BinaryOpKind::Shl:
            out = builder().CreateShl(lhs, rhs, "shl");
            break;
        case cir::BinaryOpKind::Shr:
            out = use_unsigned ? builder().CreateLShr(lhs, rhs, "lshr")
                               : builder().CreateAShr(lhs, rhs, "shr");
            break;
        case cir::BinaryOpKind::Less:
            out = fp ? builder().CreateFCmpOLT(lhs, rhs, "cmp")
                     : (use_unsigned ? builder().CreateICmpULT(lhs, rhs, "cmp")
                                     : builder().CreateICmpSLT(lhs, rhs, "cmp"));
            break;
        case cir::BinaryOpKind::LessEqual:
            out = fp ? builder().CreateFCmpOLE(lhs, rhs, "cmp")
                     : (use_unsigned ? builder().CreateICmpULE(lhs, rhs, "cmp")
                                     : builder().CreateICmpSLE(lhs, rhs, "cmp"));
            break;
        case cir::BinaryOpKind::Greater:
            out = fp ? builder().CreateFCmpOGT(lhs, rhs, "cmp")
                     : (use_unsigned ? builder().CreateICmpUGT(lhs, rhs, "cmp")
                                     : builder().CreateICmpSGT(lhs, rhs, "cmp"));
            break;
        case cir::BinaryOpKind::GreaterEqual:
            out = fp ? builder().CreateFCmpOGE(lhs, rhs, "cmp")
                     : (use_unsigned ? builder().CreateICmpUGE(lhs, rhs, "cmp")
                                     : builder().CreateICmpSGE(lhs, rhs, "cmp"));
            break;
        case cir::BinaryOpKind::Equal:
            out = fp ? builder().CreateFCmpOEQ(lhs, rhs, "cmp") : builder().CreateICmpEQ(lhs, rhs, "cmp");
            break;
        case cir::BinaryOpKind::NotEqual:

            out = fp ? builder().CreateFCmpUNE(lhs, rhs, "cmp") : builder().CreateICmpNE(lhs, rhs, "cmp");
            break;
        case cir::BinaryOpKind::Invalid:
        case cir::BinaryOpKind::LogicalAnd:
        case cir::BinaryOpKind::LogicalOr:
        case cir::BinaryOpKind::Comma:
            break;
    }

    if (!out) {
        error("unsupported binary operator '" +
                  std::string(cir::binary_op_spelling(descriptor.op)) + "'",
              inst.loc);
        return nullptr;
    }
    return cast_value(out, llvm_type(inst.result_type), inst.loc, "binary.result");
}

llvm::Value* Lowerer::lower_builtin_call(const cir::Inst& inst,
                                         const cir::BuiltinCallPayload& payload,
                                         const std::vector<cir::ValueRef>& operands) {
    auto arg = [&](size_t index) -> llvm::Value* {
        if (index >= operands.size()) {
            error("builtin '" + payload.name + "' has too few operands", inst.loc);
            return nullptr;
        }
        return value_for(operands[index], inst.loc);
    };
    auto intrinsic = [&](llvm::Intrinsic::ID id, llvm::Type* type) {
        return llvm::Intrinsic::getOrInsertDeclaration(&module(), id, {type});
    };
    auto continue_after_terminator = [&](std::string_view name) {
        if (!current_function_) {
            return;
        }
        llvm::BasicBlock* next =
            llvm::BasicBlock::Create(context(),
                                     llvm::StringRef(name.data(), name.size()),
                                     current_function_);
        builder().SetInsertPoint(next);
    };

    switch (payload.kind) {
        case BuiltinKind::IS_CONSTANT_EVALUATED:

            return llvm::ConstantInt::get(llvm_type(inst.result_type), 0);
        case BuiltinKind::BIT_CAST: {
            llvm::Value* source = arg(0);
            if (!source || operands.empty() ||
                !file_.valid(operands.front().inst)) {
                return nullptr;
            }
            cir::TypeId source_type =
                file_.inst(operands.front().inst).result_type;
            std::optional<cir::TypeSizeAlign> source_layout =
                cir::size_align_of_type(file_, source_type);
            std::optional<cir::TypeSizeAlign> target_layout =
                cir::size_align_of_type(file_, inst.result_type);
            if (!source_layout || !target_layout ||
                source_layout->size_bytes != target_layout->size_bytes) {
                error("__builtin_bit_cast requires equally sized complete types",
                      inst.loc);
                return nullptr;
            }

            llvm::Type* source_llvm_type = llvm_type(source_type);
            llvm::Type* target_llvm_type = llvm_type(inst.result_type);
            llvm::AllocaInst* source_storage =
                create_entry_alloca(source_llvm_type, "bit_cast.source");
            llvm::AllocaInst* target_storage =
                create_entry_alloca(target_llvm_type, "bit_cast.target");
            llvm::Align source_align(
                std::max<size_t>(1, source_layout->alignment_bytes));
            llvm::Align target_align(
                std::max<size_t>(1, target_layout->alignment_bytes));
            source_storage->setAlignment(source_align);
            target_storage->setAlignment(target_align);
            llvm::StoreInst* store =
                builder().CreateStore(source, source_storage);
            store->setAlignment(source_align);
            builder().CreateMemCpy(target_storage,
                                   llvm::MaybeAlign(target_align),
                                   source_storage,
                                   llvm::MaybeAlign(source_align),
                                   static_cast<uint64_t>(
                                       source_layout->size_bytes));
            llvm::LoadInst* result = builder().CreateLoad(
                target_llvm_type, target_storage, "bit_cast");
            result->setAlignment(target_align);
            return result;
        }
        case BuiltinKind::CONVERTVECTOR: {
            llvm::Value* value = arg(0);
            if (!value) {
                return nullptr;
            }
            cir::TypeId source_type = !operands.empty() && file_.valid(operands[0].inst)
                ? file_.inst(operands[0].inst).result_type
                : cir::TypeId{};
            return cast_value(value,
                              source_type,
                              inst.result_type,
                              inst.loc,
                              "convertvector");
        }
        case BuiltinKind::REDUCE_AND: {
            llvm::Value* value = arg(0);
            auto* vector_type = value
                ? llvm::dyn_cast<llvm::FixedVectorType>(value->getType())
                : nullptr;
            if (!vector_type ||
                !vector_type->getElementType()->isIntegerTy()) {
                error("__builtin_reduce_and operand must be an integer vector",
                      inst.loc);
                return nullptr;
            }
            return builder().CreateAndReduce(value);
        }
        case BuiltinKind::SHUFFLEVECTOR: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            if (!lhs || !rhs) {
                return nullptr;
            }
            auto* result_vector =
                llvm::dyn_cast<llvm::FixedVectorType>(llvm_type(inst.result_type));
            if (!result_vector) {
                error("__builtin_shufflevector result must be a fixed vector", inst.loc);
                return nullptr;
            }
            std::vector<int> mask;
            mask.reserve(payload.integer_operands.size());
            auto* lhs_vector = llvm::dyn_cast<llvm::FixedVectorType>(lhs->getType());
            auto* rhs_vector = llvm::dyn_cast<llvm::FixedVectorType>(rhs->getType());
            if (!lhs_vector || !rhs_vector) {
                error("__builtin_shufflevector operands must be fixed vectors", inst.loc);
                return nullptr;
            }
            int64_t lane_limit =
                static_cast<int64_t>(lhs_vector->getNumElements() +
                                     rhs_vector->getNumElements());
            for (int64_t lane : payload.integer_operands) {
                if (lane < -1 || lane >= lane_limit) {
                    error("__builtin_shufflevector mask lane is out of range", inst.loc);
                    return nullptr;
                }
                mask.push_back(static_cast<int>(lane));
            }
            if (mask.size() != result_vector->getNumElements()) {
                error("__builtin_shufflevector mask length does not match result type",
                      inst.loc);
                return nullptr;
            }
            return builder().CreateShuffleVector(lhs, rhs, mask, "shufflevector");
        }
        case BuiltinKind::EXPECT:
        case BuiltinKind::EXPECT_WITH_PROBABILITY: {
            llvm::Value* value = arg(0);
            llvm::Value* expected = arg(1);
            if (!value || !expected) {
                return nullptr;
            }
            if (!value->getType()->isIntegerTy()) {
                return cast_value(value, llvm_type(inst.result_type), inst.loc, "expect.result");
            }
            expected = cast_value(expected, value->getType(), inst.loc, "expect.expected");
            if (!expected) {
                return nullptr;
            }
            llvm::Function* expect_fn =
                intrinsic(llvm::Intrinsic::expect, value->getType());
            llvm::Value* hinted =
                builder().CreateCall(expect_fn, {value, expected}, "expect");
            return cast_value(hinted, llvm_type(inst.result_type), inst.loc, "expect.result");
        }
        case BuiltinKind::CONSTANT_P: {

            llvm::Value* value = arg(0);
            if (!value) {
                return nullptr;
            }
            llvm::Function* is_constant_fn =
                intrinsic(llvm::Intrinsic::is_constant, value->getType());
            llvm::Value* result =
                builder().CreateCall(is_constant_fn, {value}, "is.constant");
            return cast_value(result, llvm_type(inst.result_type), inst.loc,
                              "constant_p.result");
        }
        case BuiltinKind::ASSUME_ALIGNED: {
            llvm::Value* pointer = arg(0);
            if (!pointer || !pointer->getType()->isPointerTy() ||
                payload.integer_operands.size() != 1) {
                error("__builtin_assume_aligned has invalid operands", inst.loc);
                return nullptr;
            }
            llvm::Value* alignment = llvm::ConstantInt::get(
                llvm::Type::getInt64Ty(context()),
                static_cast<uint64_t>(payload.integer_operands.front()));
            llvm::Value* offset =
                operands.size() == 2 ? arg(1) : nullptr;
            builder().CreateAlignmentAssumption(
                module().getDataLayout(), pointer, alignment, offset);
            return cast_value(pointer, llvm_type(inst.result_type), inst.loc,
                              "assume_aligned.result");
        }
        case BuiltinKind::LAUNDER: {
            llvm::Value* pointer = arg(0);
            if (!pointer || !pointer->getType()->isPointerTy()) {
                error("__builtin_launder has an invalid operand", inst.loc);
                return nullptr;
            }
            // Clang lowers the source-level optimization barrier to the
            // unchanged pointer. Keeping it as a distinct CIR instruction
            // prevents frontend folding across the barrier; Aburi does not
            // attach LLVM invariant-group metadata that would require an
            // LLVM-side launder intrinsic.
            return cast_value(pointer, llvm_type(inst.result_type), inst.loc,
                              "launder.result");
        }
        case BuiltinKind::UNREACHABLE:
            builder().CreateUnreachable();
            continue_after_terminator("after.unreachable");
            return nullptr;
        case BuiltinKind::TRAP: {
            llvm::Function* trap_fn =
                llvm::Intrinsic::getOrInsertDeclaration(&module(),
                                                        llvm::Intrinsic::trap);
            builder().CreateCall(trap_fn);
            builder().CreateUnreachable();
            continue_after_terminator("after.trap");
            return nullptr;
        }
        case BuiltinKind::MEMCPY: {
            llvm::Value* dst = arg(0);
            llvm::Value* src = arg(1);
            llvm::Value* size = arg(2);
            if (!dst || !src || !size) {
                return nullptr;
            }
            builder().CreateMemCpy(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
            return cast_value(dst, llvm_type(inst.result_type), inst.loc, "memcpy.result");
        }
        case BuiltinKind::MEMMOVE: {
            llvm::Value* dst = arg(0);
            llvm::Value* src = arg(1);
            llvm::Value* size = arg(2);
            if (!dst || !src || !size) {
                return nullptr;
            }
            builder().CreateMemMove(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
            return cast_value(dst, llvm_type(inst.result_type), inst.loc, "memmove.result");
        }
        case BuiltinKind::MEMSET: {
            llvm::Value* dst = arg(0);
            llvm::Value* value = arg(1);
            llvm::Value* size = arg(2);
            if (!dst || !value || !size) {
                return nullptr;
            }
            value = cast_value(value, llvm::Type::getInt8Ty(context()), inst.loc, "memset.value");
            if (!value) {
                return nullptr;
            }
            builder().CreateMemSet(dst, value, size, llvm::MaybeAlign(1));
            return cast_value(dst, llvm_type(inst.result_type), inst.loc, "memset.result");
        }
        case BuiltinKind::CLZ:
        case BuiltinKind::CLZL:
        case BuiltinKind::CLZLL:
        case BuiltinKind::CLZG:
        case BuiltinKind::CTZ:
        case BuiltinKind::CTZL:
        case BuiltinKind::CTZLL:
        case BuiltinKind::CTZG:
        case BuiltinKind::POPCOUNT:
        case BuiltinKind::POPCOUNTL:
        case BuiltinKind::POPCOUNTLL:
        case BuiltinKind::POPCOUNTG: {
            llvm::Value* value = arg(0);
            if (!value) {
                return nullptr;
            }
            if (!value->getType()->isIntegerTy()) {
                error("bit builtin requires an integer operand", inst.loc);
                return nullptr;
            }
            llvm::Intrinsic::ID id = llvm::Intrinsic::ctpop;
            std::vector<llvm::Value*> call_args{value};
            bool generic_count_zero =
                payload.kind == BuiltinKind::CLZG ||
                payload.kind == BuiltinKind::CTZG;
            if (payload.kind == BuiltinKind::CLZ ||
                payload.kind == BuiltinKind::CLZL ||
                payload.kind == BuiltinKind::CLZLL ||
                payload.kind == BuiltinKind::CLZG) {
                id = llvm::Intrinsic::ctlz;
                call_args.push_back(llvm::ConstantInt::get(
                    llvm::Type::getInt1Ty(context()),
                    generic_count_zero && operands.size() == 1));
            } else if (payload.kind == BuiltinKind::CTZ ||
                       payload.kind == BuiltinKind::CTZL ||
                       payload.kind == BuiltinKind::CTZLL ||
                       payload.kind == BuiltinKind::CTZG) {
                id = llvm::Intrinsic::cttz;
                call_args.push_back(llvm::ConstantInt::get(
                    llvm::Type::getInt1Ty(context()),
                    generic_count_zero && operands.size() == 1));
            }
            llvm::Function* fn = intrinsic(id, value->getType());
            llvm::Value* lowered = builder().CreateCall(fn, call_args, "bit.builtin");
            llvm::Value* result = cast_value(
                lowered, llvm_type(inst.result_type), inst.loc, "bit.result");
            if (!result || !generic_count_zero || operands.size() == 1) {
                return result;
            }
            llvm::Value* fallback = arg(1);
            fallback = cast_value(fallback,
                                  result->getType(),
                                  inst.loc,
                                  "bit.fallback");
            if (!fallback) {
                return nullptr;
            }
            llvm::Value* is_zero = builder().CreateICmpEQ(
                value,
                llvm::ConstantInt::get(value->getType(), 0),
                "bit.is_zero");
            return builder().CreateSelect(
                is_zero, fallback, result, "bit.zero_fallback");
        }
        case BuiltinKind::FFS:
        case BuiltinKind::FFSL:
        case BuiltinKind::FFSLL: {
            llvm::Value* value = arg(0);
            if (!value) {
                return nullptr;
            }
            if (!value->getType()->isIntegerTy()) {
                error("ffs builtin requires an integer operand", inst.loc);
                return nullptr;
            }
            llvm::Function* cttz_fn = intrinsic(llvm::Intrinsic::cttz, value->getType());
            llvm::Value* trailing =
                builder().CreateCall(cttz_fn,
                                     {value, llvm::ConstantInt::getFalse(context())},
                                     "ffs.cttz");
            llvm::Value* one = llvm::ConstantInt::get(value->getType(), 1);
            llvm::Value* one_based = builder().CreateAdd(trailing, one, "ffs.one_based");
            llvm::Value* zero =
                llvm::ConstantInt::get(value->getType(), 0);
            llvm::Value* is_zero = builder().CreateICmpEQ(value, zero, "ffs.is_zero");
            llvm::Value* selected = builder().CreateSelect(is_zero, zero, one_based, "ffs");
            return cast_value(selected, llvm_type(inst.result_type), inst.loc, "ffs.result");
        }
        case BuiltinKind::BSWAP16:
        case BuiltinKind::BSWAP32:
        case BuiltinKind::BSWAP64: {
            llvm::Value* value = arg(0);
            if (!value) {
                return nullptr;
            }
            unsigned bits = payload.kind == BuiltinKind::BSWAP16
                ? 16
                : (payload.kind == BuiltinKind::BSWAP32 ? 32 : 64);
            llvm::Type* integer_type = llvm::IntegerType::get(context(), bits);
            value = cast_value(value, integer_type, inst.loc, "bswap.arg");
            if (!value) {
                return nullptr;
            }
            llvm::Function* bswap_fn = intrinsic(llvm::Intrinsic::bswap, integer_type);
            llvm::Value* swapped = builder().CreateCall(bswap_fn, {value}, "bswap");
            return cast_value(swapped, llvm_type(inst.result_type), inst.loc, "bswap.result");
        }
        case BuiltinKind::ALLOCA: {
            llvm::Value* size = arg(0);
            if (!size) {
                return nullptr;
            }
            llvm::AllocaInst* stack = builder().CreateAlloca(
                llvm::Type::getInt8Ty(context()), size, "alloca");
            stack->setAlignment(llvm::Align(16));
            return stack;
        }
        case BuiltinKind::RETURN_ADDRESS:
        case BuiltinKind::FRAME_ADDRESS: {
            llvm::Value* level = arg(0);
            if (!level) {
                return nullptr;
            }
            level = cast_value(level, llvm::Type::getInt32Ty(context()), inst.loc,
                               "addr.level");
            llvm::Function* fn = payload.kind == BuiltinKind::RETURN_ADDRESS
                ? llvm::Intrinsic::getOrInsertDeclaration(
                      &module(), llvm::Intrinsic::returnaddress)
                : llvm::Intrinsic::getOrInsertDeclaration(
                      &module(),
                      llvm::Intrinsic::frameaddress,
                      {llvm::PointerType::get(context(), 0)});
            return builder().CreateCall(fn, {level}, "builtin.addr");
        }
        case BuiltinKind::CPOW: {
            llvm::Type* complex_type = llvm_type(inst.result_type);
            llvm::FunctionType* cpow_type = llvm::FunctionType::get(
                complex_type, {complex_type, complex_type}, false);
            llvm::FunctionCallee cpow_fn =
                module().getOrInsertFunction("cpow", cpow_type);
            llvm::Value* base = arg(0);
            llvm::Value* exponent = arg(1);
            if (!base || !exponent) {
                return nullptr;
            }
            return builder().CreateCall(cpow_fn, {base, exponent}, "cpow");
        }
        case BuiltinKind::STRLEN: {
            llvm::Value* pointer = arg(0);
            if (!pointer) {
                return nullptr;
            }
            llvm::FunctionCallee callee = module().getOrInsertFunction(
                "strlen",
                llvm::FunctionType::get(llvm_type(inst.result_type),
                                        {llvm::PointerType::get(context(), 0)},
                                        false));
            return builder().CreateCall(callee, {pointer}, "strlen");
        }
        case BuiltinKind::ABS:
        case BuiltinKind::LABS:
        case BuiltinKind::LLABS: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isIntegerTy()) {
                return nullptr;
            }
            llvm::Function* abs_fn = intrinsic(llvm::Intrinsic::abs, value->getType());
            return builder().CreateCall(
                abs_fn, {value, llvm::ConstantInt::getFalse(context())}, "abs");
        }
        case BuiltinKind::FABS: case BuiltinKind::FABSF: case BuiltinKind::FABSL:
        case BuiltinKind::SQRT: case BuiltinKind::SQRTF: case BuiltinKind::SQRTL:
        case BuiltinKind::SIN: case BuiltinKind::SINF: case BuiltinKind::SINL:
        case BuiltinKind::COS: case BuiltinKind::COSF: case BuiltinKind::COSL:
        case BuiltinKind::EXP: case BuiltinKind::EXPF: case BuiltinKind::EXPL:
        case BuiltinKind::EXP2: case BuiltinKind::EXP2F: case BuiltinKind::EXP2L:
        case BuiltinKind::LOG: case BuiltinKind::LOGF: case BuiltinKind::LOGL:
        case BuiltinKind::LOG2: case BuiltinKind::LOG2F: case BuiltinKind::LOG2L:
        case BuiltinKind::LOG10: case BuiltinKind::LOG10F: case BuiltinKind::LOG10L:
        case BuiltinKind::FLOOR: case BuiltinKind::FLOORF: case BuiltinKind::FLOORL:
        case BuiltinKind::CEIL: case BuiltinKind::CEILF: case BuiltinKind::CEILL:
        case BuiltinKind::TRUNC: case BuiltinKind::TRUNCF: case BuiltinKind::TRUNCL:
        case BuiltinKind::RINT: case BuiltinKind::RINTF: case BuiltinKind::RINTL:
        case BuiltinKind::NEARBYINT: case BuiltinKind::NEARBYINTF:
        case BuiltinKind::NEARBYINTL:
        case BuiltinKind::ROUND: case BuiltinKind::ROUNDF: case BuiltinKind::ROUNDL: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isFloatingPointTy()) {
                return nullptr;
            }
            llvm::Intrinsic::ID id = llvm::Intrinsic::fabs;
            switch (payload.kind) {
                case BuiltinKind::SQRT: case BuiltinKind::SQRTF: case BuiltinKind::SQRTL:
                    id = llvm::Intrinsic::sqrt; break;
                case BuiltinKind::SIN: case BuiltinKind::SINF: case BuiltinKind::SINL:
                    id = llvm::Intrinsic::sin; break;
                case BuiltinKind::COS: case BuiltinKind::COSF: case BuiltinKind::COSL:
                    id = llvm::Intrinsic::cos; break;
                case BuiltinKind::EXP: case BuiltinKind::EXPF: case BuiltinKind::EXPL:
                    id = llvm::Intrinsic::exp; break;
                case BuiltinKind::EXP2: case BuiltinKind::EXP2F: case BuiltinKind::EXP2L:
                    id = llvm::Intrinsic::exp2; break;
                case BuiltinKind::LOG: case BuiltinKind::LOGF: case BuiltinKind::LOGL:
                    id = llvm::Intrinsic::log; break;
                case BuiltinKind::LOG2: case BuiltinKind::LOG2F: case BuiltinKind::LOG2L:
                    id = llvm::Intrinsic::log2; break;
                case BuiltinKind::LOG10: case BuiltinKind::LOG10F: case BuiltinKind::LOG10L:
                    id = llvm::Intrinsic::log10; break;
                case BuiltinKind::FLOOR: case BuiltinKind::FLOORF: case BuiltinKind::FLOORL:
                    id = llvm::Intrinsic::floor; break;
                case BuiltinKind::CEIL: case BuiltinKind::CEILF: case BuiltinKind::CEILL:
                    id = llvm::Intrinsic::ceil; break;
                case BuiltinKind::TRUNC: case BuiltinKind::TRUNCF: case BuiltinKind::TRUNCL:
                    id = llvm::Intrinsic::trunc; break;
                case BuiltinKind::RINT: case BuiltinKind::RINTF: case BuiltinKind::RINTL:
                    id = llvm::Intrinsic::rint; break;
                case BuiltinKind::NEARBYINT: case BuiltinKind::NEARBYINTF:
                case BuiltinKind::NEARBYINTL:
                    id = llvm::Intrinsic::nearbyint; break;
                case BuiltinKind::ROUND: case BuiltinKind::ROUNDF: case BuiltinKind::ROUNDL:
                    id = llvm::Intrinsic::round; break;
                default: break;
            }
            llvm::Function* fn = intrinsic(id, value->getType());
            return builder().CreateCall(fn, {value}, "fp.builtin");
        }
        case BuiltinKind::POW: case BuiltinKind::POWF: case BuiltinKind::POWL:
        case BuiltinKind::COPYSIGN: case BuiltinKind::COPYSIGNF:
        case BuiltinKind::COPYSIGNL:
        case BuiltinKind::FMIN: case BuiltinKind::FMINF: case BuiltinKind::FMINL:
        case BuiltinKind::FMAX: case BuiltinKind::FMAXF: case BuiltinKind::FMAXL: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            if (!lhs || !rhs || !lhs->getType()->isFloatingPointTy()) {
                return nullptr;
            }
            llvm::Intrinsic::ID id = llvm::Intrinsic::pow;
            switch (payload.kind) {
                case BuiltinKind::COPYSIGN: case BuiltinKind::COPYSIGNF:
                case BuiltinKind::COPYSIGNL:
                    id = llvm::Intrinsic::copysign; break;
                case BuiltinKind::FMIN: case BuiltinKind::FMINF: case BuiltinKind::FMINL:
                    id = llvm::Intrinsic::minnum; break;
                case BuiltinKind::FMAX: case BuiltinKind::FMAXF: case BuiltinKind::FMAXL:
                    id = llvm::Intrinsic::maxnum; break;
                default: break;
            }
            llvm::Function* fn = intrinsic(id, lhs->getType());
            return builder().CreateCall(fn, {lhs, rhs}, "fp.builtin2");
        }
        case BuiltinKind::FMA: case BuiltinKind::FMAF: case BuiltinKind::FMAL: {
            llvm::Value* a = arg(0);
            llvm::Value* b = arg(1);
            llvm::Value* c = arg(2);
            if (!a || !b || !c) {
                return nullptr;
            }
            llvm::Function* fn = intrinsic(llvm::Intrinsic::fma, a->getType());
            return builder().CreateCall(fn, {a, b, c}, "fma");
        }
        case BuiltinKind::FMOD: case BuiltinKind::FMODF: case BuiltinKind::FMODL: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            if (!lhs || !rhs) {
                return nullptr;
            }
            return builder().CreateFRem(lhs, rhs, "fmod");
        }
        case BuiltinKind::ISNAN: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isFloatingPointTy()) {
                return nullptr;
            }
            llvm::Value* unordered = builder().CreateFCmpUNO(value, value, "isnan");
            return cast_value(unordered, llvm_type(inst.result_type), inst.loc,
                              "isnan.result");
        }
        case BuiltinKind::ISINF:
        case BuiltinKind::ISINF_SIGN: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isFloatingPointTy()) {
                return nullptr;
            }
            llvm::Function* fabs_fn = intrinsic(llvm::Intrinsic::fabs, value->getType());
            llvm::Value* magnitude = builder().CreateCall(fabs_fn, {value}, "isinf.mag");
            llvm::Value* infinity =
                llvm::ConstantFP::getInfinity(value->getType(), false);
            llvm::Value* is_inf =
                builder().CreateFCmpOEQ(magnitude, infinity, "isinf");
            if (payload.kind == BuiltinKind::ISINF) {
                return cast_value(is_inf, llvm_type(inst.result_type), inst.loc,
                                  "isinf.result");
            }
            llvm::Type* result_type = llvm_type(inst.result_type);
            llvm::Value* negative = builder().CreateFCmpOLT(
                value, llvm::ConstantFP::getZero(value->getType()), "isinf.neg");
            llvm::Value* signed_one = builder().CreateSelect(
                negative,
                llvm::ConstantInt::getSigned(result_type, -1),
                llvm::ConstantInt::get(result_type, 1),
                "isinf.sign");
            return builder().CreateSelect(
                is_inf, signed_one, llvm::ConstantInt::get(result_type, 0),
                "isinf_sign");
        }
        case BuiltinKind::ISNORMAL:
        case BuiltinKind::ISFINITE: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isFloatingPointTy()) {
                return nullptr;
            }

            unsigned mask = payload.kind == BuiltinKind::ISNORMAL ? 0x108u : 0x1f8u;
            llvm::Function* fn =
                intrinsic(llvm::Intrinsic::is_fpclass, value->getType());
            llvm::Value* classified = builder().CreateCall(
                fn,
                {value,
                 llvm::ConstantInt::get(llvm::Type::getInt32Ty(context()), mask)},
                "fpclass");
            return cast_value(classified, llvm_type(inst.result_type), inst.loc,
                              "fpclass.result");
        }
        case BuiltinKind::CLRSB:
        case BuiltinKind::CLRSBL:
        case BuiltinKind::CLRSBLL: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isIntegerTy()) {
                return nullptr;
            }
            unsigned bits = value->getType()->getIntegerBitWidth();
            llvm::Value* sign_spread = builder().CreateAShr(
                value, llvm::ConstantInt::get(value->getType(), bits - 1),
                "clrsb.sign");
            llvm::Value* folded = builder().CreateXor(value, sign_spread, "clrsb.fold");
            llvm::Function* ctlz_fn = intrinsic(llvm::Intrinsic::ctlz, value->getType());
            llvm::Value* leading = builder().CreateCall(
                ctlz_fn, {folded, llvm::ConstantInt::getFalse(context())},
                "clrsb.ctlz");
            llvm::Value* redundant = builder().CreateSub(
                leading, llvm::ConstantInt::get(value->getType(), 1), "clrsb");
            return cast_value(redundant, llvm_type(inst.result_type), inst.loc,
                              "clrsb.result");
        }
        case BuiltinKind::PARITY:
        case BuiltinKind::PARITYL:
        case BuiltinKind::PARITYLL: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isIntegerTy()) {
                return nullptr;
            }
            llvm::Function* ctpop_fn =
                intrinsic(llvm::Intrinsic::ctpop, value->getType());
            llvm::Value* ones = builder().CreateCall(ctpop_fn, {value}, "parity.pop");
            llvm::Value* parity = builder().CreateAnd(
                ones, llvm::ConstantInt::get(value->getType(), 1), "parity");
            return cast_value(parity, llvm_type(inst.result_type), inst.loc,
                              "parity.result");
        }
        case BuiltinKind::IA32_BZHI_SI: {
            llvm::Value* source = arg(0);
            llvm::Value* index = arg(1);
            if (!source || !index) {
                return nullptr;
            }
            llvm::Type* u32 = llvm::Type::getInt32Ty(context());
            source = cast_value(source, u32, inst.loc, "bzhi.src");
            index = cast_value(index, u32, inst.loc, "bzhi.idx");
            llvm::Value* n = builder().CreateAnd(
                index, llvm::ConstantInt::get(u32, 0xff), "bzhi.n");
            llvm::Value* one = llvm::ConstantInt::get(u32, 1);
            llvm::Value* clamped = builder().CreateAnd(
                n, llvm::ConstantInt::get(u32, 31), "bzhi.clamp");
            llvm::Value* mask = builder().CreateSub(
                builder().CreateShl(one, clamped, "bzhi.shl"), one, "bzhi.mask");
            llvm::Value* masked = builder().CreateAnd(source, mask, "bzhi.and");
            llvm::Value* wide = builder().CreateICmpUGE(
                n, llvm::ConstantInt::get(u32, 32), "bzhi.wide");
            llvm::Value* selected =
                builder().CreateSelect(wide, source, masked, "bzhi");
            return cast_value(selected, llvm_type(inst.result_type), inst.loc,
                              "bzhi.result");
        }
        case BuiltinKind::ADD_OVERFLOW:
        case BuiltinKind::SUB_OVERFLOW:
        case BuiltinKind::MUL_OVERFLOW: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            llvm::Value* destination = arg(2);
            if (!lhs || !rhs || !destination ||
                !lhs->getType()->isIntegerTy() || !rhs->getType()->isIntegerTy()) {
                return nullptr;
            }

            auto signedness = [&](size_t index) {
                cir::TypeId type = file_.valid(operands[index].inst)
                    ? file_.inst(operands[index].inst).result_type
                    : cir::TypeId{};
                return !cir::integer_shape_for_type(file_, type).is_unsigned;
            };
            llvm::Type* i128 = llvm::IntegerType::get(context(), 128);
            llvm::Value* wide_lhs = signedness(0)
                ? builder().CreateSExt(lhs, i128, "ovf.lhs")
                : builder().CreateZExt(lhs, i128, "ovf.lhs");
            llvm::Value* wide_rhs = signedness(1)
                ? builder().CreateSExt(rhs, i128, "ovf.rhs")
                : builder().CreateZExt(rhs, i128, "ovf.rhs");
            llvm::Value* wide_result = payload.kind == BuiltinKind::ADD_OVERFLOW
                ? builder().CreateAdd(wide_lhs, wide_rhs, "ovf.add")
                : payload.kind == BuiltinKind::SUB_OVERFLOW
                    ? builder().CreateSub(wide_lhs, wide_rhs, "ovf.sub")
                    : builder().CreateMul(wide_lhs, wide_rhs, "ovf.mul");
            cir::TypeId dest_pointer = file_.valid(operands[2].inst)
                ? file_.resolved_type(file_.inst(operands[2].inst).result_type)
                : cir::TypeId{};
            const auto* pointer_payload = file_.valid(dest_pointer)
                ? std::get_if<cir::PointerTypePayload>(&file_.type_payload(dest_pointer))
                : nullptr;
            if (!pointer_payload) {
                error("overflow builtin requires a pointer destination", inst.loc);
                return nullptr;
            }
            cir::TypeId dest_type = file_.resolved_type(pointer_payload->pointee.type);
            auto dest_shape = cir::integer_shape_for_type(file_, dest_type);
            llvm::Type* narrow = llvm::IntegerType::get(context(), dest_shape.bit_width);
            llvm::Value* truncated =
                builder().CreateTrunc(wide_result, narrow, "ovf.trunc");
            llvm::Value* reextended = dest_shape.is_unsigned
                ? builder().CreateZExt(truncated, i128, "ovf.reext")
                : builder().CreateSExt(truncated, i128, "ovf.reext");
            llvm::Value* overflowed =
                builder().CreateICmpNE(wide_result, reextended, "ovf.check");
            builder().CreateStore(truncated, destination);
            return cast_value(overflowed, llvm_type(inst.result_type), inst.loc,
                              "ovf.result");
        }
        case BuiltinKind::STACK_SAVE: {
            llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
                &module(), llvm::Intrinsic::stacksave,
                {llvm::PointerType::get(context(), 0)});
            return builder().CreateCall(fn, {}, "stacksave");
        }
        case BuiltinKind::STACK_RESTORE: {
            llvm::Value* saved = arg(0);
            if (!saved) {
                return nullptr;
            }
            llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
                &module(), llvm::Intrinsic::stackrestore,
                {llvm::PointerType::get(context(), 0)});
            builder().CreateCall(fn, {saved});
            return nullptr;
        }
        case BuiltinKind::PREFETCH: {
            llvm::Value* address = arg(0);
            if (!address) {
                return nullptr;
            }
            llvm::Type* i32 = llvm::Type::getInt32Ty(context());
            llvm::Value* rw = operands.size() > 1 && arg(1)
                ? cast_value(arg(1), i32, inst.loc, "prefetch.rw")
                : llvm::ConstantInt::get(i32, 0);
            llvm::Value* locality = operands.size() > 2 && arg(2)
                ? cast_value(arg(2), i32, inst.loc, "prefetch.loc")
                : llvm::ConstantInt::get(i32, 3);
            llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
                &module(), llvm::Intrinsic::prefetch,
                {llvm::PointerType::get(context(), 0)});
            builder().CreateCall(fn, {address, rw, locality,
                                      llvm::ConstantInt::get(i32, 1)});
            return nullptr;
        }
        case BuiltinKind::SIGNBIT:
        case BuiltinKind::SIGNBITF:
        case BuiltinKind::SIGNBITL: {
            llvm::Value* value = arg(0);
            if (!value || !value->getType()->isFloatingPointTy()) {
                return nullptr;
            }
            unsigned bits = value->getType()->getPrimitiveSizeInBits();
            llvm::Type* raw_type = llvm::IntegerType::get(context(), bits);
            llvm::Value* raw = builder().CreateBitCast(value, raw_type, "signbit.raw");
            llvm::Value* negative = builder().CreateICmpSLT(
                raw, llvm::ConstantInt::get(raw_type, 0), "signbit");
            return cast_value(negative, llvm_type(inst.result_type), inst.loc,
                              "signbit.result");
        }
        case BuiltinKind::ISUNORDERED:
        case BuiltinKind::ISGREATER:
        case BuiltinKind::ISLESS:
        case BuiltinKind::ISLESSEQUAL:
        case BuiltinKind::ISLESSGREATER:
        case BuiltinKind::ISGREATEREQUAL: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            if (!lhs || !rhs) {
                return nullptr;
            }
            if (lhs->getType() != rhs->getType()) {
                rhs = cast_value(rhs, lhs->getType(), inst.loc, "fpcmp.rhs");
                if (!rhs) {
                    return nullptr;
                }
            }
            llvm::Value* compared = nullptr;
            switch (payload.kind) {
                case BuiltinKind::ISUNORDERED:
                    compared = builder().CreateFCmpUNO(lhs, rhs, "isunordered");
                    break;
                case BuiltinKind::ISGREATER:
                    compared = builder().CreateFCmpOGT(lhs, rhs, "isgreater");
                    break;
                case BuiltinKind::ISLESS:
                    compared = builder().CreateFCmpOLT(lhs, rhs, "isless");
                    break;
                case BuiltinKind::ISLESSEQUAL:
                    compared = builder().CreateFCmpOLE(lhs, rhs, "islesseq");
                    break;
                case BuiltinKind::ISGREATEREQUAL:
                    compared = builder().CreateFCmpOGE(lhs, rhs, "isgreatereq");
                    break;
                default:
                    compared = builder().CreateFCmpONE(lhs, rhs, "islessgreater");
                    break;
            }
            return cast_value(compared, llvm_type(inst.result_type), inst.loc,
                              "fpcmp.result");
        }
        case BuiltinKind::FPCLASSIFY: {

            if (operands.size() < 6) {
                error("__builtin_fpclassify requires six arguments", inst.loc);
                return nullptr;
            }
            llvm::Value* value = arg(5);
            if (!value || !value->getType()->isFloatingPointTy()) {
                return nullptr;
            }
            llvm::Type* i32 = llvm::Type::getInt32Ty(context());
            llvm::Function* classify_fn =
                intrinsic(llvm::Intrinsic::is_fpclass, value->getType());
            auto classified = [&](unsigned mask, const char* label) {
                return builder().CreateCall(
                    classify_fn,
                    {value, llvm::ConstantInt::get(i32, mask)},
                    label);
            };
            llvm::Value* result = arg(0);
            llvm::Value* selected = builder().CreateSelect(
                classified(0x204u, "fpc.inf"), arg(1), result, "fpc.sel_inf");
            selected = builder().CreateSelect(
                classified(0x108u, "fpc.norm"), arg(2), selected, "fpc.sel_norm");
            selected = builder().CreateSelect(
                classified(0x090u, "fpc.subnorm"), arg(3), selected,
                "fpc.sel_subnorm");
            selected = builder().CreateSelect(
                classified(0x060u, "fpc.zero"), arg(4), selected, "fpc.sel_zero");
            return cast_value(selected, llvm_type(inst.result_type), inst.loc,
                              "fpclassify");
        }
        case BuiltinKind::CLEAR_PADDING: {
            llvm::Value* pointer = arg(0);
            if (!pointer) {
                return nullptr;
            }
            cir::TypeId pointer_type = file_.valid(operands[0].inst)
                ? file_.resolved_type(file_.inst(operands[0].inst).result_type)
                : cir::TypeId{};
            const auto* pointer_payload = file_.valid(pointer_type)
                ? std::get_if<cir::PointerTypePayload>(&file_.type_payload(pointer_type))
                : nullptr;
            cir::TypeId object_type = pointer_payload
                ? file_.resolved_type(pointer_payload->pointee.type)
                : cir::TypeId{};
            if (cir::type_has_known_no_padding(file_, object_type)) {

                return nullptr;
            }
            const auto* record_payload = file_.valid(object_type)
                ? std::get_if<cir::RecordTypePayload>(
                      &file_.type_payload(object_type))
                : nullptr;
            const cir::RecordFacts* facts = record_payload
                ? file_.record_facts(record_payload->entity)
                : nullptr;
            std::optional<size_t> total = cir::size_of_type(file_, object_type);
            if (!facts || !total.has_value()) {
                error("__builtin_clear_padding does not support this object's padding layout",
                      inst.loc);
                return nullptr;
            }

            std::vector<std::pair<size_t, size_t>> covered;
            for (const cir::RecordFieldFact& field : facts->fields) {
                if (field.subobject_size == cir::SubobjectSizeKind::Zero) {
                    continue;
                }
                std::optional<size_t> field_size =
                    cir::size_of_type(file_, field.type.type);
                if (field_size.has_value()) {
                    covered.emplace_back(field.offset, field.offset + *field_size);
                }
            }
            std::sort(covered.begin(), covered.end());
            llvm::Type* i8 = llvm::Type::getInt8Ty(context());
            size_t cursor = 0;
            auto clear_range = [&](size_t from, size_t to) {
                if (to <= from) {
                    return;
                }
                llvm::Value* base = builder().CreateConstInBoundsGEP1_64(
                    i8, pointer, from, "padding.addr");
                builder().CreateMemSet(
                    base, llvm::ConstantInt::get(i8, 0),
                    llvm::ConstantInt::get(llvm::Type::getInt64Ty(context()), to - from),
                    llvm::MaybeAlign(1));
            };
            for (const auto& range : covered) {
                if (range.first > cursor) {
                    clear_range(cursor, range.first);
                }
                cursor = std::max(cursor, range.second);
            }
            clear_range(cursor, *total);
            return nullptr;
        }
        case BuiltinKind::ISEQSIG: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            if (!lhs || !rhs) {
                return nullptr;
            }
            llvm::Value* equal = builder().CreateFCmpOEQ(lhs, rhs, "iseqsig");
            return cast_value(equal, llvm_type(inst.result_type), inst.loc,
                              "iseqsig.result");
        }
        case BuiltinKind::CLEAR_CACHE: {
            llvm::Value* begin = arg(0);
            llvm::Value* end = arg(1);
            if (!begin || !end) {
                return nullptr;
            }
            llvm::Function* fn = llvm::Intrinsic::getOrInsertDeclaration(
                &module(), llvm::Intrinsic::clear_cache);
            builder().CreateCall(fn, {begin, end});
            return nullptr;
        }
        case BuiltinKind::ADD_OVERFLOW_P:
        case BuiltinKind::SUB_OVERFLOW_P: {
            llvm::Value* lhs = arg(0);
            llvm::Value* rhs = arg(1);
            if (!lhs || !rhs || !lhs->getType()->isIntegerTy() ||
                !rhs->getType()->isIntegerTy()) {
                return nullptr;
            }
            auto operand_signedness = [&](size_t index) {
                cir::TypeId type = file_.valid(operands[index].inst)
                    ? file_.inst(operands[index].inst).result_type
                    : cir::TypeId{};
                return !cir::integer_shape_for_type(file_, type).is_unsigned;
            };
            llvm::Type* i128 = llvm::IntegerType::get(context(), 128);
            llvm::Value* wide_lhs = operand_signedness(0)
                ? builder().CreateSExt(lhs, i128, "ovfp.lhs")
                : builder().CreateZExt(lhs, i128, "ovfp.lhs");
            llvm::Value* wide_rhs = operand_signedness(1)
                ? builder().CreateSExt(rhs, i128, "ovfp.rhs")
                : builder().CreateZExt(rhs, i128, "ovfp.rhs");
            llvm::Value* wide_result = payload.kind == BuiltinKind::ADD_OVERFLOW_P
                ? builder().CreateAdd(wide_lhs, wide_rhs, "ovfp.add")
                : builder().CreateSub(wide_lhs, wide_rhs, "ovfp.sub");

            cir::TypeId dest_type = file_.valid(operands[2].inst)
                ? file_.resolved_type(file_.inst(operands[2].inst).result_type)
                : cir::TypeId{};
            auto dest_shape = cir::integer_shape_for_type(file_, dest_type);
            llvm::Value* overflowed = nullptr;
            if (dest_shape.bit_width >= 128) {

                overflowed = dest_shape.is_unsigned
                    ? builder().CreateICmpSLT(
                          wide_result, llvm::ConstantInt::get(i128, 0),
                          "ovfp.neg")
                    : llvm::ConstantInt::getFalse(context());
            } else {
                llvm::Type* narrow =
                    llvm::IntegerType::get(context(), dest_shape.bit_width);
                llvm::Value* truncated =
                    builder().CreateTrunc(wide_result, narrow, "ovfp.trunc");
                llvm::Value* reextended = dest_shape.is_unsigned
                    ? builder().CreateZExt(truncated, i128, "ovfp.reext")
                    : builder().CreateSExt(truncated, i128, "ovfp.reext");
                overflowed =
                    builder().CreateICmpNE(wide_result, reextended, "ovfp.check");
            }
            return cast_value(overflowed, llvm_type(inst.result_type), inst.loc,
                              "ovfp.result");
        }
        default: {
            if (const BuiltinLibcall* libcall = builtin_libcall(payload.kind)) {
                std::vector<llvm::Value*> call_args;
                std::vector<llvm::Type*> param_types;
                for (size_t index = 0; index + 1 < operands.size() + 1 &&
                                       index < operands.size(); ++index) {
                    llvm::Value* value = arg(index);
                    if (!value) {
                        return nullptr;
                    }
                    call_args.push_back(value);
                    param_types.push_back(value->getType());
                }
                llvm::Type* return_type = llvm_type(inst.result_type);
                if (!return_type) {
                    return nullptr;
                }

                bool callee_is_variadic =
                    std::strchr(libcall->signature, '.') != nullptr;
                if (callee_is_variadic) {
                    size_t fixed = std::strlen(libcall->signature) - 2;
                    if (param_types.size() > fixed) {
                        param_types.resize(fixed);
                    }
                }
                llvm::FunctionCallee callee = module().getOrInsertFunction(
                    libcall->callee,
                    llvm::FunctionType::get(return_type, param_types,
                                            callee_is_variadic));
                llvm::CallInst* call = builder().CreateCall(
                    callee, call_args,
                    return_type->isVoidTy() ? "" : libcall->callee);
                if (payload.kind == BuiltinKind::MEMCMP_EQ) {
                    llvm::Value* equal = builder().CreateICmpEQ(
                        call, llvm::ConstantInt::get(call->getType(), 0),
                        "memcmp_eq");
                    return cast_value(equal, llvm_type(inst.result_type),
                                      inst.loc, "memcmp_eq.result");
                }
                return return_type->isVoidTy() ? nullptr : call;
            }
            error("unsupported builtin reached lowering: " + payload.name, inst.loc);
            return nullptr;
        }
    }
}

void Lowerer::lower_inline_asm(const cir::InlineAsmPayload& payload,
                               const std::vector<cir::ValueRef>& operands,
                               llvm::BasicBlock* fallthrough,
                               const std::vector<llvm::BasicBlock*>& indirect_dests,
                               SrcLoc loc) {
    if (operands.size() != payload.outputs.size() + payload.inputs.size()) {
        error("inline asm operand count does not match metadata", loc);
        return;
    }

    std::string asm_template = payload.asm_string;
    {
        std::unordered_map<std::string, size_t> name_to_index;
        size_t index = 0;
        for (const cir::InlineAsmOperandPayload& output : payload.outputs) {
            if (output.symbolic_name.valid()) {
                std::string name = file_.name(output.symbolic_name);
                if (!name.empty()) {
                    name_to_index[name] = index;
                }
            }
            ++index;
        }
        for (const cir::InlineAsmOperandPayload& input : payload.inputs) {
            if (input.symbolic_name.valid()) {
                std::string name = file_.name(input.symbolic_name);
                if (!name.empty()) {
                    name_to_index[name] = index;
                }
            }
            ++index;
        }
        for (const cir::InlineAsmOperandPayload& output : payload.outputs) {
            if (!output.constraint.empty() && output.constraint[0] == '+') {
                ++index;
            }
        }
        for (cir::NameId label : payload.goto_labels) {
            if (label.valid()) {
                std::string name = file_.name(label);
                if (!name.empty()) {
                    name_to_index[name] = index;
                }
            }
            ++index;
        }

        std::string rewritten;
        rewritten.reserve(asm_template.size());
        for (size_t i = 0; i < asm_template.size(); ++i) {
            if (asm_template[i] == '%' && i + 1 < asm_template.size()) {
                if (asm_template[i + 1] == '[') {
                    size_t close = asm_template.find(']', i + 2);
                    if (close != std::string::npos) {
                        std::string name = asm_template.substr(i + 2, close - (i + 2));
                        auto found = name_to_index.find(name);
                        if (found != name_to_index.end()) {
                            rewritten += "%" + std::to_string(found->second);
                            i = close;
                            continue;
                        }
                    }
                }
                if (std::isalpha(static_cast<unsigned char>(asm_template[i + 1])) &&
                    i + 2 < asm_template.size() &&
                    asm_template[i + 2] == '[') {
                    char modifier = asm_template[i + 1];
                    size_t close = asm_template.find(']', i + 3);
                    if (close != std::string::npos) {
                        std::string name = asm_template.substr(i + 3, close - (i + 3));
                        auto found = name_to_index.find(name);
                        if (found != name_to_index.end()) {
                            rewritten += "%";
                            rewritten += modifier;
                            rewritten += std::to_string(found->second);
                            i = close;
                            continue;
                        }
                    }
                }
            }
            rewritten += asm_template[i];
        }
        asm_template = translate_gcc_to_llvm_asm(rewritten);
    }

    std::string constraints;
    std::vector<llvm::Type*> output_types;
    std::vector<llvm::Value*> output_addrs;
    std::vector<llvm::Value*> input_values;
    std::vector<llvm::Type*> input_types;
    std::vector<llvm::Type*> input_element_types;
    std::vector<int> output_model_index(payload.outputs.size(), -1);

    std::vector<int> output_constraint_index(payload.outputs.size(), -1);
    int appended_output_count = 0;
    std::vector<llvm::Value*> memory_output_addrs(payload.outputs.size(), nullptr);
    std::vector<llvm::Type*> memory_output_element_types(payload.outputs.size(), nullptr);
    std::vector<bool> memory_output_tied(payload.outputs.size(), false);
    bool needs_implicit_memory_clobber = false;
    bool has_memory_clobber = false;
    bool has_template_text = template_has_non_whitespace(payload.asm_string);

    auto append_constraint = [&](const std::string& constraint) {
        if (!constraints.empty()) {
            constraints += ',';
        }
        constraints += constraint;
    };

    for (size_t output_index = 0; output_index < payload.outputs.size(); ++output_index) {
        const cir::InlineAsmOperandPayload& output = payload.outputs[output_index];
        std::string constraint = normalize_gcc_constraint_for_llvm(output.constraint);
        bool memory_output = constraint_uses_memory_operand(constraint);
        cir::ValueRef output_ref = operands[output_index];
        llvm::Value* addr = value_for(output_ref, loc);
        if (!addr) {
            return;
        }
        cir::TypeId place_type = file_.inst(output_ref.inst).result_type;
        cir::TypeId object_type = file_.place_object_type(place_type);
        llvm::Type* llvm_object_type = llvm_type(object_type);
        if (memory_output && !has_template_text) {
            needs_implicit_memory_clobber = true;
            continue;
        }
        if (memory_output) {
            std::string output_constraint = add_llvm_indirect_memory_marker(constraint);
            if (!output_constraint.empty() && output_constraint[0] == '+') {
                output_constraint[0] = '=';
                memory_output_tied[output_index] = true;
            }
            output_constraint_index[output_index] = appended_output_count++;
            append_constraint(output_constraint);
            input_values.push_back(addr);
            input_types.push_back(addr->getType());
            input_element_types.push_back(llvm_object_type);
            memory_output_addrs[output_index] = addr;
            memory_output_element_types[output_index] = llvm_object_type;
            continue;
        }

        output_addrs.push_back(addr);
        output_types.push_back(llvm_object_type);
        output_model_index[output_index] = static_cast<int>(output_types.size()) - 1;
        output_constraint_index[output_index] = appended_output_count++;
        if (!constraint.empty() && constraint[0] == '+') {
            constraint[0] = '=';
        }
        if (!output.register_binding.empty()) {
            std::string reg = options_.target
                ? normalize_asm_register_for_target(
                      output.register_binding, options_.target->arch,
                      asm_operand_bit_width(llvm_object_type))
                : output.register_binding;
            constraint = constraint_with_register_binding(constraint, reg);
        }
        append_constraint(constraint);
    }

    size_t input_operand_base = payload.outputs.size();
    for (size_t input_index = 0; input_index < payload.inputs.size(); ++input_index) {
        const cir::InlineAsmOperandPayload& input = payload.inputs[input_index];
        std::string constraint = normalize_gcc_constraint_for_llvm(input.constraint);
        cir::ValueRef input_ref = operands[input_operand_base + input_index];
        llvm::Value* value = value_for(input_ref, loc);
        if (!value) {
            return;
        }
        if (constraint_is_memory_only(constraint)) {
            cir::TypeId place_type = file_.inst(input_ref.inst).result_type;
            cir::TypeId object_type = file_.place_object_type(place_type);
            input_element_types.push_back(llvm_type(object_type));
            constraint = add_llvm_indirect_memory_marker(constraint);
        } else {

            constraint = strip_memory_alternatives(constraint);
            input_element_types.push_back(nullptr);
        }
        if (!input.register_binding.empty() &&
            !constraint_is_memory_only(input.constraint)) {
            std::string reg = options_.target
                ? normalize_asm_register_for_target(
                      input.register_binding, options_.target->arch,
                      asm_operand_bit_width(value->getType()))
                : input.register_binding;
            constraint = constraint_with_register_binding(constraint, reg);
        }
        input_values.push_back(value);
        input_types.push_back(value->getType());
        append_constraint(constraint);
    }

    for (size_t output_index = 0; output_index < payload.outputs.size(); ++output_index) {
        const cir::InlineAsmOperandPayload& output = payload.outputs[output_index];
        if (output.constraint.empty() || output.constraint[0] != '+') {
            continue;
        }
        if (memory_output_tied[output_index]) {
            llvm::Value* addr = memory_output_addrs[output_index];
            if (!addr) {
                return;
            }
            std::string tie_constraint =
                normalize_gcc_constraint_for_llvm(output.constraint);
            tie_constraint = add_llvm_indirect_memory_marker(
                strip_output_constraint_prefix(tie_constraint));
            input_values.push_back(addr);
            input_types.push_back(addr->getType());
            input_element_types.push_back(memory_output_element_types[output_index]);
            append_constraint(tie_constraint);
            continue;
        }
        if (output_model_index[output_index] < 0) {
            continue;
        }
        int modeled_index = output_model_index[output_index];
        llvm::Value* loaded = builder().CreateLoad(output_types[modeled_index],
                                                   output_addrs[modeled_index],
                                                   "asm.tied");
        input_values.push_back(loaded);
        input_types.push_back(output_types[modeled_index]);
        input_element_types.push_back(nullptr);

        append_constraint(std::to_string(output_constraint_index[output_index]));
    }

    for (size_t index = 0; index < indirect_dests.size(); ++index) {
        (void)index;
        append_constraint("!i");
    }

    for (const std::string& clobber : payload.clobbers) {
        if (clobber == "memory") {
            has_memory_clobber = true;
        }
        append_constraint("~{" + clobber + "}");
    }
    if (needs_implicit_memory_clobber && !has_memory_clobber) {
        append_constraint("~{memory}");
    }

    llvm::Type* return_type = nullptr;
    if (output_types.empty()) {
        return_type = llvm::Type::getVoidTy(context());
    } else if (output_types.size() == 1) {
        return_type = output_types.front();
    } else {
        return_type = llvm::StructType::get(context(), output_types);
    }

    llvm::FunctionType* asm_type =
        llvm::FunctionType::get(return_type, input_types, false);
    llvm::InlineAsm::AsmDialect dialect = payload.intel_dialect
        ? llvm::InlineAsm::AD_Intel
        : llvm::InlineAsm::AD_ATT;
    llvm::InlineAsm* asm_value =
        llvm::InlineAsm::get(asm_type,
                             asm_template,
                             constraints,
                             payload.has_side_effects || needs_implicit_memory_clobber,
                             payload.align_stack,
                             dialect);

    llvm::CallBase* call = nullptr;
    llvm::Value* result = nullptr;
    if (fallthrough) {
        auto* callbr = builder().CreateCallBr(asm_type,
                                              asm_value,
                                              fallthrough,
                                              indirect_dests,
                                              input_values);
        call = callbr;
        result = callbr;
        builder().SetInsertPoint(fallthrough);
    } else {
        auto* call_inst = builder().CreateCall(asm_type, asm_value, input_values);
        call = call_inst;
        result = call_inst;
    }

    for (size_t index = 0; index < input_element_types.size(); ++index) {
        if (!input_element_types[index]) {
            continue;
        }
        call->addParamAttr(
            static_cast<unsigned>(index),
            llvm::Attribute::get(
                context(), llvm::Attribute::ElementType, input_element_types[index]));
    }

    if (output_types.empty()) {
        return;
    }
    if (output_types.size() == 1) {
        builder().CreateStore(result, output_addrs.front());
        return;
    }
    for (size_t index = 0; index < output_types.size(); ++index) {
        llvm::Value* extracted = builder().CreateExtractValue(result,
                                                              static_cast<unsigned>(index),
                                                              "asm.out");
        builder().CreateStore(extracted, output_addrs[index]);
    }
}

llvm::Value* Lowerer::lower_call(const cir::Inst& inst,
                                 const std::vector<cir::Operand>& operands) {
    FunctionAbiInfo abi;
    llvm::Value* callee = nullptr;
    size_t first_arg = 0;
    cir::TypeId source_function_type{};

    if (operands.empty()) {
        error("call is missing a callee", inst.loc);
        return nullptr;
    }

    if (const auto* entity = std::get_if<cir::EntityId>(&operands[0].data)) {
        if (file_.valid(*entity) &&
            file_.entity(*entity).decl_flags.is_consteval) {
            error("call to consteval function is not a constant expression",
                  inst.loc);
            return nullptr;
        }
        callee = function_symbol(*entity);
        source_function_type = file_.entity(*entity).type;
        abi = classify_function_abi(source_function_type);
        first_arg = 1;
    } else if (const auto* value = std::get_if<cir::ValueRef>(&operands[0].data)) {
        callee = value_for(*value, inst.loc);
        cir::TypeId callee_type = file_.inst(value->inst).result_type;
        source_function_type = file_.pointer_pointee_type(callee_type);
        cir::TypeId resolved_fn = file_.resolved_type(source_function_type);
        if (!file_.valid(resolved_fn) ||
            file_.type(resolved_fn).kind != cir::TypeKind::Function) {

            if (!callee) {
                return nullptr;
            }
            std::vector<llvm::Type*> param_types;
            std::vector<llvm::Value*> direct_args;
            for (size_t i = 1; i < operands.size(); ++i) {
                cir::ValueRef arg_ref = value_operand_at(operands, i);
                llvm::Value* arg = value_for(arg_ref, inst.loc);
                if (!arg) {
                    return nullptr;
                }
                param_types.push_back(arg->getType());
                direct_args.push_back(arg);
            }
            llvm::Type* result_type = file_.valid(inst.result_type)
                ? llvm_type(inst.result_type)
                : llvm::Type::getVoidTy(context());
            if (!result_type) {
                result_type = llvm::Type::getVoidTy(context());
            }
            llvm::FunctionType* call_type =
                llvm::FunctionType::get(result_type, param_types, false);
            return builder().CreateCall(call_type, callee, direct_args);
        }
        abi = classify_function_abi(source_function_type);
        first_arg = 1;
    } else {
        error("call callee operand has invalid kind", inst.loc);
        return nullptr;
    }
    if (!callee || !abi.llvm_type) {
        return nullptr;
    }

    std::vector<llvm::Value*> args;
    llvm::Value* indirect_result_slot = nullptr;
    if (abi.result.kind == AbiArgKind::Indirect) {
        indirect_result_slot = inst.result_object_entity.valid()
            ? storage_for_entity(inst.result_object_entity, inst.loc)
            : create_entry_alloca(llvm_type(abi.result.source_type),
                                  "call.sret");
        if (!indirect_result_slot) {
            return nullptr;
        }
        if (!inst.result_object_entity.valid()) {
            if (auto size_align = cir::size_align_of_type(
                    file_, abi.result.source_type.type)) {
                llvm::cast<llvm::AllocaInst>(indirect_result_slot)
                    ->setAlignment(llvm::Align(
                        std::max<size_t>(1,
                                         size_align->alignment_bytes)));
            }
        }
        args.push_back(indirect_result_slot);
    }

    for (size_t i = first_arg; i < operands.size(); ++i) {
        cir::ValueRef arg_ref = value_operand_at(operands, i);
        llvm::Value* arg = value_for(arg_ref, inst.loc);
        size_t param_index = i - first_arg;
        if (arg && param_index < abi.params.size()) {
            const AbiArgInfo& param_abi = abi.params[param_index];
            if (param_abi.is_ignored) {
                continue;
            }
            if (param_abi.kind == AbiArgKind::Indirect) {
                cir::EntityId argument_object =
                    parameter_argument_object(file_, arg_ref.inst);
                arg = argument_object.valid()
                    ? storage_for_entity(argument_object, inst.loc)
                    : materialize_source_value_to_indirect_abi(
                          arg, param_abi.source_type, inst.loc,
                          "indirect.tmp");
            } else if (param_abi.is_direct_aggregate) {
                arg = materialize_source_value_to_abi(arg,
                                                      param_abi.source_type,
                                                      param_abi.abi_type,
                                                      inst.loc,
                                                      "arg.abi");
            } else {
                arg = cast_value(arg,
                                 param_abi.abi_type,
                                 inst.loc,
                                 "arg.cast");
            }
        } else if (arg && (abi.is_variadic || !abi.has_prototype) &&
                   param_index >= abi.params.size()) {

            cir::TypeId arg_type = file_.valid(arg_ref.inst)
                ? file_.inst(arg_ref.inst).result_type
                : cir::TypeId{};

            AbiArgInfo extra_abi = abi.is_variadic
                ? classify_vararg_abi(file_.type_ref(arg_type))
                : classify_param_abi(file_.type_ref(arg_type));
            if (extra_abi.kind == AbiArgKind::Indirect) {
                arg = materialize_source_value_to_indirect_abi(arg,
                                                               extra_abi.source_type,
                                                               inst.loc,
                                                               "unnamed.indirect");
            } else if (extra_abi.is_direct_aggregate) {
                arg = materialize_source_value_to_abi(arg,
                                                      extra_abi.source_type,
                                                      extra_abi.abi_type,
                                                      inst.loc,
                                                      "unnamed.abi");
            }
        }
        if (arg) {
            args.push_back(arg);
        }
    }

    llvm::FunctionType* call_type = abi.llvm_type;
    if (!abi.has_prototype && args.size() != abi.llvm_type->getNumParams()) {
        std::vector<llvm::Type*> actual_param_types;
        actual_param_types.reserve(args.size());
        for (llvm::Value* arg : args) {
            actual_param_types.push_back(arg->getType());
        }
        call_type = llvm::FunctionType::get(abi.llvm_type->getReturnType(),
                                            actual_param_types,
                                            false);
    }

    if (abi.has_prototype && !call_type->isVarArg() &&
        args.size() != call_type->getNumParams()) {
        error("call argument count does not match callee type", inst.loc);
        return nullptr;
    }
    if (abi.has_prototype && call_type->isVarArg() &&
        args.size() < call_type->getNumParams()) {
        error("variadic call has too few fixed arguments", inst.loc);
        return nullptr;
    }

    bool callee_can_throw = true;
    if (const auto* fn_payload = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(source_function_type)));
        fn_payload &&
        fn_payload->exception_spec.kind ==
            cir::FunctionExceptionSpecKind::NonThrowing) {

        callee_can_throw = false;
    }
    llvm::CallBase* call = emit_call_or_invoke(
        call_type,
        callee,
        args,
        callee_can_throw,
        call_type->getReturnType()->isVoidTy() ? "" : "call",
        inst.loc);
    if (!call) {
        return nullptr;
    }
    apply_call_abi_attributes(call, abi);
    if (!callee_can_throw) {
        call->setDoesNotThrow();
    }
    if (const auto* call_payload =
            std::get_if<cir::CallPayload>(&file_.payload(inst.payload_index))) {
        if (call_payload->must_tail) {

            if (auto* plain = llvm::dyn_cast<llvm::CallInst>(call)) {
                plain->setTailCallKind(llvm::CallInst::TCK_MustTail);
            }
        }
    }
    if (indirect_result_slot) {
        return materialize_indirect_abi_value_to_source(indirect_result_slot,
                                                        abi.result.source_type,
                                                        inst.loc,
                                                        "call.sret.load");
    }
    if (abi.result.is_ignored) {
        return llvm::Constant::getNullValue(llvm_type(inst.result_type));
    }
    if (call->getType()->isVoidTy()) {
        return call;
    }
    if (abi.result.is_direct_aggregate) {
        return materialize_abi_value_to_source(call,
                                               abi.result.source_type,
                                               inst.loc,
                                               "call.result");
    }
    return cast_value(call, llvm_type(inst.result_type), inst.loc, "call.result");
}

void Lowerer::lower_terminator(const cir::Terminator& terminator) {
    std::vector<cir::ValueRef> operands = file_.value_operands(terminator.operands);
    auto add_block_arg_incomings = [&](cir::BlockId target, size_t first_arg) -> bool {
        if (!file_.valid(target)) {
            error("invalid branch target", terminator.loc);
            return false;
        }
        const cir::Block& target_block = file_.block(target);
        size_t arg_count = operands.size() > first_arg ? operands.size() - first_arg : 0;
        if (arg_count != target_block.parameters.size()) {
            error("branch target argument count does not match target parameters",
                  terminator.loc);
            return false;
        }

        llvm::BasicBlock* source_block = builder().GetInsertBlock();
        for (size_t index = 0; index < arg_count; ++index) {
            llvm::Value* incoming = value_for(operands[first_arg + index], terminator.loc);
            llvm::Value* param_value = value_for(target_block.parameters[index], terminator.loc);
            auto* phi = llvm::dyn_cast_or_null<llvm::PHINode>(param_value);
            if (!incoming || !phi) {
                error("branch target parameter was not lowered as a PHI", terminator.loc);
                return false;
            }
            cir::TypeId source_type = file_.valid(operands[first_arg + index].inst)
                ? file_.inst(operands[first_arg + index].inst).result_type
                : cir::TypeId{};
            cir::TypeId target_type = file_.valid(target_block.parameters[index])
                ? file_.inst(target_block.parameters[index]).result_type
                : cir::TypeId{};
            incoming = cast_value(incoming,
                                  source_type,
                                  target_type,
                                  terminator.loc,
                                  "blockarg.cast");
            if (!incoming) {
                return false;
            }
            phi->addIncoming(incoming, source_block);
        }
        return true;
    };

    switch (terminator.kind) {
        case cir::TerminatorKind::Return:
            if (operands.empty()) {
                builder().CreateRetVoid();
            } else {
                llvm::Value* value = value_for(operands[0], terminator.loc);
                if (!value) {
                    return;
                }
                if (has_current_abi_ && current_abi_.result.is_ignored) {
                    builder().CreateRetVoid();
                    return;
                }
                if (has_current_abi_ &&
                    current_abi_.result.kind == AbiArgKind::Indirect) {
                    if (!current_sret_pointer_) {
                        error("missing indirect result pointer for return", terminator.loc);
                        return;
                    }
                    llvm::Type* object_type = llvm_type(current_abi_.result.source_type);
                    value = cast_value(value, object_type, terminator.loc, "return.sret.cast");
                    if (!value) {
                        return;
                    }
                    builder().CreateStore(value, current_sret_pointer_);
                    builder().CreateRetVoid();
                    return;
                }
                if (has_current_abi_ && current_abi_.result.is_direct_aggregate) {
                    value = materialize_source_value_to_abi(value,
                                                            current_abi_.result.source_type,
                                                            current_abi_.result.abi_type,
                                                            terminator.loc,
                                                            "return.abi");
                    if (!value) {
                        return;
                    }
                    builder().CreateRet(value);
                    return;
                }
                value = cast_value(value,
                                   current_function_->getReturnType(),
                                   terminator.loc,
                                   "return.cast");
                if (value) {
                    builder().CreateRet(value);
                }
            }
            return;
        case cir::TerminatorKind::Branch:
            if (!add_block_arg_incomings(terminator.target, 0)) {
                return;
            }
            builder().CreateBr(block_values_[id_key(terminator.target)]);
            return;
        case cir::TerminatorKind::CondBranch:
            if (operands.empty()) {
                error("conditional branch missing condition", terminator.loc);
                return;
            }
            if (llvm::Value* condition =
                    truth_value(value_for(operands[0], terminator.loc), terminator.loc)) {
                if (!add_block_arg_incomings(terminator.target, 1) ||
                    !add_block_arg_incomings(terminator.false_target, 1)) {
                    return;
                }
                builder().CreateCondBr(condition,
                                       block_values_[id_key(terminator.target)],
                                       block_values_[id_key(terminator.false_target)]);
            }
            return;
        case cir::TerminatorKind::Switch: {
            if (operands.size() != 1) {
                error("switch terminator missing condition", terminator.loc);
                return;
            }
            llvm::Value* condition = value_for(operands[0], terminator.loc);
            if (!condition) {
                return;
            }
            auto* condition_type = llvm::dyn_cast<llvm::IntegerType>(condition->getType());
            if (!condition_type) {
                error("switch condition must lower to an integer type", terminator.loc);
                return;
            }
            const cir::InstPayload& payload = file_.payload(terminator.payload_index);
            const auto* switch_payload =
                std::get_if<cir::SwitchTerminatorPayload>(&payload);
            if (!switch_payload) {
                error("switch terminator payload is missing", terminator.loc);
                return;
            }
            llvm::BasicBlock* default_block = block_values_[id_key(terminator.target)];
            if (!default_block) {
                error("switch default target is invalid", terminator.loc);
                return;
            }

            auto case_constant = [&](int64_t value) -> llvm::ConstantInt* {
                return llvm::ConstantInt::get(
                    context(),
                    llvm::APInt(condition_type->getBitWidth(),
                                static_cast<uint64_t>(value),
                                true));
            };

            bool has_range = false;
            for (const cir::SwitchCaseRange& case_range : switch_payload->cases) {
                if (case_range.low != case_range.high) {
                    has_range = true;
                    break;
                }
            }
            if (!has_range) {
                llvm::SwitchInst* switch_inst =
                    builder().CreateSwitch(condition,
                                           default_block,
                                           static_cast<unsigned>(
                                               switch_payload->cases.size()));
                for (const cir::SwitchCaseRange& case_range : switch_payload->cases) {
                    llvm::BasicBlock* target_block =
                        block_values_[id_key(case_range.target)];
                    if (!target_block) {
                        error("switch case target is invalid", case_range.loc);
                        return;
                    }
                    switch_inst->addCase(case_constant(case_range.low), target_block);
                }
                return;
            }

            if (switch_payload->cases.empty()) {
                builder().CreateBr(default_block);
                return;
            }

            std::vector<llvm::BasicBlock*> check_blocks;
            check_blocks.reserve(switch_payload->cases.size());
            check_blocks.push_back(builder().GetInsertBlock());
            for (size_t index = 1; index < switch_payload->cases.size(); ++index) {
                check_blocks.push_back(
                    llvm::BasicBlock::Create(context(),
                                             "switch.range.check",
                                             current_function_));
            }
            cir::IntegerTypeShape shape =
                cir::integer_shape_for_type(file_, switch_payload->condition_type.type);
            llvm::CmpInst::Predicate ge_pred =
                shape.is_unsigned ? llvm::CmpInst::ICMP_UGE : llvm::CmpInst::ICMP_SGE;
            llvm::CmpInst::Predicate le_pred =
                shape.is_unsigned ? llvm::CmpInst::ICMP_ULE : llvm::CmpInst::ICMP_SLE;

            for (size_t index = 0; index < switch_payload->cases.size(); ++index) {
                const cir::SwitchCaseRange& case_range = switch_payload->cases[index];
                llvm::BasicBlock* target_block = block_values_[id_key(case_range.target)];
                if (!target_block) {
                    error("switch case target is invalid", case_range.loc);
                    return;
                }
                llvm::BasicBlock* false_block = index + 1 < check_blocks.size()
                    ? check_blocks[index + 1]
                    : default_block;
                builder().SetInsertPoint(check_blocks[index]);
                llvm::Value* matches = nullptr;
                if (case_range.low == case_range.high) {
                    matches = builder().CreateICmpEQ(condition,
                                                     case_constant(case_range.low),
                                                     "switch.case.eq");
                } else {
                    llvm::Value* above_low =
                        builder().CreateICmp(ge_pred,
                                             condition,
                                             case_constant(case_range.low),
                                             "switch.range.ge");
                    llvm::Value* below_high =
                        builder().CreateICmp(le_pred,
                                             condition,
                                             case_constant(case_range.high),
                                             "switch.range.le");
                    matches = builder().CreateAnd(above_low,
                                                  below_high,
                                                  "switch.range.match");
                }
                builder().CreateCondBr(matches, target_block, false_block);
            }
            return;
        }
        case cir::TerminatorKind::IndirectBranch: {
            if (operands.empty()) {
                error("indirect branch missing target", terminator.loc);
                return;
            }
            llvm::Value* target = value_for(operands[0], terminator.loc);
            if (!target) {
                return;
            }
            target = cast_value(target,
                                llvm::PointerType::get(context(), 0),
                                terminator.loc,
                                "indirectbr.cast");
            if (!target) {
                return;
            }

            auto* branch =
                builder().CreateIndirectBr(target,
                                           static_cast<unsigned>(address_taken_blocks_.size()));
            for (llvm::BasicBlock* dest : address_taken_blocks_) {
                branch->addDestination(dest);
            }
            return;
        }
        case cir::TerminatorKind::AsmGoto: {
            if (!file_.valid(terminator.target)) {
                error("asm goto fallthrough target is invalid", terminator.loc);
                return;
            }
            const cir::InstPayload& term_payload = file_.payload(terminator.payload_index);
            const auto* asm_ref = std::get_if<cir::InlineAsmPayloadRef>(&term_payload);
            if (!asm_ref || !file_.valid(asm_ref->payload)) {
                error("asm goto terminator is missing asm metadata", terminator.loc);
                return;
            }
            const cir::InlineAsmPayload& asm_payload =
                file_.inline_asm_payload(asm_ref->payload);
            std::vector<llvm::BasicBlock*> indirect_dests;
            indirect_dests.reserve(asm_payload.goto_targets.size());
            for (cir::BlockId target : asm_payload.goto_targets) {
                auto found = block_values_.find(id_key(target));
                if (found == block_values_.end()) {
                    error("asm goto label target was not lowered", terminator.loc);
                    return;
                }
                indirect_dests.push_back(found->second);
            }
            auto fallthrough_it = block_values_.find(id_key(terminator.target));
            if (fallthrough_it == block_values_.end()) {
                error("asm goto fallthrough block was not lowered", terminator.loc);
                return;
            }
            lower_inline_asm(asm_payload,
                             operands,
                             fallthrough_it->second,
                             indirect_dests,
                             terminator.loc);
            return;
        }
        case cir::TerminatorKind::Unreachable:
            builder().CreateUnreachable();
            return;
        case cir::TerminatorKind::Throw:
        case cir::TerminatorKind::Rethrow:
            lower_throw_terminator(terminator);
            return;
        case cir::TerminatorKind::Resume:
            lower_resume_terminator(terminator);
            return;
        case cir::TerminatorKind::CoroSuspend:
        case cir::TerminatorKind::CoroEnd:
            error("pre-split coroutine CIR reached the LLVM backend; the "
                  "coroutine split pass must run first",
                  terminator.loc);
            return;
        case cir::TerminatorKind::Invalid:
            error("missing terminator reached lowering", terminator.loc);
            return;
    }
}

llvm::AtomicOrdering Lowerer::atomic_ordering(cir::MemoryOrder order,
                                              bool is_store,
                                              bool is_load) {
    llvm::AtomicOrdering result = llvm::AtomicOrdering::SequentiallyConsistent;
    switch (order) {
        case cir::MemoryOrder::Relaxed: result = llvm::AtomicOrdering::Monotonic; break;
        case cir::MemoryOrder::Consume:
        case cir::MemoryOrder::Acquire: result = llvm::AtomicOrdering::Acquire; break;
        case cir::MemoryOrder::Release: result = llvm::AtomicOrdering::Release; break;
        case cir::MemoryOrder::AcqRel: result = llvm::AtomicOrdering::AcquireRelease; break;
        case cir::MemoryOrder::SeqCst: result = llvm::AtomicOrdering::SequentiallyConsistent; break;
    }

    if (is_load && (result == llvm::AtomicOrdering::Release ||
                    result == llvm::AtomicOrdering::AcquireRelease)) {
        result = llvm::AtomicOrdering::SequentiallyConsistent;
    }
    if (is_store && (result == llvm::AtomicOrdering::Acquire ||
                     result == llvm::AtomicOrdering::AcquireRelease ||
                     result == llvm::AtomicOrdering::Monotonic)) {
        result = result == llvm::AtomicOrdering::Monotonic
            ? llvm::AtomicOrdering::Monotonic
            : llvm::AtomicOrdering::SequentiallyConsistent;
    }
    return result;
}

llvm::Align Lowerer::atomic_alignment(cir::TypeId type) {
    std::optional<size_t> size = cir::size_of_type(file_, type);
    size_t bytes = size.value_or(8);
    size_t align = 1;
    while (align < bytes && align < 16) {
        align *= 2;
    }
    return llvm::Align(align);
}

llvm::Value* Lowerer::truth_value(llvm::Value* value, SrcLoc loc) {
    if (!value) {
        return nullptr;
    }
    llvm::Type* type = value->getType();
    if (type->isIntegerTy(1)) {
        return value;
    }
    if (type->isIntegerTy()) {
        return builder().CreateICmpNE(value, llvm::ConstantInt::get(type, 0), "truth");
    }
    if (type->isFloatingPointTy()) {

        return builder().CreateFCmpUNE(value, llvm::ConstantFP::get(type, 0.0), "truth");
    }
    if (type->isArrayTy() && type->getArrayNumElements() == 2 &&
        (type->getArrayElementType()->isFloatingPointTy() ||
         type->getArrayElementType()->isIntegerTy())) {

        llvm::Value* re =
            truth_value(builder().CreateExtractValue(value, {0}, "truth.re"), loc);
        llvm::Value* im =
            truth_value(builder().CreateExtractValue(value, {1}, "truth.im"), loc);
        return builder().CreateOr(re, im, "truth.complex");
    }
    if (type->isPointerTy()) {
        return builder().CreateICmpNE(value, llvm::ConstantPointerNull::get(
                                               llvm::cast<llvm::PointerType>(type)),
                                     "truth");
    }
    error("cannot convert value to condition", loc);
    return nullptr;
}

llvm::Value* Lowerer::cast_value(llvm::Value* value,
                        llvm::Type* target_type,
                        SrcLoc loc,
                        llvm::StringRef name) {
    if (!value || !target_type) {
        return nullptr;
    }
    llvm::Type* source_type = value->getType();
    if (source_type == target_type) {
        return value;
    }
    if (target_type->isVoidTy()) {
        return value;
    }
    if (target_type->isIntegerTy(1) &&
        (source_type->isIntegerTy() || source_type->isFloatingPointTy() ||
         source_type->isPointerTy())) {
        return truth_value(value, loc);
    }
    auto* source_vector = llvm::dyn_cast<llvm::FixedVectorType>(source_type);
    auto* target_vector = llvm::dyn_cast<llvm::FixedVectorType>(target_type);
    if (target_vector) {
        llvm::Type* target_element = target_vector->getElementType();
        if (!source_vector) {
            if (!source_type->isIntegerTy() && !source_type->isFloatingPointTy()) {
                error("unsupported scalar-to-vector cast", loc);
                return nullptr;
            }
            llvm::Value* element =
                cast_value(value, target_element, loc, "vector.splat.elem");
            return element
                ? builder().CreateVectorSplat(target_vector->getElementCount(),
                                              element,
                                              name)
                : nullptr;
        }
        if (source_vector->getNumElements() != target_vector->getNumElements()) {
            error("vector cast requires matching lane counts", loc);
            return nullptr;
        }
        llvm::Type* source_element = source_vector->getElementType();
        if (target_element->isIntegerTy(1)) {
            llvm::Constant* zero = llvm::Constant::getNullValue(source_type);
            if (source_element->isIntegerTy()) {
                return builder().CreateICmpNE(value, zero, name);
            }
            if (source_element->isFloatingPointTy()) {
                return builder().CreateFCmpUNE(value, zero, name);
            }
        }
        if (source_element->isIntegerTy() && target_element->isIntegerTy()) {
            if (source_element->isIntegerTy(1)) {
                return builder().CreateSExt(value, target_type, name);
            }
            return builder().CreateIntCast(value, target_type, true, name);
        }
        if (source_element->isIntegerTy() && target_element->isFloatingPointTy()) {
            return builder().CreateSIToFP(value, target_type, name);
        }
        if (source_element->isFloatingPointTy() && target_element->isIntegerTy()) {
            return builder().CreateFPToSI(value, target_type, name);
        }
        if (source_element->isFloatingPointTy() && target_element->isFloatingPointTy()) {
            return builder().CreateFPCast(value, target_type, name);
        }
    }
    if (source_vector) {

        if ((target_type->isIntegerTy() || target_type->isFloatingPointTy()) &&
            module().getDataLayout().getTypeSizeInBits(source_type) ==
                module().getDataLayout().getTypeSizeInBits(target_type)) {
            return builder().CreateBitCast(value, target_type, name);
        }
        error("unsupported vector-to-scalar cast", loc);
        return nullptr;
    }
    if (source_type->isIntegerTy() && target_type->isIntegerTy()) {
        bool source_is_bool = source_type->getIntegerBitWidth() == 1;
        return builder().CreateIntCast(value, target_type, !source_is_bool, name);
    }
    if (source_type->isIntegerTy() && target_type->isFloatingPointTy()) {
        return builder().CreateSIToFP(value, target_type, name);
    }
    if (source_type->isFloatingPointTy() && target_type->isIntegerTy()) {
        return builder().CreateFPToSI(value, target_type, name);
    }
    if (source_type->isFloatingPointTy() && target_type->isFloatingPointTy()) {
        return builder().CreateFPCast(value, target_type, name);
    }
    if (source_type->isPointerTy() && target_type->isPointerTy()) {
        return value;
    }
    if (source_type->isPointerTy() && target_type->isIntegerTy()) {
        return builder().CreatePtrToInt(value, target_type, name);
    }
    if (source_type->isIntegerTy() && target_type->isPointerTy()) {
        return builder().CreateIntToPtr(value, target_type, name);
    }
    error("unsupported cast from LLVM type to target type", loc);
    return nullptr;
}

llvm::Value* Lowerer::cast_value(llvm::Value* value,
                                 cir::TypeId source_type_id,
                                 cir::TypeId target_type_id,
                                 SrcLoc loc,
                                 llvm::StringRef name) {
    if (!value) {
        return nullptr;
    }
    llvm::Type* target_type = llvm_type(target_type_id);
    if (!target_type) {
        return nullptr;
    }
    llvm::Type* source_type = value->getType();
    if (is_nullptr_type(target_type_id)) {
        return llvm_nullptr_carrier_value();
    }
    auto cir_type_kind = [&](cir::TypeId type_id) -> std::optional<cir::TypeKind> {
        type_id = file_.resolved_type(type_id);
        if (!file_.valid(type_id)) {
            return std::nullopt;
        }
        return file_.type(type_id).kind;
    };
    if (is_nullptr_type(source_type_id)) {
        std::optional<cir::TypeKind> target_kind = cir_type_kind(target_type_id);
        if (target_kind &&
            (*target_kind == cir::TypeKind::Pointer ||
             *target_kind == cir::TypeKind::BlockPointer) &&
            target_type->isPointerTy()) {
            return llvm::ConstantPointerNull::get(
                llvm::cast<llvm::PointerType>(target_type));
        }
        if (target_kind && *target_kind == cir::TypeKind::MemberPointer) {
            if (file_.member_pointer_points_to_function(target_type_id)) {
                llvm::StructType* type = llvm::dyn_cast<llvm::StructType>(target_type);
                if (!type || type != llvm_member_function_pointer_type()) {
                    error("member function pointer null conversion requires pair ABI storage",
                          loc);
                    return nullptr;
                }
                return llvm::ConstantStruct::get(
                    type,
                    {llvm::ConstantPointerNull::get(
                         llvm::PointerType::get(context(), 0)),
                     llvm::ConstantInt::get(
                         llvm::IntegerType::get(
                             context(), static_cast<unsigned>(pointer_bits())),
                         0,
                         true)});
            }
            if (target_type->isIntegerTy()) {
                return llvm::ConstantInt::get(target_type,
                                             static_cast<uint64_t>(-1),
                                             true);
            }
        }
        if (target_type->isIntegerTy()) {
            return llvm::ConstantInt::get(target_type, 0, false);
        }
    }
    if (source_type == target_type || target_type->isVoidTy()) {
        return value;
    }
    cir::OperatorValueDomain source_domain =
        source_type_id.valid()
            ? file_.operator_value_domain(file_.type_ref(source_type_id))
            : cir::OperatorValueDomain::Unknown;
    cir::OperatorValueDomain target_domain =
        target_type_id.valid()
            ? file_.operator_value_domain(file_.type_ref(target_type_id))
            : cir::OperatorValueDomain::Unknown;

    cir::TypeId resolved_source_type =
        source_type_id.valid()
            ? file_.resolved_type(source_type_id)
            : cir::TypeId{};
    bool source_is_member_pointer =
        file_.valid(resolved_source_type) &&
        file_.type(resolved_source_type).kind ==
            cir::TypeKind::MemberPointer;
    if (target_type->isIntegerTy(1) &&
        target_domain == cir::OperatorValueDomain::Bool &&
        source_is_member_pointer) {
        if (file_.member_pointer_points_to_function(resolved_source_type)) {
            if (!source_type->isStructTy()) {
                error("member function pointer truth conversion requires pair ABI storage",
                      loc);
                return nullptr;
            }
            llvm::Value* function =
                builder().CreateExtractValue(value, {0}, "member.fn.truth");
            return builder().CreateICmpNE(
                function,
                llvm::Constant::getNullValue(function->getType()),
                name);
        }
        if (!source_type->isIntegerTy()) {
            error("data member pointer truth conversion requires integer ABI storage",
                  loc);
            return nullptr;
        }
        return builder().CreateICmpNE(
            value,
            llvm::ConstantInt::get(source_type,
                                   static_cast<uint64_t>(-1), true),
            name);
    }

    if (target_type->isIntegerTy(1) &&
        (target_domain == cir::OperatorValueDomain::Bool ||
         !target_type_id.valid()) &&
        (source_type->isIntegerTy() || source_type->isFloatingPointTy() ||
         source_type->isPointerTy() ||
         (source_type->isArrayTy() && source_type->getArrayNumElements() == 2))) {
        return truth_value(value, loc);
    }
    bool source_unsigned =
        source_domain == cir::OperatorValueDomain::UnsignedInteger ||
        source_domain == cir::OperatorValueDomain::Bool;
    bool target_unsigned =
        target_domain == cir::OperatorValueDomain::UnsignedInteger ||
        target_domain == cir::OperatorValueDomain::Bool;

    auto* source_vector = llvm::dyn_cast<llvm::FixedVectorType>(source_type);
    auto* target_vector = llvm::dyn_cast<llvm::FixedVectorType>(target_type);
    if (target_vector) {
        llvm::Type* target_element = target_vector->getElementType();
        if (!source_vector) {
            if (!source_type->isIntegerTy() && !source_type->isFloatingPointTy()) {
                error("unsupported scalar-to-vector cast", loc);
                return nullptr;
            }
            cir::TypeId target_element_type = target_type_id.valid()
                ? file_.vector_element_type(target_type_id)
                : cir::TypeId{};
            llvm::Value* element = target_element_type.valid()
                ? cast_value(value,
                             source_type_id,
                             target_element_type,
                             loc,
                             "vector.splat.elem")
                : cast_value(value, target_element, loc, "vector.splat.elem");
            return element
                ? builder().CreateVectorSplat(target_vector->getElementCount(),
                                              element,
                                              name)
                : nullptr;
        }
        if (source_vector->getNumElements() != target_vector->getNumElements()) {
            error("vector cast requires matching lane counts", loc);
            return nullptr;
        }
        llvm::Type* source_element = source_vector->getElementType();
        if (target_element->isIntegerTy(1) &&
            target_domain == cir::OperatorValueDomain::Bool) {
            llvm::Constant* zero = llvm::Constant::getNullValue(source_type);
            if (source_element->isIntegerTy()) {
                return builder().CreateICmpNE(value, zero, name);
            }
            if (source_element->isFloatingPointTy()) {
                return builder().CreateFCmpUNE(value, zero, name);
            }
        }
        if (source_element->isIntegerTy() && target_element->isIntegerTy()) {
            if (source_element->isIntegerTy(1)) {
                return builder().CreateSExt(value, target_type, name);
            }
            return builder().CreateIntCast(value, target_type, !source_unsigned, name);
        }
        if (source_element->isIntegerTy() && target_element->isFloatingPointTy()) {
            return source_unsigned ? builder().CreateUIToFP(value, target_type, name)
                                   : builder().CreateSIToFP(value, target_type, name);
        }
        if (source_element->isFloatingPointTy() && target_element->isIntegerTy()) {
            return target_unsigned ? builder().CreateFPToUI(value, target_type, name)
                                   : builder().CreateFPToSI(value, target_type, name);
        }
        if (source_element->isFloatingPointTy() && target_element->isFloatingPointTy()) {
            return builder().CreateFPCast(value, target_type, name);
        }
    }
    if (source_vector) {

        if ((target_type->isIntegerTy() || target_type->isFloatingPointTy()) &&
            module().getDataLayout().getTypeSizeInBits(source_type) ==
                module().getDataLayout().getTypeSizeInBits(target_type)) {
            return builder().CreateBitCast(value, target_type, name);
        }
        error("unsupported vector-to-scalar cast", loc);
        return nullptr;
    }
    auto is_complex_agg = [](llvm::Type* type) {
        return type->isArrayTy() && type->getArrayNumElements() == 2 &&
               (type->getArrayElementType()->isFloatingPointTy() ||
                type->getArrayElementType()->isIntegerTy());
    };
    if (is_complex_agg(source_type) || is_complex_agg(target_type)) {
        if (is_complex_agg(source_type) && is_complex_agg(target_type)) {
            llvm::Type* target_element = target_type->getArrayElementType();
            auto convert_element = [&](unsigned index, const char* label) {
                llvm::Value* element =
                    builder().CreateExtractValue(value, {index}, label);
                if (element->getType() == target_element) {
                    return element;
                }
                if (element->getType()->isFloatingPointTy() &&
                    target_element->isFloatingPointTy()) {
                    return builder().CreateFPCast(element, target_element, label);
                }
                if (element->getType()->isFloatingPointTy()) {
                    return builder().CreateFPToSI(element, target_element, label);
                }
                if (target_element->isFloatingPointTy()) {
                    return builder().CreateSIToFP(element, target_element, label);
                }
                return builder().CreateIntCast(element, target_element, true, label);
            };
            llvm::Value* re = convert_element(0, "ccast.re");
            llvm::Value* im = convert_element(1, "ccast.im");
            llvm::Value* out = llvm::UndefValue::get(target_type);
            out = builder().CreateInsertValue(out, re, {0});
            return builder().CreateInsertValue(out, im, {1}, name);
        }
        if (is_complex_agg(target_type)) {

            llvm::Type* target_element = target_type->getArrayElementType();
            llvm::Value* re = value;
            if (re->getType() != target_element) {
                if (target_element->isFloatingPointTy()) {
                    re = re->getType()->isIntegerTy()
                        ? (source_unsigned
                               ? builder().CreateUIToFP(re, target_element, "ccast.re")
                               : builder().CreateSIToFP(re, target_element, "ccast.re"))
                        : builder().CreateFPCast(re, target_element, "ccast.re");
                } else {
                    re = re->getType()->isFloatingPointTy()
                        ? builder().CreateFPToSI(re, target_element, "ccast.re")
                        : builder().CreateIntCast(re, target_element,
                                                  !source_unsigned, "ccast.re");
                }
            }
            llvm::Value* out = llvm::UndefValue::get(target_type);
            out = builder().CreateInsertValue(out, re, {0});
            return builder().CreateInsertValue(
                out, llvm::Constant::getNullValue(target_element), {1}, name);
        }

        llvm::Value* re = builder().CreateExtractValue(value, {0}, "ccast.real");
        if (re->getType() == target_type) {
            return re;
        }
        if (re->getType()->isIntegerTy()) {
            if (target_type->isIntegerTy()) {
                return builder().CreateIntCast(re, target_type, true, name);
            }
            if (target_type->isFloatingPointTy()) {
                return builder().CreateSIToFP(re, target_type, name);
            }
            return re;
        }
        if (target_type->isFloatingPointTy()) {
            return builder().CreateFPCast(re, target_type, name);
        }
        if (target_type->isIntegerTy()) {
            return target_unsigned ? builder().CreateFPToUI(re, target_type, name)
                                   : builder().CreateFPToSI(re, target_type, name);
        }
        return re;
    }
    if (source_type->isIntegerTy() && target_type->isIntegerTy()) {
        return builder().CreateIntCast(value, target_type, !source_unsigned, name);
    }
    if (source_type->isIntegerTy() && target_type->isFloatingPointTy()) {
        return source_unsigned ? builder().CreateUIToFP(value, target_type, name)
                               : builder().CreateSIToFP(value, target_type, name);
    }
    if (source_type->isFloatingPointTy() && target_type->isIntegerTy()) {
        return target_unsigned ? builder().CreateFPToUI(value, target_type, name)
                               : builder().CreateFPToSI(value, target_type, name);
    }
    return cast_value(value, target_type, loc, name);
}

} // namespace aburi::cir2llvm
