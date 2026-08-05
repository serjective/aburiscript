#include "file.h"

#include "inst_schema.h"
#include "layout.h"

#include "../numeric/floating_cir.h"
#include "../perf_stats.h"

#include <algorithm>
#include <cassert>
#include <functional>
#include <iomanip>
#include <ostream>
#include <sstream>
#include <vector>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <variant>

namespace aburi::cir {
namespace {

void bump_cir_counter(PerfCounter counter) {
    if (auto* profiler = active_perf_profiler()) {
        profiler->add_counter(counter);
    }
}

BuiltinTypeKind canonical_builtin_type_kind(BuiltinTypeKind kind,
                                            const TargetInfo& target) {
    if (kind != BuiltinTypeKind::USize) {
        return kind;
    }
    if (target.pointer_width <= 32) {
        return BuiltinTypeKind::UInt;
    }
    if (target.pointer_width <= target.long_width) {
        return BuiltinTypeKind::ULong;
    }
    return BuiltinTypeKind::ULongLong;
}

void dump_id(std::ostream& out, uint32_t index, uint32_t generation) {
    out << '#' << index << ".g" << generation;
}

template <typename IdT>
uint64_t id_key(IdT id) {
    return (static_cast<uint64_t>(id.generation) << 32) | id.index;
}

void append_hex_escape(std::ostream& out, uint8_t byte) {
    static const char kHex[] = "0123456789ABCDEF";
    out << "\\x" << kHex[(byte >> 4) & 0xF] << kHex[byte & 0xF];
}

void dump_escaped_string(std::ostream& out, std::string_view text) {
    for (char c : text) {
        switch (c) {
            case '\n': out << "\\n"; break;
            case '\r': out << "\\r"; break;
            case '\t': out << "\\t"; break;
            case '\\': out << "\\\\"; break;
            case '"': out << "\\\""; break;
            default: out << c; break;
        }
    }
}

void dump_escaped_bytes(std::ostream& out, const LiteralByteArray& bytes) {
    for (uint8_t byte : bytes) {
        switch (byte) {
            case '\n': out << "\\n"; break;
            case '\r': out << "\\r"; break;
            case '\t': out << "\\t"; break;
            case '\\': out << "\\\\"; break;
            case '"': out << "\\\""; break;
            default:
                if (byte < 0x20 || byte >= 0x7F) {
                    append_hex_escape(out, byte);
                } else {
                    out << static_cast<char>(byte);
                }
                break;
        }
    }
}

int64_t integer_from_bytes(const LiteralByteArray& bytes) {
    int64_t value = 0;
    for (uint8_t byte : bytes) {
        value <<= 8;
        value |= static_cast<int64_t>(byte);
    }
    return value;
}

std::string qualifier_prefix(uint8_t qualifiers) {
    std::string out;
    if ((qualifiers & QualConst) != 0) out += "const ";
    if ((qualifiers & QualVolatile) != 0) out += "volatile ";
    if ((qualifiers & QualRestrict) != 0) out += "restrict ";
    if ((qualifiers & QualAtomic) != 0) out += "atomic ";
    return out;
}

std::string type_ref_prefix(TypeRef ref) {
    std::string out = qualifier_prefix(ref.qualifiers);
    if (ref.memory_space != MemorySpace::Default) {
        out += "addrspace(";
        out += memory_space_name(ref.memory_space);
        out += ") ";
    }
    return out;
}

std::string_view structured_binding_strategy_name(
    StructuredBindingStrategy strategy) {
    switch (strategy) {
        case StructuredBindingStrategy::Dependent: return "dependent";
        case StructuredBindingStrategy::Array: return "array";
        case StructuredBindingStrategy::Tuple: return "tuple";
        case StructuredBindingStrategy::Member: return "member";
        case StructuredBindingStrategy::Invalid: return "invalid";
    }
    return "invalid";
}

} // namespace

std::string_view entity_kind_name(EntityKind kind) {
    switch (kind) {
        case EntityKind::Invalid: return "Invalid";
        case EntityKind::TranslationUnit: return "TranslationUnit";
        case EntityKind::Function: return "Function";
        case EntityKind::Parameter: return "Parameter";
        case EntityKind::Variable: return "Variable";
        case EntityKind::Concept: return "Concept";
        case EntityKind::TypeAlias: return "TypeAlias";
        case EntityKind::Record: return "Record";
        case EntityKind::Enum: return "Enum";
        case EntityKind::Enumerator: return "Enumerator";
        case EntityKind::Field: return "Field";
        case EntityKind::Method: return "Method";
        case EntityKind::Constructor: return "Constructor";
        case EntityKind::Destructor: return "Destructor";
        case EntityKind::TemplateParam: return "TemplateParam";
        case EntityKind::StructuredBinding: return "StructuredBinding";
        case EntityKind::Namespace: return "Namespace";
        case EntityKind::NamespaceAlias: return "NamespaceAlias";
    }
    return "UnknownEntityKind";
}

std::string_view storage_duration_name(StorageDuration duration) {
    switch (duration) {
        case StorageDuration::None: return "none";
        case StorageDuration::Automatic: return "automatic";
        case StorageDuration::Static: return "static";
        case StorageDuration::Thread: return "thread";
        case StorageDuration::Allocated: return "allocated";
        case StorageDuration::Temporary: return "temporary";
        case StorageDuration::Parameter: return "parameter";
        case StorageDuration::Unknown: return "unknown";
    }
    return "unknown";
}

std::string_view execution_space_name(ExecutionSpace space) {
    switch (space) {
        case ExecutionSpace::Host: return "host";
        case ExecutionSpace::Device: return "device";
        case ExecutionSpace::Kernel: return "kernel";
        case ExecutionSpace::HostDevice: return "host_device";
        case ExecutionSpace::Unspecified: return "unspecified";
    }
    return "unknown";
}

std::string_view record_kind_name(RecordKind kind) {
    switch (kind) {
        case RecordKind::Struct: return "struct";
        case RecordKind::Class: return "class";
        case RecordKind::Union: return "union";
    }
    return "record";
}

std::string_view record_member_access_name(RecordMemberAccess access) {
    switch (access) {
        case RecordMemberAccess::Public: return "public";
        case RecordMemberAccess::Protected: return "protected";
        case RecordMemberAccess::Private: return "private";
    }
    return "unknown";
}

std::string_view decl_context_kind_name(DeclContextKind kind) {
    switch (kind) {
        case DeclContextKind::Invalid: return "invalid";
        case DeclContextKind::TranslationUnit: return "translation_unit";
        case DeclContextKind::Namespace: return "namespace";
        case DeclContextKind::Record: return "record";
        case DeclContextKind::Enum: return "enum";
        case DeclContextKind::Function: return "function";
        case DeclContextKind::Prototype: return "prototype";
        case DeclContextKind::TemplateParameter: return "template_parameter";
        case DeclContextKind::Block: return "block";
    }
    return "unknown";
}

std::string_view lookup_namespace_name(LookupNamespace lookup_namespace) {
    switch (lookup_namespace) {
        case LookupNamespace::None: return "none";
        case LookupNamespace::Ordinary: return "ordinary";
        case LookupNamespace::Tag: return "tag";
        case LookupNamespace::Label: return "label";
    }
    return "mixed";
}

std::string_view inst_kind_name(InstKind kind) {
    return inst_schema(kind).kind_name;
}

std::string_view terminator_kind_name(TerminatorKind kind) {
    switch (kind) {
        case TerminatorKind::Invalid: return "Invalid";
        case TerminatorKind::Return: return "Return";
        case TerminatorKind::Branch: return "Branch";
        case TerminatorKind::CondBranch: return "CondBranch";
        case TerminatorKind::Switch: return "Switch";
        case TerminatorKind::IndirectBranch: return "IndirectBranch";
        case TerminatorKind::AsmGoto: return "AsmGoto";
        case TerminatorKind::Unreachable: return "Unreachable";
        case TerminatorKind::Throw: return "Throw";
        case TerminatorKind::Rethrow: return "Rethrow";
        case TerminatorKind::Resume: return "Resume";
        case TerminatorKind::CoroSuspend: return "CoroSuspend";
        case TerminatorKind::CoroEnd: return "CoroEnd";
    }
    return "UnknownTerminatorKind";
}

std::string_view unary_op_kind_name(UnaryOpKind kind) {
    switch (kind) {
        case UnaryOpKind::Invalid: return "Invalid";
        case UnaryOpKind::Plus: return "Plus";
        case UnaryOpKind::Minus: return "Minus";
        case UnaryOpKind::LogicalNot: return "LogicalNot";
        case UnaryOpKind::BitwiseNot: return "BitwiseNot";
    }
    return "UnknownUnaryOpKind";
}

std::string_view unary_op_spelling(UnaryOpKind kind) {
    switch (kind) {
        case UnaryOpKind::Plus: return "+";
        case UnaryOpKind::Minus: return "-";
        case UnaryOpKind::LogicalNot: return "!";
        case UnaryOpKind::BitwiseNot: return "~";
        case UnaryOpKind::Invalid: break;
    }
    return "";
}

std::string_view binary_op_kind_name(BinaryOpKind kind) {
    switch (kind) {
        case BinaryOpKind::Invalid: return "Invalid";
        case BinaryOpKind::Add: return "Add";
        case BinaryOpKind::Sub: return "Sub";
        case BinaryOpKind::Mul: return "Mul";
        case BinaryOpKind::Div: return "Div";
        case BinaryOpKind::Mod: return "Mod";
        case BinaryOpKind::Less: return "Less";
        case BinaryOpKind::LessEqual: return "LessEqual";
        case BinaryOpKind::Greater: return "Greater";
        case BinaryOpKind::GreaterEqual: return "GreaterEqual";
        case BinaryOpKind::Equal: return "Equal";
        case BinaryOpKind::NotEqual: return "NotEqual";
        case BinaryOpKind::LogicalAnd: return "LogicalAnd";
        case BinaryOpKind::LogicalOr: return "LogicalOr";
        case BinaryOpKind::BitAnd: return "BitAnd";
        case BinaryOpKind::BitOr: return "BitOr";
        case BinaryOpKind::BitXor: return "BitXor";
        case BinaryOpKind::Shl: return "Shl";
        case BinaryOpKind::Shr: return "Shr";
        case BinaryOpKind::Comma: return "Comma";
    }
    return "UnknownBinaryOpKind";
}

std::string_view binary_op_spelling(BinaryOpKind kind) {
    switch (kind) {
        case BinaryOpKind::Add: return "+";
        case BinaryOpKind::Sub: return "-";
        case BinaryOpKind::Mul: return "*";
        case BinaryOpKind::Div: return "/";
        case BinaryOpKind::Mod: return "%";
        case BinaryOpKind::Less: return "<";
        case BinaryOpKind::LessEqual: return "<=";
        case BinaryOpKind::Greater: return ">";
        case BinaryOpKind::GreaterEqual: return ">=";
        case BinaryOpKind::Equal: return "==";
        case BinaryOpKind::NotEqual: return "!=";
        case BinaryOpKind::LogicalAnd: return "&&";
        case BinaryOpKind::LogicalOr: return "||";
        case BinaryOpKind::BitAnd: return "&";
        case BinaryOpKind::BitOr: return "|";
        case BinaryOpKind::BitXor: return "^";
        case BinaryOpKind::Shl: return "<<";
        case BinaryOpKind::Shr: return ">>";
        case BinaryOpKind::Comma: return ",";
        case BinaryOpKind::Invalid: break;
    }
    return "";
}

std::string_view operator_value_domain_name(OperatorValueDomain domain) {
    switch (domain) {
        case OperatorValueDomain::Unknown: return "unknown";
        case OperatorValueDomain::Bool: return "bool";
        case OperatorValueDomain::SignedInteger: return "signed_integer";
        case OperatorValueDomain::UnsignedInteger: return "unsigned_integer";
        case OperatorValueDomain::Floating: return "floating";
        case OperatorValueDomain::Complex: return "complex";
        case OperatorValueDomain::Pointer: return "pointer";
    }
    return "unknown";
}

File::File() {
    set_target_info(TargetInfo::create_host());
    names_.push_back({});
    name_generations_.push_back(0);
    types_.push_back(Type{});
    type_generations_.push_back(0);
    type_payloads_.push_back(InvalidTypePayload{});
    entities_.push_back(Entity{});
    entity_generations_.push_back(0);
    decl_contexts_.push_back(DeclContext{});
    decl_context_generations_.push_back(0);
    bindings_.push_back(Binding{});
    binding_generations_.push_back(0);
    place_facts_.push_back(PlaceFact{});
    place_fact_generations_.push_back(0);
    placeholder_result_facts_.push_back(PlaceholderResultFact{});
    placeholder_result_fact_generations_.push_back(0);
    constant_states_.push_back(ConstantStateFact{});
    constant_state_generations_.push_back(0);
    closure_identities_.push_back(ClosureIdentityFact{});
    closure_identity_generations_.push_back(0);
    switch_facts_.push_back(SwitchFact{});
    switch_fact_generations_.push_back(0);
    module_units_.push_back(ModuleUnitFact{});
    module_unit_generations_.push_back(0);
    insts_.push_back(Inst{});
    inst_generations_.push_back(0);
    payloads_.push_back(InstPayload{});
    inline_asm_payloads_.push_back(InlineAsmPayload{});
    inline_asm_payload_generations_.push_back(0);
    blocks_.push_back(Block{});
    block_generations_.push_back(0);
    functions_.push_back(Function{});
    function_generations_.push_back(0);
    generics_.push_back(Generic{});
    generic_generations_.push_back(0);
    specifics_.push_back(Specific{});
    specific_generations_.push_back(0);
    value_expressions_.push_back(TemplateValueExpression{});
    value_expression_generations_.push_back(0);
}

void File::set_target_info(std::shared_ptr<TargetInfo> target) {
    target_ = target ? std::move(target) : TargetInfo::create_host();
    abi_policy_ = abi_policy_for_target(*target_);
}

const TargetInfo& File::target_info() const {
    if (!target_) {
        static std::shared_ptr<TargetInfo> fallback = TargetInfo::create_host();
        return *fallback;
    }
    return *target_;
}

File::TransactionId File::begin_transaction() {
    Transaction transaction;
#ifndef NDEBUG
    if (transaction_integrity_checks_) {
        transaction.rollback_fingerprint = debug_semantic_fingerprint();
    }
#endif
    transaction.id = next_transaction_id_++;
    if (next_transaction_id_ == 0) {
        next_transaction_id_ = 1;
    }
    transaction.names_size = names_.size();
    transaction.types_size = types_.size();
    transaction.type_payloads_size = type_payloads_.size();
    transaction.entities_size = entities_.size();
    transaction.decl_contexts_size = decl_contexts_.size();
    transaction.bindings_size = bindings_.size();
    transaction.place_facts_size = place_facts_.size();
    transaction.placeholder_result_facts_size =
        placeholder_result_facts_.size();
    transaction.constant_states_size = constant_states_.size();
    transaction.closure_identities_size = closure_identities_.size();
    transaction.switch_facts_size = switch_facts_.size();
    transaction.coroutine_facts_size = coroutine_facts_.size();
    transaction.module_units_size = module_units_.size();
    transaction.insts_size = insts_.size();
    transaction.payloads_size = payloads_.size();
    transaction.inline_asm_payloads_size = inline_asm_payloads_.size();
    transaction.operands_size = operands_.size();
    transaction.blocks_size = blocks_.size();
    transaction.functions_size = functions_.size();
    transaction.generics_size = generics_.size();
    transaction.specifics_size = specifics_.size();
    transaction.value_expressions_size = value_expressions_.size();
    transaction.module_asm_size = module_asm_.size();
    transaction.errors_size = errors_.size();
    transaction.warnings_size = warnings_.size();
    transaction.notes_size = notes_.size();
    transaction.prelude_mark = prelude_mark_;
    transaction.active_module = active_module_;
    transaction.visibility_unit = visibility_unit_;
    transaction.visible_units = visible_units_;
    transaction.module_redeclared_entities = module_redeclared_entities_;
    transaction.imported_definition_entities = imported_definition_entities_;
    transaction.coroutines_lowered = coroutines_lowered_;
    transactions_.push_back(std::move(transaction));
    return transactions_.back().id;
}

void File::commit_transaction(TransactionId id) {
    assert(!transactions_.empty() && transactions_.back().id == id &&
           "CIR transactions must commit in LIFO order");
    if (transactions_.empty() || transactions_.back().id != id) {
        return;
    }
    Transaction transaction = std::move(transactions_.back());
    transactions_.pop_back();
    merge_committed_transaction(std::move(transaction));
}

void File::rollback_transaction(TransactionId id) {
    assert(!transactions_.empty() && transactions_.back().id == id &&
           "CIR transactions must roll back in LIFO order");
    if (transactions_.empty() || transactions_.back().id != id) {
        return;
    }
    Transaction transaction = std::move(transactions_.back());
    transactions_.pop_back();

    for (auto& [index, entity] : transaction.entity_mutations) {
        if (index < entities_.size()) {
            entities_[index] = std::move(entity);
        }
    }

    for (auto& [index, context] : transaction.decl_context_mutations) {
        if (index < decl_contexts_.size()) {
            decl_contexts_[index] = std::move(context);
        }
    }
    for (size_t position = transaction.decl_context_deltas.size();
         position > 0;
         --position) {
        undo_decl_context_delta(
            transaction.decl_context_deltas[position - 1]);
    }
    for (auto& [index, binding] : transaction.binding_mutations) {
        if (index < bindings_.size()) {
            bindings_[index] = std::move(binding);
        }
    }
    for (auto& [index, fact] : transaction.place_fact_mutations) {
        if (index < place_facts_.size()) {
            place_facts_[index] = std::move(fact);
        }
    }
    for (auto& [index, fact] :
         transaction.placeholder_result_fact_mutations) {
        if (index < placeholder_result_facts_.size()) {
            placeholder_result_facts_[index] = std::move(fact);
        }
    }
    for (auto& [index, fact] : transaction.closure_identity_mutations) {
        if (index < closure_identities_.size()) {
            closure_identities_[index] = std::move(fact);
        }
    }
    for (auto& [index, fact] : transaction.coroutine_fact_mutations) {
        if (index < coroutine_facts_.size()) {
            coroutine_facts_[index] = std::move(fact);
        }
    }
    for (auto& [index, fact] : transaction.module_unit_mutations) {
        if (index < module_units_.size()) {
            module_units_[index] = std::move(fact);
        }
    }
    for (auto& [index, inst] : transaction.inst_mutations) {
        if (index < insts_.size()) {
            insts_[index] = std::move(inst);
        }
    }
    for (auto& [index, block] : transaction.block_mutations) {
        if (index < blocks_.size()) {
            blocks_[index] = std::move(block);
        }
    }
    for (auto& [index, function] : transaction.function_mutations) {
        if (index < functions_.size()) {
            functions_[index] = std::move(function);
        }
    }
    for (auto& [key, facts] : transaction.record_fact_mutations) {
        if (facts.has_value()) {
            record_facts_[key] = std::move(*facts);
        } else {
            record_facts_.erase(key);
        }
    }
    for (auto& [key, facts] : transaction.objc_interface_fact_mutations) {
        if (facts.has_value()) {
            objc_interface_facts_[key] = std::move(*facts);
        } else {
            objc_interface_facts_.erase(key);
        }
    }
    for (auto& [key, fact] :
         transaction.defaulted_comparison_fact_mutations) {
        if (fact.has_value()) {
            defaulted_comparison_facts_[key] = std::move(*fact);
        } else {
            defaulted_comparison_facts_.erase(key);
        }
    }
    for (auto& [key, fact] : transaction.structured_binding_fact_mutations) {
        if (fact.has_value()) {
            structured_binding_facts_[key] = std::move(*fact);
        } else {
            structured_binding_facts_.erase(key);
        }
    }
    for (auto& [key, fact] : transaction.template_specialization_mutations) {
        if (fact.has_value()) {
            template_specializations_[key] = std::move(*fact);
        } else {
            template_specializations_.erase(key);
        }
    }
    for (auto& [key, remap] :
         transaction.module_import_provenance_mutations) {
        if (remap.has_value()) {
            module_import_provenance_[key] = std::move(*remap);
        } else {
            module_import_provenance_.erase(key);
        }
    }

    for (const std::string& key : transaction.inserted_name_keys) {
        name_index_.erase(key);
    }
    for (const auto& [hash, id] : transaction.inserted_type_entries) {
        auto range = type_index_.equal_range(hash);
        for (auto it = range.first; it != range.second; ++it) {
            if (it->second == id) {
                type_index_.erase(it);
                break;
            }
        }
    }
    for (const auto& [hash, id] :
         transaction.inserted_value_expression_entries) {
        auto range = value_expression_index_.equal_range(hash);
        for (auto it = range.first; it != range.second; ++it) {
            if (it->second == id) {
                value_expression_index_.erase(it);
                break;
            }
        }
    }
#ifdef ABURI_VERIFY_TYPE_INTERN
    for (const std::string& key : transaction.inserted_type_keys) {
        verify_type_index_.erase(key);
    }
#endif
    for (BuiltinTypeKind kind : transaction.inserted_builtin_type_keys) {
        builtin_types_.erase(kind);
    }

    rollback_table_sizes(transaction);
    prelude_mark_ = transaction.prelude_mark;
    active_module_ = transaction.active_module;
    visibility_unit_ = transaction.visibility_unit;
    visible_units_ = std::move(transaction.visible_units);
    module_redeclared_entities_ =
        std::move(transaction.module_redeclared_entities);
    imported_definition_entities_ =
        std::move(transaction.imported_definition_entities);
    coroutines_lowered_ = transaction.coroutines_lowered;
#ifndef NDEBUG
    if (transaction.rollback_fingerprint.has_value()) {
        assert(debug_semantic_fingerprint() ==
                   *transaction.rollback_fingerprint &&
               "CIR transaction rollback changed the live semantic graph");
    }
#endif
}


void File::record_entity_mutation(EntityId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.entities_size ||
        transaction.entity_mutations.contains(id.index)) {
        return;
    }
    transaction.entity_mutations.emplace(id.index, entities_[id.index]);
}

void File::record_decl_context_mutation(DeclContextId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.decl_contexts_size ||
        transaction.decl_context_mutations.contains(id.index)) {
        return;
    }
    transaction.decl_context_mutations.emplace(id.index, decl_contexts_[id.index]);
}

std::unordered_map<uint64_t, BindingId>& File::decl_context_index(
    DeclContext& context,
    DeclContextIndexKind kind) {
    switch (kind) {
        case DeclContextIndexKind::OrdinaryLatest:
            return context.ordinary_latest_bindings;
        case DeclContextIndexKind::OrdinaryValue:
            return context.ordinary_value_bindings;
        case DeclContextIndexKind::OrdinaryCallable:
            return context.ordinary_callable_bindings;
        case DeclContextIndexKind::OrdinaryTypeName:
            return context.ordinary_type_name_bindings;
        case DeclContextIndexKind::OrdinaryTemplateName:
            return context.ordinary_template_name_bindings;
        case DeclContextIndexKind::OrdinaryNamespace:
            return context.ordinary_namespace_bindings;
        case DeclContextIndexKind::Tag:
            return context.tag_bindings;
        case DeclContextIndexKind::Label:
            return context.label_bindings;
    }
    return context.ordinary_latest_bindings;
}

File::Transaction* File::decl_context_delta_journal(DeclContextId id) {
    if (transactions_.empty() || !valid(id)) {
        return nullptr;
    }
    Transaction& transaction = transactions_.back();

    if (id.index >= transaction.decl_contexts_size ||
        transaction.decl_context_mutations.contains(id.index)) {
        return nullptr;
    }
    return &transaction;
}

void File::journal_decl_context_append(DeclContextId id,
                                       DeclContextDelta::Kind kind) {
    if (Transaction* transaction = decl_context_delta_journal(id)) {
        DeclContextDelta delta;
        delta.context = id.index;
        delta.kind = kind;
        transaction->decl_context_deltas.push_back(delta);
    }
}

void File::assign_decl_context_index(DeclContextId id,
                                     DeclContextIndexKind kind,
                                     uint64_t key,
                                     BindingId binding_id) {
    if (!valid(id)) {
        return;
    }
    std::unordered_map<uint64_t, BindingId>& index =
        decl_context_index(decl_contexts_[id.index], kind);
    if (Transaction* transaction = decl_context_delta_journal(id)) {
        DeclContextDelta delta;
        delta.context = id.index;
        delta.kind = DeclContextDelta::Kind::IndexAssigned;
        delta.index = kind;
        delta.key = key;
        auto previous = index.find(key);
        delta.had_previous = previous != index.end();
        if (delta.had_previous) {
            delta.previous = previous->second;
        }
        transaction->decl_context_deltas.push_back(delta);
    }
    index[key] = binding_id;
}

void File::undo_decl_context_delta(const DeclContextDelta& delta) {
    if (delta.context >= decl_contexts_.size()) {
        return;
    }
    DeclContext& context = decl_contexts_[delta.context];
    switch (delta.kind) {
        case DeclContextDelta::Kind::BindingAppended:
            if (!context.bindings.empty()) {
                context.bindings.pop_back();
            }
            return;
        case DeclContextDelta::Kind::ChildAppended:
            if (!context.children.empty()) {
                context.children.pop_back();
            }
            return;
        case DeclContextDelta::Kind::UsingDirectiveAppended:
            if (!context.using_directives.empty()) {
                context.using_directives.pop_back();
            }
            context.using_directive_origins.resize(
                context.using_directives.size());
            return;
        case DeclContextDelta::Kind::IndexAssigned: {
            std::unordered_map<uint64_t, BindingId>& index =
                decl_context_index(context, delta.index);
            if (delta.had_previous) {
                index[delta.key] = delta.previous;
            } else {
                index.erase(delta.key);
            }
            return;
        }
    }
}

void File::record_binding_mutation(BindingId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.bindings_size ||
        transaction.binding_mutations.contains(id.index)) {
        return;
    }
    transaction.binding_mutations.emplace(id.index, bindings_[id.index]);
}

void File::record_place_fact_mutation(PlaceFactId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.place_facts_size ||
        transaction.place_fact_mutations.contains(id.index)) {
        return;
    }
    transaction.place_fact_mutations.emplace(id.index, place_facts_[id.index]);
}

void File::record_placeholder_result_fact_mutation(
    PlaceholderResultFactId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.placeholder_result_facts_size ||
        transaction.placeholder_result_fact_mutations.contains(id.index)) {
        return;
    }
    transaction.placeholder_result_fact_mutations.emplace(
        id.index, placeholder_result_facts_[id.index]);
}

void File::record_closure_identity_mutation(ClosureIdentityId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.closure_identities_size ||
        transaction.closure_identity_mutations.contains(id.index)) {
        return;
    }
    transaction.closure_identity_mutations.emplace(
        id.index, closure_identities_[id.index]);
}

void File::record_coroutine_fact_mutation(size_t index) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (index >= transaction.coroutine_facts_size ||
        transaction.coroutine_fact_mutations.contains(
            static_cast<uint32_t>(index))) {
        return;
    }
    transaction.coroutine_fact_mutations.emplace(
        static_cast<uint32_t>(index), coroutine_facts_[index]);
}

void File::record_module_unit_mutation(ModuleAttachmentId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.module_units_size ||
        transaction.module_unit_mutations.contains(id.index)) {
        return;
    }
    transaction.module_unit_mutations.emplace(id.index,
                                              module_units_[id.index]);
}

void File::record_inst_mutation(InstId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.insts_size ||
        transaction.inst_mutations.contains(id.index)) {
        return;
    }
    transaction.inst_mutations.emplace(id.index, insts_[id.index]);
}

void File::record_block_mutation(BlockId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.blocks_size ||
        transaction.block_mutations.contains(id.index)) {
        return;
    }
    transaction.block_mutations.emplace(id.index, blocks_[id.index]);
}

void File::record_function_mutation(FunctionId id) {
    if (transactions_.empty() || !valid(id)) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (id.index >= transaction.functions_size ||
        transaction.function_mutations.contains(id.index)) {
        return;
    }
    transaction.function_mutations.emplace(id.index, functions_[id.index]);
}

void File::record_record_facts_mutation(uint64_t key) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (transaction.record_fact_mutations.contains(key)) {
        return;
    }
    auto found = record_facts_.find(key);
    if (found == record_facts_.end()) {
        transaction.record_fact_mutations.emplace(key, std::nullopt);
    } else {
        transaction.record_fact_mutations.emplace(key, found->second);
    }
}

void File::record_objc_interface_facts_mutation(uint64_t key) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (transaction.objc_interface_fact_mutations.contains(key)) {
        return;
    }
    auto found = objc_interface_facts_.find(key);
    if (found == objc_interface_facts_.end()) {
        transaction.objc_interface_fact_mutations.emplace(key, std::nullopt);
    } else {
        transaction.objc_interface_fact_mutations.emplace(key, found->second);
    }
}

void File::record_defaulted_comparison_fact_mutation(uint64_t key) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (transaction.defaulted_comparison_fact_mutations.contains(key)) {
        return;
    }
    auto found = defaulted_comparison_facts_.find(key);
    if (found == defaulted_comparison_facts_.end()) {
        transaction.defaulted_comparison_fact_mutations.emplace(
            key, std::nullopt);
    } else {
        transaction.defaulted_comparison_fact_mutations.emplace(
            key, found->second);
    }
}

void File::record_structured_binding_fact_mutation(uint64_t key) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (transaction.structured_binding_fact_mutations.contains(key)) {
        return;
    }
    auto found = structured_binding_facts_.find(key);
    if (found == structured_binding_facts_.end()) {
        transaction.structured_binding_fact_mutations.emplace(
            key, std::nullopt);
    } else {
        transaction.structured_binding_fact_mutations.emplace(
            key, found->second);
    }
}

void File::record_template_specialization_mutation(uint64_t key) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    if (transaction.template_specialization_mutations.contains(key)) {
        return;
    }
    auto found = template_specializations_.find(key);
    if (found == template_specializations_.end()) {
        transaction.template_specialization_mutations.emplace(key,
                                                             std::nullopt);
    } else {
        transaction.template_specialization_mutations.emplace(key,
                                                             found->second);
    }
}

void File::record_module_import_provenance_mutation(std::string_view key) {
    if (transactions_.empty()) {
        return;
    }
    Transaction& transaction = transactions_.back();
    std::string owned_key(key);
    if (transaction.module_import_provenance_mutations.contains(owned_key)) {
        return;
    }
    auto found = module_import_provenance_.find(owned_key);
    if (found == module_import_provenance_.end()) {
        transaction.module_import_provenance_mutations.emplace(
            std::move(owned_key), std::nullopt);
    } else {
        transaction.module_import_provenance_mutations.emplace(
            std::move(owned_key), found->second);
    }
}

void File::merge_committed_transaction(Transaction transaction) {
    if (transactions_.empty()) {
        return;
    }

    Transaction& parent = transactions_.back();
    parent.inserted_name_keys.insert(parent.inserted_name_keys.end(),
                                     transaction.inserted_name_keys.begin(),
                                     transaction.inserted_name_keys.end());
    parent.inserted_type_entries.insert(
        parent.inserted_type_entries.end(),
        transaction.inserted_type_entries.begin(),
        transaction.inserted_type_entries.end());
    parent.inserted_value_expression_entries.insert(
        parent.inserted_value_expression_entries.end(),
        transaction.inserted_value_expression_entries.begin(),
        transaction.inserted_value_expression_entries.end());
#ifdef ABURI_VERIFY_TYPE_INTERN
    parent.inserted_type_keys.insert(parent.inserted_type_keys.end(),
                                     transaction.inserted_type_keys.begin(),
                                     transaction.inserted_type_keys.end());
#endif
    parent.inserted_builtin_type_keys.insert(
        parent.inserted_builtin_type_keys.end(),
        transaction.inserted_builtin_type_keys.begin(),
        transaction.inserted_builtin_type_keys.end());

    for (auto& [index, value] : transaction.entity_mutations) {
        if (index < parent.entities_size && !parent.entity_mutations.contains(index)) {
            parent.entity_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.decl_context_mutations) {
        if (index < parent.decl_contexts_size &&
            !parent.decl_context_mutations.contains(index)) {
            parent.decl_context_mutations.emplace(index, std::move(value));
        }
    }

    for (const DeclContextDelta& delta : transaction.decl_context_deltas) {
        if (delta.context < parent.decl_contexts_size &&
            !parent.decl_context_mutations.contains(delta.context)) {
            parent.decl_context_deltas.push_back(delta);
        }
    }
    for (auto& [index, value] : transaction.binding_mutations) {
        if (index < parent.bindings_size &&
            !parent.binding_mutations.contains(index)) {
            parent.binding_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.place_fact_mutations) {
        if (index < parent.place_facts_size &&
            !parent.place_fact_mutations.contains(index)) {
            parent.place_fact_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] :
         transaction.placeholder_result_fact_mutations) {
        if (index < parent.placeholder_result_facts_size &&
            !parent.placeholder_result_fact_mutations.contains(index)) {
            parent.placeholder_result_fact_mutations.emplace(
                index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.closure_identity_mutations) {
        if (index < parent.closure_identities_size &&
            !parent.closure_identity_mutations.contains(index)) {
            parent.closure_identity_mutations.emplace(index,
                                                       std::move(value));
        }
    }
    for (auto& [index, value] : transaction.coroutine_fact_mutations) {
        if (index < parent.coroutine_facts_size &&
            !parent.coroutine_fact_mutations.contains(index)) {
            parent.coroutine_fact_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.module_unit_mutations) {
        if (index < parent.module_units_size &&
            !parent.module_unit_mutations.contains(index)) {
            parent.module_unit_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.inst_mutations) {
        if (index < parent.insts_size && !parent.inst_mutations.contains(index)) {
            parent.inst_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.block_mutations) {
        if (index < parent.blocks_size && !parent.block_mutations.contains(index)) {
            parent.block_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [index, value] : transaction.function_mutations) {
        if (index < parent.functions_size && !parent.function_mutations.contains(index)) {
            parent.function_mutations.emplace(index, std::move(value));
        }
    }
    for (auto& [key, value] : transaction.record_fact_mutations) {
        if (!parent.record_fact_mutations.contains(key)) {
            parent.record_fact_mutations.emplace(key, std::move(value));
        }
    }
    for (auto& [key, value] : transaction.objc_interface_fact_mutations) {
        if (!parent.objc_interface_fact_mutations.contains(key)) {
            parent.objc_interface_fact_mutations.emplace(key, std::move(value));
        }
    }
    for (auto& [key, value] :
         transaction.defaulted_comparison_fact_mutations) {
        if (!parent.defaulted_comparison_fact_mutations.contains(key)) {
            parent.defaulted_comparison_fact_mutations.emplace(
                key, std::move(value));
        }
    }
    for (auto& [key, value] :
         transaction.structured_binding_fact_mutations) {
        if (!parent.structured_binding_fact_mutations.contains(key)) {
            parent.structured_binding_fact_mutations.emplace(
                key, std::move(value));
        }
    }
    for (auto& [key, value] :
         transaction.template_specialization_mutations) {
        if (!parent.template_specialization_mutations.contains(key)) {
            parent.template_specialization_mutations.emplace(key,
                                                            std::move(value));
        }
    }
    for (auto& [key, value] :
         transaction.module_import_provenance_mutations) {
        if (!parent.module_import_provenance_mutations.contains(key)) {
            parent.module_import_provenance_mutations.emplace(
                key, std::move(value));
        }
    }
}

void File::rollback_table_sizes(const Transaction& transaction) {
    names_.resize(transaction.names_size);
    types_.resize(transaction.types_size);
    type_payloads_.resize(transaction.type_payloads_size);
    entities_.resize(transaction.entities_size);
    decl_contexts_.resize(transaction.decl_contexts_size);
    bindings_.resize(transaction.bindings_size);
    place_facts_.resize(transaction.place_facts_size);
    placeholder_result_facts_.resize(
        transaction.placeholder_result_facts_size);
    constant_states_.resize(transaction.constant_states_size);
    closure_identities_.resize(transaction.closure_identities_size);
    switch_facts_.resize(transaction.switch_facts_size);
    coroutine_facts_.resize(transaction.coroutine_facts_size);
    module_units_.resize(transaction.module_units_size);
    insts_.resize(transaction.insts_size);
    payloads_.resize(transaction.payloads_size);
    inline_asm_payloads_.resize(transaction.inline_asm_payloads_size);
    operands_.resize(transaction.operands_size);
    blocks_.resize(transaction.blocks_size);
    functions_.resize(transaction.functions_size);
    generics_.resize(transaction.generics_size);
    specifics_.resize(transaction.specifics_size);
    value_expressions_.resize(transaction.value_expressions_size);
    errors_.resize(std::max(transaction.errors_size, error_floor_));
    warnings_.resize(transaction.warnings_size);
    notes_.resize(std::max(transaction.notes_size, note_floor_));
    module_asm_.resize(transaction.module_asm_size);
}

NameId File::intern_name(std::string_view spelling_view) {
    auto found = name_index_.find(spelling_view);
    if (found != name_index_.end()) {
        bump_cir_counter(PerfCounter::NameInternHits);
        return found->second;
    }
    bump_cir_counter(PerfCounter::NamesInterned);
    std::string spelling(spelling_view);
    if (!transactions_.empty()) {
        transactions_.back().inserted_name_keys.push_back(spelling);
    }
    uint32_t index = static_cast<uint32_t>(names_.size());
    uint32_t generation = 1;
    if (index < name_generations_.size()) {
        generation = name_generations_[index] + 1;
        if (generation == 0) {
            generation = 1;
        }
        name_generations_[index] = generation;
    } else {
        name_generations_.push_back(generation);
    }
    names_.push_back(spelling);
    NameId id{index, generation};
    name_index_.emplace(std::move(spelling), id);
    return id;
}

const std::string& File::name(NameId id) const {
    static const std::string empty;
    if (!valid(id)) {
        return empty;
    }
    return names_[id.index];
}

TypeId File::builtin_type(BuiltinTypeKind kind) {

    kind = canonical_builtin_type_kind(kind, target_info());
    auto found = builtin_types_.find(kind);
    if (found != builtin_types_.end()) {
        return found->second;
    }

    std::string spelling(builtin_type_kind_name(kind));
    NameId name = intern_name(spelling);
    BuiltinTypePayload payload;
    payload.kind = kind;
    payload.spelling = spelling;

    TypeSpec spec;
    spec.kind = TypeKind::Builtin;
    spec.payload = std::move(payload);
    spec.debug_name = name;

    TypeId id = intern_type(std::move(spec));
    if (!transactions_.empty()) {
        transactions_.back().inserted_builtin_type_keys.push_back(kind);
    }
    builtin_types_.emplace(kind, id);
    return id;
}

TypeId File::builtin_type(BuiltinTypeKind kind) const {
    kind = canonical_builtin_type_kind(kind, target_info());
    auto found = builtin_types_.find(kind);
    return found != builtin_types_.end() ? found->second : TypeId{};
}

TypeId File::builtin_type(std::string_view spelling) {
    return builtin_type(builtin_type_kind_from_spelling(spelling));
}

TypeId File::unknown_type() {
    static const std::string spelling = "<unknown>";
    NameId name = intern_name(spelling);

    TypeSpec spec;
    spec.kind = TypeKind::Unknown;
    spec.payload = UnknownTypePayload{spelling};
    spec.debug_name = name;
    return intern_type(std::move(spec));
}

TypeId File::dependent_type(const std::string& spelling) {
    NameId name = intern_name(spelling);

    TypeSpec spec;
    spec.kind = TypeKind::Dependent;
    spec.payload = DependentTypePayload{name};
    spec.debug_name = name;
    return intern_type(std::move(spec));
}

TypeId File::dependent_name_type(TypeRef qualifier_type,
                                 std::string_view member_name,
                                 std::vector<TemplateArgument> template_arguments,
                                 bool is_current_instantiation) {
    std::string spelling =
        format_type(qualifier_type) + "::" + std::string(member_name);
    NameId member = intern_name(member_name);
    NameId debug = intern_name(spelling);
    for (TemplateArgument& argument : template_arguments) {
        canonicalize_template_value_expression(
            argument.dependent_value_expr);
        canonicalize_template_value_expression(
            argument.generated_pack_count_expr);
    }

    TypeSpec spec;
    spec.kind = TypeKind::DependentName;
    spec.payload = DependentNameTypePayload{
        qualifier_type,
        member,
        std::move(template_arguments),
        is_current_instantiation};
    spec.debug_name = debug;
    return intern_type(std::move(spec));
}

TypeId File::template_specialization_type(
    NameId template_name,
    EntityId primary_template,
    std::vector<TemplateArgument> arguments,
    bool is_dependent,
    bool is_class_template_placeholder,
    TemplateValueExpression splice_operand) {
    for (TemplateArgument& argument : arguments) {
        canonicalize_template_value_expression(argument.dependent_value_expr);
        canonicalize_template_value_expression(
            argument.generated_pack_count_expr);
    }
    canonicalize_template_value_expression(splice_operand);

    TypeSpec spec;
    spec.kind = TypeKind::TemplateSpecialization;
    spec.payload = TemplateSpecializationTypePayload{
        template_name,
        primary_template,
        std::move(arguments),
        std::move(splice_operand),
        is_dependent,
        is_class_template_placeholder};
    spec.debug_name = template_name;
    return intern_type(std::move(spec));
}

TypeId File::alias_specialization_type(
    NameId template_name,
    EntityId alias_template,
    std::vector<TemplateArgument> arguments,
    TypeRef associated_type) {
    if (!associated_type.valid() || !valid(associated_type.type)) {
        return {};
    }
    for (TemplateArgument& argument : arguments) {
        canonicalize_template_value_expression(argument.dependent_value_expr);
        canonicalize_template_value_expression(
            argument.generated_pack_count_expr);
    }

    TypeSpec spec;
    spec.kind = TypeKind::AliasSpecialization;
    spec.payload = AliasSpecializationTypePayload{
        template_name,
        alias_template,
        std::move(arguments),
        associated_type};
    spec.debug_name = template_name;
    spec.canonical = canonical_type(associated_type.type);
    spec.desugared = desugared_type(associated_type.type);
    spec.resolved = resolved_type(associated_type.type);
    spec.dependency.add(DependencyFlag::InstantiationDependent);
    spec.dependency.add(DependencyFlag::RequiresInstantiation);
    return intern_type(std::move(spec));
}

TypeRef File::type_ref(TypeId type, uint8_t qualifiers, MemorySpace memory_space) const {
    return TypeRef{type, qualifiers, memory_space};
}

TypeRef File::entity_type_ref(EntityId id) const {
    if (!valid(id)) {
        return {};
    }
    const Entity& record = entity(id);
    return type_ref(record.type, record.qualifiers, record.memory_space);
}

TypeRef File::qualified_type(TypeId type, uint8_t qualifiers) const {
    return type_ref(type, qualifiers);
}

TypeRef File::memory_type_ref(TypeId type, MemorySpace memory_space) const {
    return type_ref(type, QualNone, memory_space);
}

ValueExprId File::intern_template_value_expression(
    TemplateValueExpression expression) {
    if (!expression.valid()) {
        return {};
    }
    for (TemplateValueExprNode& node : expression.nodes) {
        for (TemplateArgument& argument :
             node.template_arguments.values()) {
            canonicalize_template_argument_value_expressions(argument);
        }
    }
    if (valid(expression.canonical_id)) {
        const TemplateValueExpression& canonical =
            value_expressions_[expression.canonical_id.index];
        if (template_value_expressions_structurally_equal(canonical,
                                                          expression)) {
            return expression.canonical_id;
        }
    }
    expression.canonical_id = {};
    uint64_t hash = template_value_expression_structural_hash(expression);
    auto candidates = value_expression_index_.equal_range(hash);
    for (auto it = candidates.first; it != candidates.second; ++it) {
        if (valid(it->second) &&
            template_value_expressions_structurally_equal(
                value_expressions_[it->second.index], expression)) {
            return it->second;
        }
    }

    ValueExprId id = add_record<TemplateValueExpression, ValueExprId>(
        value_expressions_, value_expression_generations_,
        std::move(expression));
    value_expressions_[id.index].canonical_id = id;
    value_expression_index_.emplace(hash, id);
    if (!transactions_.empty()) {
        transactions_.back().inserted_value_expression_entries.push_back(
            {hash, id});
    }
    return id;
}

ValueExprId File::canonicalize_template_value_expression(
    TemplateValueExpression& expression) {
    if (!expression.valid()) {
        expression.canonical_id = {};
        return {};
    }
    for (TemplateValueExprNode& node : expression.nodes) {
        for (TemplateArgument& argument :
             node.template_arguments.values()) {
            canonicalize_template_argument_value_expressions(argument);
        }
    }
    if (valid(expression.canonical_id)) {
        const TemplateValueExpression& canonical =
            value_expressions_[expression.canonical_id.index];
        if (template_value_expressions_structurally_equal(canonical,
                                                          expression)) {
            return expression.canonical_id;
        }
    }
    expression.canonical_id = {};
    expression.canonical_id = intern_template_value_expression(expression);
    return expression.canonical_id;
}

TemplateValueExprNode File::template_integer_expression_node(
    IntegerValue value,
    TypeRef result_type) const {
    TypeId resolved = resolved_type(result_type.type);
    if (valid(resolved) && is_integer_like_type(*this, resolved)) {
        IntegerTypeShape shape = integer_shape_for_type(*this, resolved);
        value = template_value_kind_for_type(resolved) ==
                TemplateValueKind::Boolean
            ? IntegerValue::from_unsigned(value.is_zero() ? 0 : 1,
                                          shape.bit_width)
            : value.cast(shape.bit_width, shape.is_unsigned);
    }

    TemplateValueExprNode node;
    node.kind = TemplateValueExprKind::Integer;
    node.integer_value = value;
    node.result_type = result_type;
    return node;
}

void File::canonicalize_template_argument_value_expressions(
    TemplateArgument& argument) {
    for (TemplateArgument& element : argument.value_elements) {
        canonicalize_template_argument_value_expressions(element);
    }
    if (argument.unconverted_value_alternative) {
        canonicalize_template_argument_value_expressions(
            *argument.unconverted_value_alternative);
    }
    canonicalize_template_value_expression(argument.dependent_value_expr);
    canonicalize_template_value_expression(argument.generated_pack_count_expr);
}

const TemplateValueExpression& File::template_value_expression(
    ValueExprId id) const {
    static const TemplateValueExpression invalid;
    return valid(id) ? value_expressions_[id.index] : invalid;
}

TypeId File::pointer_type(TypeId pointee) {
    return pointer_type(type_ref(pointee));
}

TypeId File::pointer_type(TypeRef pointee) {
    TypeSpec spec;
    spec.kind = TypeKind::Pointer;
    spec.payload = PointerTypePayload{pointee};
    return intern_type(std::move(spec));
}

TypeId File::block_pointer_type(TypeRef pointee) {
    TypeSpec spec;
    spec.kind = TypeKind::BlockPointer;
    spec.payload = BlockPointerTypePayload{pointee};
    return intern_type(std::move(spec));
}

TypeId File::reference_type(TypeRef referred, ReferenceKind reference_kind) {
    TypeId referred_type = resolved_type(referred.type);
    if (valid(referred_type)) {
        TypeKind referred_kind = type(referred_type).kind;
        if (referred_kind == TypeKind::LValueReference ||
            referred_kind == TypeKind::RValueReference) {

            ReferenceKind collapsed =
                (referred_kind == TypeKind::LValueReference ||
                 reference_kind == ReferenceKind::LValue)
                    ? ReferenceKind::LValue
                    : ReferenceKind::RValue;
            return reference_type(reference_referred_ref(referred_type),
                                  collapsed);
        }
    }
    TypeSpec spec;
    spec.kind = reference_kind == ReferenceKind::LValue
        ? TypeKind::LValueReference
        : TypeKind::RValueReference;
    spec.payload = ReferenceTypePayload{referred, reference_kind};
    return intern_type(std::move(spec));
}

TypeId File::member_pointer_type(TypeRef class_type, TypeRef member_type) {
    TypeSpec spec;
    spec.kind = TypeKind::MemberPointer;
    spec.payload = MemberPointerTypePayload{class_type, member_type};
    return intern_type(std::move(spec));
}

TypeId File::auto_type(AutoTypeFlavor flavor) {
    TypeSpec spec;
    spec.kind = TypeKind::Auto;
    spec.payload = AutoTypePayload{flavor};
    return intern_type(std::move(spec));
}

TypeId File::typeof_expr_type(InstId expr) {
    TypeSpec spec;
    spec.kind = TypeKind::TypeofExpr;
    spec.payload = TypeofExprTypePayload{expr};
    return intern_type(std::move(spec));
}

TypeId File::decltype_expr_type(InstId expr,
                                bool use_declared_type_rule,
                                DecltypeOperandCategory operand_category,
                                TypeRef operand_type,
                                TypeRef dependent_value_qualifier,
                                NameId dependent_value_name,
                                TemplateValueExpression operand_expression) {
    canonicalize_template_value_expression(operand_expression);
    TypeSpec spec;
    spec.kind = TypeKind::DecltypeExpr;
    spec.payload = DecltypeExprTypePayload{
        expr,
        use_declared_type_rule,
        operand_category,
        operand_type,
        dependent_value_qualifier,
        dependent_value_name,
        std::move(operand_expression)};
    return intern_type(std::move(spec));
}

TypeId File::builtin_type_transform_type(
    BuiltinTypeTransformKind transform_kind,
    TypeRef operand_type) {
    TypeSpec spec;
    spec.kind = TypeKind::BuiltinTransform;
    spec.payload = BuiltinTypeTransformTypePayload{transform_kind,
                                                   operand_type};
    spec.dependency.add(DependencyFlag::TypeDependent);
    spec.dependency.add(DependencyFlag::InstantiationDependent);
    spec.dependency.add(DependencyFlag::RequiresInstantiation);
    return intern_type(std::move(spec));
}

TypeId File::builtin_pack_element_type(
    std::vector<TemplateArgument> arguments) {
    for (TemplateArgument& argument : arguments) {
        canonicalize_template_value_expression(
            argument.dependent_value_expr);
    }
    TypeSpec spec;
    spec.kind = TypeKind::BuiltinPackElement;
    spec.payload =
        BuiltinPackElementTypePayload{std::move(arguments)};
    spec.dependency.add(DependencyFlag::TypeDependent);
    spec.dependency.add(DependencyFlag::InstantiationDependent);
    spec.dependency.add(DependencyFlag::RequiresInstantiation);
    return intern_type(std::move(spec));
}

TypeId File::array_type(TypeId element, std::optional<size_t> size) {
    return array_type(type_ref(element),
                      size.has_value() ? ArraySizeKind::Constant : ArraySizeKind::Incomplete,
                      size);
}

TypeId File::array_type(TypeRef element,
                        ArraySizeKind size_kind,
                        std::optional<size_t> size,
                        InstId size_expr,
                        bool size_expr_is_dependent,
                        uint32_t extent_param,
                        TemplateValueExpression dependent_size_expr) {
    canonicalize_template_value_expression(dependent_size_expr);
    TypeSpec spec;
    spec.kind = TypeKind::Array;
    spec.payload = ArrayTypePayload{element,
                                    size_kind,
                                    size,
                                    size_expr,
                                    size_expr_is_dependent,
                                    extent_param,
                                    std::move(dependent_size_expr)};
    return intern_type(std::move(spec));
}

TypeId File::pack_index_type(TypeRef pack_type,
                             TemplateValueExpression index_expression,
                             std::vector<TypeRef> expansions,
                             bool fully_substituted) {
    canonicalize_template_value_expression(index_expression);
    TypeSpec spec;
    spec.kind = TypeKind::PackIndex;
    spec.payload = PackIndexTypePayload{pack_type,
                                        std::move(index_expression),
                                        std::move(expansions),
                                        fully_substituted};
    spec.dependency.add(DependencyFlag::TypeDependent);
    spec.dependency.add(DependencyFlag::ValueDependent);
    spec.dependency.add(DependencyFlag::InstantiationDependent);
    spec.dependency.add(DependencyFlag::RequiresInstantiation);
    return intern_type(std::move(spec));
}

TypeId File::place_type(TypeId object_type) {
    return place_type(type_ref(object_type));
}

TypeId File::place_type(TypeRef object_type) {
    TypeSpec spec;
    spec.kind = TypeKind::Place;
    spec.payload = PlaceTypePayload{object_type};
    return intern_type(std::move(spec));
}

TypeId File::record_type(EntityId entity, const std::string& spelling) {
    NameId name = intern_name(spelling);

    TypeSpec spec;
    spec.kind = TypeKind::Record;
    spec.payload = RecordTypePayload{entity, name};
    spec.debug_name = name;
    return intern_type(std::move(spec));
}

TypeId File::enum_type(EntityId entity,
                       const std::string& spelling,
                       TypeRef underlying_type,
                       bool is_scoped,
                       bool is_incomplete,
                       bool has_fixed_underlying_type) {
    NameId name = intern_name(spelling);

    TypeSpec spec;
    spec.kind = TypeKind::Enum;
    spec.payload = EnumTypePayload{entity,
                                   name,
                                   is_scoped,
                                   is_incomplete,
                                   has_fixed_underlying_type,
                                   underlying_type};
    spec.debug_name = name;
    return intern_type(std::move(spec));
}

TypeId File::complex_type(TypeRef element_type) {
    TypeSpec spec;
    spec.kind = TypeKind::Complex;
    spec.payload = ComplexTypePayload{element_type};
    return intern_type(std::move(spec));
}

TypeId File::bit_int_type(uint32_t bits, bool is_unsigned) {
    TypeSpec spec;
    spec.kind = TypeKind::BitInt;
    spec.payload = BitIntTypePayload{bits, is_unsigned};
    return intern_type(std::move(spec));
}

TypeId File::vector_type(TypeRef element_type,
                         uint32_t element_count,
                         uint64_t size_bytes) {
    TypeSpec spec;
    spec.kind = TypeKind::Vector;
    spec.payload = VectorTypePayload{element_type, element_count, size_bytes};
    return intern_type(std::move(spec));
}

TypeId File::type_param_type(EntityId entity,
                             const std::string& spelling,
                             uint32_t index,
                             uint32_t depth,
                             bool is_parameter_pack) {
    NameId name = intern_name(spelling);

    TypeSpec spec;
    spec.kind = TypeKind::TypeParam;
    TypeParamTypePayload payload{entity, name};
    payload.depth = depth;
    payload.index = index;
    payload.is_parameter_pack = is_parameter_pack;
    spec.payload = payload;
    spec.debug_name = name;
    return intern_type(std::move(spec));
}

TypeId File::function_type(TypeId result, const std::vector<TypeId>& parameters) {
    std::vector<TypeRef> parameter_refs;
    parameter_refs.reserve(parameters.size());
    for (TypeId parameter : parameters) {
        parameter_refs.push_back(type_ref(parameter));
    }
    return function_type(type_ref(result), parameter_refs);
}

TypeId File::function_type(TypeRef result,
                           const std::vector<TypeRef>& parameters,
                           bool is_variadic,
                           bool has_prototype,
                           bool member_is_const,
                           FunctionExceptionSpec exception_spec,
                           const std::vector<uint8_t>& parameter_pack_flags,
                           FunctionRefQualifierKind member_ref_qualifier,
                           bool member_is_volatile) {
    if (exception_spec.kind == FunctionExceptionSpecKind::Dependent) {
        canonicalize_template_value_expression(exception_spec.predicate);
    } else {
        exception_spec.predicate = {};
    }
    FunctionTypePayload payload;
    payload.return_type = result;
    payload.parameters = parameters;
    payload.parameter_pack_flags = parameter_pack_flags;
    payload.is_variadic = is_variadic;
    payload.has_prototype = has_prototype;
    payload.member_ref_qualifier = member_ref_qualifier;
    payload.member_is_const = member_is_const;
    payload.member_is_volatile = member_is_volatile;
    payload.exception_spec = std::move(exception_spec);

    TypeSpec spec;
    spec.kind = TypeKind::Function;
    spec.payload = std::move(payload);
    return intern_type(std::move(spec));
}

const TypePayload& File::type_payload(TypeId id) const {
    if (!valid(id)) {
        static const TypePayload invalid = InvalidTypePayload{};
        return invalid;
    }
    return type_payload(type(id).payload_index);
}

const TypePayload& File::type_payload(uint32_t index) const {
    static const TypePayload invalid = InvalidTypePayload{};
    if (index == 0 || index >= type_payloads_.size()) {
        return invalid;
    }
    return type_payloads_[index];
}

OperatorValueDomain File::operator_value_domain(TypeRef ref) const {
    if (!ref.type.valid() || !valid(ref.type)) {
        return OperatorValueDomain::Unknown;
    }
    TypeId type_id = resolved_type(ref.type);
    if (!valid(type_id)) {
        return OperatorValueDomain::Unknown;
    }

    const Type& resolved = type(type_id);
    const TypePayload& payload = type_payload(type_id);
    switch (resolved.kind) {
        case TypeKind::Builtin: {
            const auto* builtin = std::get_if<BuiltinTypePayload>(&payload);
            if (!builtin) {
                return OperatorValueDomain::Unknown;
            }
            switch (builtin->kind) {
                case BuiltinTypeKind::MetaInfo:
                    return OperatorValueDomain::Unknown;
                case BuiltinTypeKind::Bool:
                    return OperatorValueDomain::Bool;
                case BuiltinTypeKind::UChar:
                case BuiltinTypeKind::Char8:
                case BuiltinTypeKind::UShort:
                case BuiltinTypeKind::UInt:
                case BuiltinTypeKind::ULong:
                case BuiltinTypeKind::ULongLong:
                case BuiltinTypeKind::UInt128:
                case BuiltinTypeKind::USize:
                case BuiltinTypeKind::Char16:
                case BuiltinTypeKind::Char32:
                    return OperatorValueDomain::UnsignedInteger;
                case BuiltinTypeKind::Char:
                    return target_info().char_is_unsigned
                               ? OperatorValueDomain::UnsignedInteger
                               : OperatorValueDomain::SignedInteger;
                case BuiltinTypeKind::WChar:
                    return target_info().wchar_is_unsigned
                               ? OperatorValueDomain::UnsignedInteger
                               : OperatorValueDomain::SignedInteger;
                case BuiltinTypeKind::SChar:
                case BuiltinTypeKind::Short:
                case BuiltinTypeKind::Int:
                case BuiltinTypeKind::Long:
                case BuiltinTypeKind::LongLong:
                case BuiltinTypeKind::Int128:
                    return OperatorValueDomain::SignedInteger;
                case BuiltinTypeKind::Float16:
                case BuiltinTypeKind::Float:
                case BuiltinTypeKind::Double:
                case BuiltinTypeKind::LongDouble:
                    return OperatorValueDomain::Floating;
                case BuiltinTypeKind::Void:
                case BuiltinTypeKind::NullPtr:
                case BuiltinTypeKind::Other:
                    return OperatorValueDomain::Unknown;
            }
        }
        case TypeKind::Pointer:
        case TypeKind::BlockPointer:
            return OperatorValueDomain::Pointer;
        case TypeKind::Enum: {
            const auto* enum_payload = std::get_if<EnumTypePayload>(&payload);
            if (enum_payload && enum_payload->underlying_type.valid()) {
                return operator_value_domain(enum_payload->underlying_type);
            }
            return OperatorValueDomain::SignedInteger;
        }
        case TypeKind::Vector: {
            const auto* vector_payload = std::get_if<VectorTypePayload>(&payload);
            if (vector_payload && vector_payload->element_type.valid()) {
                return operator_value_domain(vector_payload->element_type);
            }
            return OperatorValueDomain::Unknown;
        }
        case TypeKind::Complex:
            return OperatorValueDomain::Complex;
        case TypeKind::BitInt: {
            const auto* bit_int_payload = std::get_if<BitIntTypePayload>(&payload);
            if (bit_int_payload && bit_int_payload->is_unsigned) {
                return OperatorValueDomain::UnsignedInteger;
            }
            return OperatorValueDomain::SignedInteger;
        }
        case TypeKind::Typedef: {
            const auto* typedef_payload = std::get_if<TypedefTypePayload>(&payload);
            if (typedef_payload && typedef_payload->underlying_type.valid()) {
                return operator_value_domain(typedef_payload->underlying_type);
            }
            return OperatorValueDomain::Unknown;
        }
        default:
            return OperatorValueDomain::Unknown;
    }
}

TypeRef File::array_element_ref(TypeId id) const {
    const auto* payload = std::get_if<ArrayTypePayload>(&type_payload(id));
    return payload ? payload->element_type : TypeRef{};
}

TypeId File::array_element_type(TypeId id) const {
    return array_element_ref(id).type;
}

TypeRef File::vector_element_ref(TypeId id) const {
    id = resolved_type(id);
    const auto* payload = std::get_if<VectorTypePayload>(&type_payload(id));
    return payload ? payload->element_type : TypeRef{};
}

TypeId File::vector_element_type(TypeId id) const {
    return vector_element_ref(id).type;
}

uint32_t File::vector_element_count(TypeId id) const {
    id = resolved_type(id);
    const auto* payload = std::get_if<VectorTypePayload>(&type_payload(id));
    return payload ? payload->element_count : 0;
}

uint64_t File::vector_size_bytes(TypeId id) const {
    id = resolved_type(id);
    const auto* payload = std::get_if<VectorTypePayload>(&type_payload(id));
    return payload ? payload->size_bytes : 0;
}

TypeRef File::place_object_ref(TypeId id) const {
    const auto* payload = std::get_if<PlaceTypePayload>(&type_payload(id));
    return payload ? payload->object_type : TypeRef{};
}

TypeId File::place_object_type(TypeId id) const {
    return place_object_ref(id).type;
}

void File::retype_entity_places(EntityId entity_id) {

    if (!valid(entity_id)) {
        return;
    }
    const Entity& named_entity = entity(entity_id);
    TypeRef object_ref = type_ref(named_entity.type,
                                  named_entity.qualifiers,
                                  named_entity.memory_space);
    if (!valid(object_ref.type)) {
        return;
    }
    TypeId place = place_type(object_ref);
    for (Inst& instruction : insts_) {
        if ((instruction.kind != InstKind::LocalPlace &&
             instruction.kind != InstKind::GlobalPlace) ||
            instruction.result_type == place) {
            continue;
        }
        std::vector<Operand> ops = operands(instruction.operands);
        if (ops.empty()) {
            continue;
        }
        const auto* named = std::get_if<EntityId>(&ops[0].data);
        if (!named || *named != entity_id) {
            continue;
        }
        instruction.result_type = place;
        if (instruction.place_fact.valid()) {
            place_fact_mut(instruction.place_fact).object_type = object_ref;
        }
    }
}

TypeRef File::pointer_pointee_ref(TypeId id) const {
    const auto* payload = std::get_if<PointerTypePayload>(&type_payload(id));
    return payload ? payload->pointee : TypeRef{};
}

TypeId File::pointer_pointee_type(TypeId id) const {
    return pointer_pointee_ref(id).type;
}

TypeRef File::reference_referred_ref(TypeId id) const {
    const auto* payload = std::get_if<ReferenceTypePayload>(&type_payload(id));
    return payload ? payload->referred_type : TypeRef{};
}

TypeId File::reference_referred_type(TypeId id) const {
    return reference_referred_ref(id).type;
}

TypeRef File::member_pointer_class_ref(TypeId id) const {
    id = resolved_type(id);
    if (!valid(id) || type(id).kind != TypeKind::MemberPointer) {
        return {};
    }
    const auto* payload =
        std::get_if<MemberPointerTypePayload>(&type_payload(id));
    return payload ? payload->class_type : TypeRef{};
}

TypeRef File::member_pointer_member_ref(TypeId id) const {
    id = resolved_type(id);
    if (!valid(id) || type(id).kind != TypeKind::MemberPointer) {
        return {};
    }
    const auto* payload =
        std::get_if<MemberPointerTypePayload>(&type_payload(id));
    return payload ? payload->member_type : TypeRef{};
}

bool File::member_pointer_points_to_function(TypeId id) const {
    TypeId member_type = resolved_type(member_pointer_member_ref(id).type);
    return valid(member_type) && type(member_type).kind == TypeKind::Function;
}

TemplateValueKind File::template_value_kind_for_type(TypeId id) const {
    TypeId resolved = resolved_type(id);
    if (!valid(resolved)) {
        return TemplateValueKind::Integer;
    }
    const Type& node = type(resolved);
    if (node.kind == TypeKind::Builtin) {
        const auto* builtin =
            std::get_if<BuiltinTypePayload>(&type_payload(resolved));
        if (builtin && builtin->kind == BuiltinTypeKind::Bool) {
            return TemplateValueKind::Boolean;
        }
        if (builtin && builtin->kind == BuiltinTypeKind::NullPtr) {
            return TemplateValueKind::Null;
        }
        if (builtin && builtin->kind == BuiltinTypeKind::MetaInfo) {
            return TemplateValueKind::MetaInfo;
        }
        if (builtin &&
            (builtin->kind == BuiltinTypeKind::Float ||
             builtin->kind == BuiltinTypeKind::Double ||
             builtin->kind == BuiltinTypeKind::LongDouble)) {
            return TemplateValueKind::Floating;
        }
    }
    if (node.kind == TypeKind::Pointer ||
        node.kind == TypeKind::BlockPointer ||
        node.kind == TypeKind::LValueReference ||
        node.kind == TypeKind::RValueReference) {
        return TemplateValueKind::Address;
    }
    if (node.kind == TypeKind::MemberPointer) {
        return TemplateValueKind::MemberPointer;
    }
    if (node.kind == TypeKind::Record) {
        const RecordFacts* facts = record_facts_for_type(resolved);
        if (facts && facts->is_lambda_closure) {
            return TemplateValueKind::Closure;
        }
        return TemplateValueKind::StructuralObject;
    }
    if (node.kind == TypeKind::Array) {
        return TemplateValueKind::StructuralObject;
    }
    return TemplateValueKind::Integer;
}

TemplateNullKind File::template_null_kind_for_type(TypeId id) const {
    TypeId resolved = resolved_type(id);
    if (!valid(resolved)) {
        return TemplateNullKind::None;
    }
    const Type& node = type(resolved);
    if (node.kind == TypeKind::Builtin) {
        const auto* builtin =
            std::get_if<BuiltinTypePayload>(&type_payload(resolved));
        if (builtin && builtin->kind == BuiltinTypeKind::NullPtr) {
            return TemplateNullKind::Nullptr;
        }
    }
    if (node.kind == TypeKind::Pointer ||
        node.kind == TypeKind::BlockPointer) {
        return TemplateNullKind::Pointer;
    }
    if (node.kind == TypeKind::MemberPointer) {
        return TemplateNullKind::MemberPointer;
    }
    return TemplateNullKind::None;
}

bool File::template_type_accepts_null_kind(TypeId id,
                                           TemplateNullKind kind) const {
    return kind != TemplateNullKind::None &&
           template_null_kind_for_type(id) == kind;
}

bool File::template_argument_references_internal_entity(
    const TemplateArgument& argument) const {
    std::vector<const TemplateArgument*> pending{&argument};
    while (!pending.empty()) {
        const TemplateArgument& current = *pending.back();
        pending.pop_back();
        if (current.closure_identity.valid() &&
            valid(current.closure_identity)) {
            const ClosureIdentityFact& closure =
                closure_identity(current.closure_identity);
            if (closure.record.valid() && valid(closure.record) &&
                entity(closure.record).linkage == LinkageKind::Internal) {
                return true;
            }
        }
        if (current.value_entity.valid() && valid(current.value_entity) &&
            entity(current.value_entity).linkage == LinkageKind::Internal) {
            return true;
        }
        for (const TemplateArgument& element : current.value_elements) {
            pending.push_back(&element);
        }
    }
    return false;
}

bool File::template_context_references_internal_entity(
    EntityId entity_id) const {
    while (entity_id.valid() && valid(entity_id)) {
        if (const TemplateSpecializationFact* specialization =
                template_specialization(entity_id)) {
            for (const TemplateArgument& argument :
                 specialization->template_arguments()) {
                if (template_argument_references_internal_entity(argument)) {
                    return true;
                }
            }
        }
        entity_id = entity(entity_id).parent;
    }
    return false;
}

LinkageKind File::odr_linkage_for_entity(EntityId entity_id) const {
    return template_context_references_internal_entity(entity_id)
        ? LinkageKind::Internal
        : LinkageKind::LinkOnceODR;
}

EntityId File::record_entity(TypeId id) const {
    TypeId resolved = resolved_type(id);
    if (!valid(resolved) || type(resolved).kind != TypeKind::Record) {
        return {};
    }
    const auto* payload = std::get_if<RecordTypePayload>(&type_payload(resolved));
    return payload ? payload->entity : EntityId{};
}

RecordFacts* File::record_facts(EntityId entity) {
    auto found = record_facts_.find(id_key(entity));
    return found == record_facts_.end() ? nullptr : &found->second;
}

const RecordFacts* File::record_facts(EntityId entity) const {
    auto found = record_facts_.find(id_key(entity));
    return found == record_facts_.end() ? nullptr : &found->second;
}

const RecordFacts* File::record_facts_for_type(TypeId type_id) const {
    EntityId entity = record_entity(type_id);
    return entity.valid() ? record_facts(entity) : nullptr;
}

ObjCInterfaceFacts* File::objc_interface_facts_mut(EntityId entity) {
    auto found = objc_interface_facts_.find(id_key(entity));
    if (found == objc_interface_facts_.end()) {
        return nullptr;
    }
    record_objc_interface_facts_mutation(id_key(entity));
    return &found->second;
}

const ObjCInterfaceFacts* File::objc_interface_facts(EntityId entity) const {
    auto found = objc_interface_facts_.find(id_key(entity));
    return found == objc_interface_facts_.end() ? nullptr : &found->second;
}

void File::set_objc_interface_facts(EntityId entity, ObjCInterfaceFacts facts) {
    if (!valid(entity)) {
        return;
    }
    EntityKind kind = this->entity(entity).kind;
    if (kind != EntityKind::ObjCInterface &&
        kind != EntityKind::ObjCProtocol &&
        kind != EntityKind::ObjCCategory) {
        return;
    }
    facts.entity = entity;
    uint64_t key = id_key(entity);
    record_objc_interface_facts_mutation(key);
    objc_interface_facts_[key] = std::move(facts);
}

SelectorId File::intern_selector(std::string_view spelling) {
    NameId name = intern_name(spelling);
    return SelectorId{name.index, name.generation};
}

NameId File::selector_name(SelectorId selector) const {
    return NameId{selector.index, selector.generation};
}

std::string_view File::selector_spelling(SelectorId selector) const {
    return name(selector_name(selector));
}

ClassPropertyState File::consteval_only_type_state(TypeId type_id) const {
    std::vector<TypeId> active;
    std::function<ClassPropertyState(TypeId)> classify =
        [&](TypeId input) -> ClassPropertyState {
        TypeId type_id = resolved_type(input);
        if (!valid(type_id)) {
            return ClassPropertyState::Unavailable;
        }
        if (std::find(active.begin(), active.end(), type_id) != active.end()) {

            return ClassPropertyState::False;
        }
        active.push_back(type_id);
        auto finish = [&](ClassPropertyState state) {
            active.pop_back();
            return state;
        };
        switch (type(type_id).kind) {
            case TypeKind::Builtin: {
                const auto* builtin = std::get_if<BuiltinTypePayload>(
                    &type_payload(type_id));
                return finish(builtin &&
                                      builtin->kind == BuiltinTypeKind::MetaInfo
                                  ? ClassPropertyState::True
                                  : ClassPropertyState::False);
            }
            case TypeKind::Pointer: {
                const auto* pointer = std::get_if<PointerTypePayload>(
                    &type_payload(type_id));
                return finish(pointer
                    ? classify(pointer->pointee.type)
                    : ClassPropertyState::Unavailable);
            }
            case TypeKind::BlockPointer: {
                const auto* pointer = std::get_if<BlockPointerTypePayload>(
                    &type_payload(type_id));
                return finish(pointer
                    ? classify(pointer->pointee.type)
                    : ClassPropertyState::Unavailable);
            }
            case TypeKind::LValueReference:
            case TypeKind::RValueReference: {
                const auto* reference = std::get_if<ReferenceTypePayload>(
                    &type_payload(type_id));
                return finish(reference
                    ? classify(reference->referred_type.type)
                    : ClassPropertyState::Unavailable);
            }
            case TypeKind::Array: {
                const auto* array = std::get_if<ArrayTypePayload>(
                    &type_payload(type_id));
                return finish(array
                    ? classify(array->element_type.type)
                    : ClassPropertyState::Unavailable);
            }
            case TypeKind::Function: {
                const auto* function = std::get_if<FunctionTypePayload>(
                    &type_payload(type_id));
                if (!function) {
                    return finish(ClassPropertyState::Unavailable);
                }
                bool dependent = false;
                auto include = [&](TypeRef component) {
                    ClassPropertyState state = classify(component.type);
                    dependent = dependent ||
                        state == ClassPropertyState::Dependent ||
                        state == ClassPropertyState::Unavailable;
                    return state == ClassPropertyState::True;
                };
                if (include(function->return_type)) {
                    return finish(ClassPropertyState::True);
                }
                for (TypeRef parameter : function->parameters) {
                    if (include(parameter)) {
                        return finish(ClassPropertyState::True);
                    }
                }
                return finish(dependent ? ClassPropertyState::Dependent
                                        : ClassPropertyState::False);
            }
            case TypeKind::MemberPointer: {
                const auto* member = std::get_if<MemberPointerTypePayload>(
                    &type_payload(type_id));
                if (!member) {
                    return finish(ClassPropertyState::Unavailable);
                }
                ClassPropertyState class_state =
                    classify(member->class_type.type);
                ClassPropertyState member_state =
                    classify(member->member_type.type);
                if (class_state == ClassPropertyState::True ||
                    member_state == ClassPropertyState::True) {
                    return finish(ClassPropertyState::True);
                }
                if (class_state == ClassPropertyState::Dependent ||
                    member_state == ClassPropertyState::Dependent ||
                    class_state == ClassPropertyState::Unavailable ||
                    member_state == ClassPropertyState::Unavailable) {
                    return finish(ClassPropertyState::Dependent);
                }
                return finish(ClassPropertyState::False);
            }
            case TypeKind::Record: {
                const RecordFacts* facts = record_facts_for_type(type_id);
                return finish(facts ? facts->is_consteval_only
                                    : ClassPropertyState::Unavailable);
            }
            case TypeKind::TypeParam:
            case TypeKind::TemplateSpecialization:
            case TypeKind::AliasSpecialization:
            case TypeKind::DependentName:
            case TypeKind::Dependent:
            case TypeKind::Placeholder:
            case TypeKind::Auto:
            case TypeKind::TypeofExpr:
            case TypeKind::DecltypeExpr:
            case TypeKind::BuiltinTransform:
            case TypeKind::BuiltinPackElement:
            case TypeKind::PackIndex:
                return finish(ClassPropertyState::Dependent);
            case TypeKind::Place: {
                const auto* place = std::get_if<PlaceTypePayload>(
                    &type_payload(type_id));
                return finish(place
                    ? classify(place->object_type.type)
                    : ClassPropertyState::Unavailable);
            }
            default:
                return finish(ClassPropertyState::False);
        }
    };
    return classify(type_id);
}

const RecordFieldFact* File::field_fact(EntityId field) const {
    if (!valid(field) || entity(field).kind != EntityKind::Field) {
        return nullptr;
    }
    EntityId parent = entity(field).parent;
    const RecordFacts* facts = record_facts(parent);
    if (!facts) {
        return nullptr;
    }
    for (const RecordFieldFact& fact : facts->fields) {
        if (fact.entity == field) {
            return &fact;
        }
    }
    return nullptr;
}

const RecordMethodFact* File::method_fact(EntityId method) const {
    if (!valid(method)) {
        return nullptr;
    }
    EntityKind kind = entity(method).kind;
    if (kind != EntityKind::Method && kind != EntityKind::Constructor &&
        kind != EntityKind::Destructor) {
        return nullptr;
    }
    const RecordFacts* facts = record_facts(entity(method).parent);
    if (!facts) {
        return nullptr;
    }
    for (const RecordMethodFact& fact : facts->methods) {
        if (fact.entity == method) {
            return &fact;
        }
    }
    return nullptr;
}

RecordMethodFact* File::method_fact_mut(EntityId method) {
    if (!valid(method)) {
        return nullptr;
    }
    EntityKind kind = entity(method).kind;
    if (kind != EntityKind::Method && kind != EntityKind::Constructor &&
        kind != EntityKind::Destructor) {
        return nullptr;
    }
    EntityId owner = entity(method).parent;
    uint64_t key = id_key(owner);
    auto found = record_facts_.find(key);
    if (found == record_facts_.end()) {
        return nullptr;
    }
    record_record_facts_mutation(key);
    for (RecordMethodFact& fact : found->second.methods) {
        if (fact.entity == method) {
            return &fact;
        }
    }
    return nullptr;
}

const DefaultedComparisonFact* File::defaulted_comparison_fact(
    EntityId function) const {
    if (!valid(function)) {
        return nullptr;
    }
    auto found = defaulted_comparison_facts_.find(id_key(function));
    return found == defaulted_comparison_facts_.end() ? nullptr
                                                       : &found->second;
}

DefaultedComparisonFact* File::defaulted_comparison_fact_mut(
    EntityId function) {
    if (!valid(function)) {
        return nullptr;
    }
    uint64_t key = id_key(function);
    auto found = defaulted_comparison_facts_.find(key);
    if (found == defaulted_comparison_facts_.end()) {
        return nullptr;
    }
    record_defaulted_comparison_fact_mutation(key);
    return &found->second;
}

void File::set_defaulted_comparison_fact(
    EntityId function,
    DefaultedComparisonFact fact) {
    if (!valid(function)) {
        return;
    }
    fact.function = function;
    uint64_t key = id_key(function);
    record_defaulted_comparison_fact_mutation(key);
    defaulted_comparison_facts_[key] = std::move(fact);
}

const StructuredBindingFact* File::structured_binding_fact(
    EntityId backing_or_binding) const {
    if (!valid(backing_or_binding)) {
        return nullptr;
    }
    EntityId backing = backing_or_binding;
    const Entity& source = entity(backing_or_binding);
    if (source.kind == EntityKind::StructuredBinding) {
        backing = source.structured_binding_backing;
    }
    if (!valid(backing)) {
        return nullptr;
    }
    auto found = structured_binding_facts_.find(id_key(backing));
    return found == structured_binding_facts_.end() ? nullptr
                                                     : &found->second;
}

StructuredBindingFact* File::structured_binding_fact_mut(
    EntityId backing_or_binding) {
    if (!valid(backing_or_binding)) {
        return nullptr;
    }
    EntityId backing = backing_or_binding;
    const Entity& source = entity(backing_or_binding);
    if (source.kind == EntityKind::StructuredBinding) {
        backing = source.structured_binding_backing;
    }
    if (!valid(backing)) {
        return nullptr;
    }
    uint64_t key = id_key(backing);
    auto found = structured_binding_facts_.find(key);
    if (found == structured_binding_facts_.end()) {
        return nullptr;
    }
    record_structured_binding_fact_mutation(key);
    return &found->second;
}

void File::set_structured_binding_fact(EntityId backing,
                                       StructuredBindingFact fact) {
    if (!valid(backing) || entity(backing).kind != EntityKind::Variable) {
        return;
    }
    fact.backing = backing;
    uint64_t key = id_key(backing);
    record_structured_binding_fact_mutation(key);
    structured_binding_facts_[key] = std::move(fact);
}

void File::set_record_facts(EntityId entity, RecordFacts facts) {
    if (!valid(entity) || this->entity(entity).kind != EntityKind::Record) {
        return;
    }
    facts.entity = entity;
    uint64_t key = id_key(entity);
    record_record_facts_mutation(key);
    record_facts_[key] = std::move(facts);
}

void File::set_template_specialization(EntityId entity,
                                       TemplateSpecializationFact fact) {
    if (!valid(entity)) {
        return;
    }
    EntityKind kind = this->entity(entity).kind;
    if (kind != EntityKind::Record &&
        kind != EntityKind::Function &&
        kind != EntityKind::Method &&
        kind != EntityKind::Constructor &&
        kind != EntityKind::Destructor &&
        kind != EntityKind::Variable) {
        return;
    }
    uint64_t key = id_key(entity);
    record_template_specialization_mutation(key);
    template_specializations_[key] = std::move(fact);
}

const TemplateSpecializationFact* File::template_specialization(
    EntityId entity) const {
    if (!valid(entity)) {
        return nullptr;
    }
    auto found = template_specializations_.find(id_key(entity));
    return found == template_specializations_.end() ? nullptr : &found->second;
}

uint32_t File::add_type_payload(TypePayload payload) {
    type_payloads_.push_back(std::move(payload));
    return static_cast<uint32_t>(type_payloads_.size() - 1);
}

TypeId File::intern_type(TypeSpec spec) {
    if (!type_spec_matches_payload(spec)) {
        return {};
    }

    auto same_link = [](TypeId lhs, TypeId rhs) {
        if (!lhs.valid() || !rhs.valid()) {
            return lhs.valid() == rhs.valid();
        }
        return lhs == rhs;
    };
    uint64_t hash = type_spec_hash(spec);
    TypeId existing{};
    auto range = type_index_.equal_range(hash);
    for (auto it = range.first; it != range.second; ++it) {

        if (!valid(it->second) ||
            types_[it->second.index].payload_index == 0 ||
            types_[it->second.index].payload_index >=
                type_payloads_.size()) {
            continue;
        }
        const Type& candidate = types_[it->second.index];
        if (candidate.kind != spec.kind ||
            !type_payloads_structurally_equal(
                spec.payload, type_payloads_[candidate.payload_index])) {
            continue;
        }

        TypeId stored_canonical = candidate.canonical == it->second
            ? TypeId{}
            : candidate.canonical;
        if (same_link(spec.canonical, stored_canonical) &&
            same_link(spec.desugared, candidate.desugared) &&
            same_link(spec.resolved, candidate.resolved)) {
            existing = it->second;
            break;
        }
    }
#ifdef ABURI_VERIFY_TYPE_INTERN
    std::string verify_key = type_structural_key(spec);
    {
        auto legacy = verify_type_index_.find(verify_key);
        bool legacy_hit = legacy != verify_type_index_.end();
        assert(legacy_hit == existing.valid() &&
               "hash-consed type interning disagrees with the string key on "
               "hit/miss");
        assert((!legacy_hit || legacy->second == existing) &&
               "hash-consed type interning found a different TypeId than the "
               "string key");
    }
#endif
    if (existing.valid()) {
        bump_cir_counter(PerfCounter::TypeInternHits);
        return existing;
    }
    bump_cir_counter(PerfCounter::TypesInterned);

    Type type;
    type.kind = spec.kind;
    type.payload_index = add_type_payload(std::move(spec.payload));
    type.canonical = spec.canonical;
    type.desugared = spec.desugared;
    type.resolved = spec.resolved;
    type.dependency = spec.dependency;
    type.debug_name = spec.debug_name;
    type.loc = spec.loc;

    TypeId id = add_record<Type, TypeId>(types_, type_generations_, std::move(type));
    if (!types_[id.index].canonical.valid()) {
        types_[id.index].canonical = id;
    }
    type_index_.emplace(hash, id);
    if (!transactions_.empty()) {
        transactions_.back().inserted_type_entries.push_back({hash, id});
    }
#ifdef ABURI_VERIFY_TYPE_INTERN
    verify_type_index_.emplace(verify_key, id);
    if (!transactions_.empty()) {
        transactions_.back().inserted_type_keys.push_back(
            std::move(verify_key));
    }
#endif
    return id;
}

EntityId File::add_entity(Entity entity) {
    if (active_module_.unit.valid()) {
        entity.origin_unit = active_module_.unit;
        entity.origin_fragment = active_module_.fragment;

        bool exempt_kind = entity.kind == EntityKind::Namespace ||
                           entity.kind == EntityKind::NamespaceAlias ||
                           entity.kind == EntityKind::TypeAlias;
        if (!exempt_kind &&
            (active_module_.fragment == ModuleFragment::Purview ||
             active_module_.fragment == ModuleFragment::Private)) {
            entity.module_attachment = active_module_.unit;
        }
    }
    return add_record<Entity, EntityId>(entities_, entity_generations_, std::move(entity));
}

const Entity& File::entity(EntityId id) const {
    static const Entity invalid;
    if (!valid(id)) {
        return invalid;
    }
    return entities_[id.index];
}

Entity& File::entity_mut(EntityId id) {
    static Entity invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_entity_mutation(id);
    return entities_[id.index];
}

std::vector<EntityId> File::entity_ids() const {
    std::vector<EntityId> ids;
    ids.reserve(entities_.size() > 0 ? entities_.size() - 1 : 0);
    for (uint32_t i = 1; i < entities_.size(); ++i) {
        ids.push_back(EntityId{i, entity_generations_[i]});
    }
    return ids;
}

DeclContextId File::add_decl_context(DeclContext context) {
    DeclContextId parent = context.parent;
    DeclContextId id =
        add_record<DeclContext, DeclContextId>(decl_contexts_,
                                               decl_context_generations_,
                                               std::move(context));
    if (valid(parent)) {
        journal_decl_context_append(parent,
                                    DeclContextDelta::Kind::ChildAppended);
        decl_contexts_[parent.index].children.push_back(id);
    }
    return id;
}

DeclContextId File::create_decl_context(DeclContextKind kind,
                                        DeclContextId parent,
                                        EntityId owner,
                                        SrcLoc loc) {
    DeclContext context;
    context.kind = kind;
    context.parent = parent;
    context.owner = owner;
    context.loc = loc;
    return add_decl_context(std::move(context));
}

const DeclContext& File::decl_context(DeclContextId id) const {
    static const DeclContext invalid;
    if (!valid(id)) {
        return invalid;
    }
    return decl_contexts_[id.index];
}

DeclContext& File::decl_context_mut(DeclContextId id) {
    static DeclContext invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_decl_context_mutation(id);
    return decl_contexts_[id.index];
}

std::vector<DeclContextId> File::decl_context_ids() const {
    std::vector<DeclContextId> ids;
    ids.reserve(decl_contexts_.size() > 0 ? decl_contexts_.size() - 1 : 0);
    for (uint32_t i = 1; i < decl_contexts_.size(); ++i) {
        ids.push_back(DeclContextId{i, decl_context_generations_[i]});
    }
    return ids;
}

BindingId File::add_binding(Binding binding) {
    if (binding.context.valid() && !valid(binding.context)) {
        return {};
    }
    BindingId id = add_record<Binding, BindingId>(bindings_,
                                                  binding_generations_,
                                                  std::move(binding));
    DeclContextId context = bindings_[id.index].context;
    if (valid(context)) {
        journal_decl_context_append(context,
                                    DeclContextDelta::Kind::BindingAppended);
        decl_contexts_[context.index].bindings.push_back(id);
        index_binding_in_decl_context(context, id);
    }
    return id;
}

void File::stamp_module_export(DeclContextId context, EntityId entity_id) {
    if (active_module_.export_depth == 0 || !valid(entity_id)) {
        return;
    }
    DeclContextKind kind = decl_context(context).kind;
    if (kind != DeclContextKind::Namespace &&
        kind != DeclContextKind::TranslationUnit) {
        return;
    }
    entity_mut(entity_id).is_module_exported = true;
}

BindingId File::bind_callable_overload(DeclContextId context,
                                       NameId name_id,
                                       EntityId entity_id,
                                       TypeRef type_ref_value,
                                       bool is_definition,
                                       SrcLoc loc) {
    if (!valid(context) || !valid(name_id) || !valid(entity_id)) {
        return {};
    }
    stamp_module_export(context, entity_id);
    const DeclContext& record = decl_context(context);
    bool block_scope_declaration =
        record.kind == DeclContextKind::Block;
    auto callable = record.ordinary_callable_bindings.find(id_key(name_id));
    if (callable != record.ordinary_callable_bindings.end() &&
        valid(callable->second)) {

        record_binding_mutation(callable->second);
        Binding& binding_record = bindings_[callable->second.index];
        binding_record.has_block_scope_function_declaration =
            binding_record.has_block_scope_function_declaration ||
            block_scope_declaration;
        auto existing = std::find(binding_record.entities.begin(),
                                  binding_record.entities.end(),
                                  entity_id);
        if (existing != binding_record.entities.end()) {
            binding_record.type = type_ref_value;
            binding_record.is_definition =
                binding_record.is_definition || is_definition;
            binding_record.loc = loc;
            assign_decl_context_index(context,
                                      DeclContextIndexKind::OrdinaryLatest,
                                      id_key(name_id),
                                      callable->second);
            return callable->second;
        }
        binding_record.entities.push_back(entity_id);
        binding_record.entity_generations.push_back(0);
        binding_record.type = type_ref_value;
        binding_record.is_definition = binding_record.is_definition || is_definition;
        binding_record.loc = loc;
        assign_decl_context_index(context,
                                  DeclContextIndexKind::OrdinaryLatest,
                                  id_key(name_id),
                                  callable->second);
        return callable->second;
    }
    BindingId binding = bind_entity(context,
                                    name_id,
                                    LookupNamespace::Ordinary,
                                    entity_id,
                                    type_ref_value,
                                    false,
                                    false,
                                    is_definition,
                                    {},
                                    loc);
    if (block_scope_declaration && valid(binding)) {
        binding_mut(binding)->has_block_scope_function_declaration = true;
    }
    return binding;
}

BindingId File::bind_entity(DeclContextId context,
                            NameId name_id,
                            LookupNamespace lookup_namespace,
                            EntityId entity_id,
                            TypeRef type_ref_value,
                            bool is_type_name,
                            bool is_template_name,
                            bool is_definition,
                            InstId place,
                            SrcLoc loc) {
    if (!valid(context) || !valid(name_id) || !valid(entity_id)) {
        return {};
    }
    stamp_module_export(context, entity_id);
    Binding binding_record;
    binding_record.name = name_id;
    binding_record.context = context;
    binding_record.lookup_namespace = lookup_namespace;
    binding_record.entities.push_back(entity_id);
    binding_record.entity_generations.push_back(0);
    binding_record.type = type_ref_value;
    binding_record.place = place;
    binding_record.is_type_name = is_type_name;
    binding_record.is_template_name = is_template_name;
    binding_record.is_definition = is_definition;
    binding_record.loc = loc;
    return add_binding(std::move(binding_record));
}

const Binding& File::binding(BindingId id) const {
    static const Binding invalid;
    if (!valid(id)) {
        return invalid;
    }
    return bindings_[id.index];
}

bool File::binding_is_callable(const Binding& binding) const {
    return ordinary_binding_matches_category(binding,
                                             OrdinaryBindingCategory::Callable);
}

Binding* File::binding_mut(BindingId id) {
    if (!valid(id)) {
        return nullptr;
    }
    record_binding_mutation(id);
    return &bindings_[id.index];
}

BindingId File::add_alias_binding(DeclContextId context,
                                  const Binding& source,
                                  SrcLoc loc,
                                  uint64_t introduction_generation) {
    if (!valid(context)) {
        return {};
    }

    if (binding_is_callable(source)) {
        const DeclContext& record = decl_context(context);
        auto callable =
            record.ordinary_callable_bindings.find(id_key(source.name));
        if (callable != record.ordinary_callable_bindings.end() &&
            valid(callable->second)) {
            record_binding_mutation(callable->second);
            Binding& binding_record = bindings_[callable->second.index];
            for (size_t i = 0; i < source.entities.size(); ++i) {
                EntityId entity_id = source.entities[i];
                if (std::find(binding_record.entities.begin(),
                              binding_record.entities.end(),
                              entity_id) != binding_record.entities.end()) {
                    continue;
                }
                binding_record.entities.push_back(entity_id);
                binding_record.entity_generations.push_back(
                    introduction_generation);
            }
            binding_record.generation = introduction_generation;
            binding_record.loc = loc;
            assign_decl_context_index(context,
                                      DeclContextIndexKind::OrdinaryLatest,
                                      id_key(source.name),
                                      callable->second);
            return callable->second;
        }
    }
    Binding alias = source;
    alias.context = context;
    alias.loc = loc;
    alias.generation = introduction_generation;
    alias.entity_generations.assign(alias.entities.size(),
                                    introduction_generation);
    return add_binding(std::move(alias));
}

void File::add_using_directive(DeclContextId context, DeclContextId target) {
    if (!valid(context) || !valid(target) || context == target) {
        return;
    }
    DeclContext& record = decl_contexts_[context.index];
    for (DeclContextId existing : record.using_directives) {
        if (existing == target) {
            return;
        }
    }
    journal_decl_context_append(
        context, DeclContextDelta::Kind::UsingDirectiveAppended);
    record.using_directives.push_back(target);
    record.using_directive_origins.resize(record.using_directives.size());
    record.using_directive_origins.back() = active_module_.unit;
}

bool File::ordinary_binding_matches_category(
    const Binding& binding_record,
    OrdinaryBindingCategory category) const {
    if (binding_record.lookup_namespace != LookupNamespace::Ordinary) {
        return false;
    }

    switch (category) {
        case OrdinaryBindingCategory::TypeName:
            return binding_record.is_type_name;
        case OrdinaryBindingCategory::TemplateName:
            return binding_record.is_template_name;
        case OrdinaryBindingCategory::NamespaceName:
            return !binding_record.entities.empty() &&
                   (entity(binding_record.entities.back()).kind ==
                        EntityKind::Namespace ||
                    entity(binding_record.entities.back()).kind ==
                        EntityKind::NamespaceAlias);
        case OrdinaryBindingCategory::Callable:
            if (binding_record.entities.empty()) {
                return false;
            }
            switch (entity(binding_record.entities.back()).kind) {
                case EntityKind::Function:
                case EntityKind::Method:
                case EntityKind::Constructor:
                case EntityKind::Destructor:
                    return true;
                case EntityKind::Invalid:
                case EntityKind::TranslationUnit:
                case EntityKind::Parameter:
                case EntityKind::Variable:
                case EntityKind::StructuredBinding:
                case EntityKind::Concept:
                case EntityKind::TypeAlias:
                case EntityKind::Record:
                case EntityKind::Enum:
                case EntityKind::Enumerator:
                case EntityKind::Field:
                case EntityKind::TemplateParam:
                case EntityKind::Namespace:
                case EntityKind::NamespaceAlias:
                    return false;
            }
            return false;
        case OrdinaryBindingCategory::Value:
            if (binding_record.entities.empty()) {
                return false;
            }
            switch (entity(binding_record.entities.back()).kind) {
                case EntityKind::Parameter:
                case EntityKind::Variable:
                case EntityKind::Enumerator:
                case EntityKind::Field:
                case EntityKind::StructuredBinding:
                    return true;
                case EntityKind::Invalid:
                case EntityKind::TranslationUnit:
                case EntityKind::Function:
                case EntityKind::Concept:
                case EntityKind::TypeAlias:
                case EntityKind::Record:
                case EntityKind::Enum:
                case EntityKind::Method:
                case EntityKind::Constructor:
                case EntityKind::Destructor:
                case EntityKind::TemplateParam:
                case EntityKind::Namespace:
                case EntityKind::NamespaceAlias:
                    return false;
            }
            return false;
    }
    return false;
}

bool File::ordinary_binding_names_qualifier(
    const Binding& binding_record) const {
    if (binding_record.lookup_namespace != LookupNamespace::Ordinary) {
        return false;
    }
    if (binding_record.is_type_name) {
        return true;
    }
    if (binding_record.entities.empty()) {
        return false;
    }
    EntityKind kind = entity(binding_record.entities.back()).kind;
    return kind == EntityKind::Namespace ||
        kind == EntityKind::NamespaceAlias;
}

NameId File::find_existing_name(std::string_view spelling) const {
    auto found = name_index_.find(spelling);
    return found == name_index_.end() ? NameId{} : found->second;
}

void File::index_binding_in_decl_context(DeclContextId context_id,
                                         BindingId binding_id) {
    if (!valid(context_id) || !valid(binding_id)) {
        return;
    }
    const Binding& binding_record = binding(binding_id);
    if (!valid(binding_record.name)) {
        return;
    }

    uint64_t key = id_key(binding_record.name);
    auto assign = [&](DeclContextIndexKind kind) {
        assign_decl_context_index(context_id, kind, key, binding_id);
    };
    switch (binding_record.lookup_namespace) {
        case LookupNamespace::Ordinary:
            assign(DeclContextIndexKind::OrdinaryLatest);
            if (ordinary_binding_matches_category(
                    binding_record, OrdinaryBindingCategory::Value)) {
                assign(DeclContextIndexKind::OrdinaryValue);
            }
            if (ordinary_binding_matches_category(
                    binding_record, OrdinaryBindingCategory::Callable)) {
                assign(DeclContextIndexKind::OrdinaryCallable);
            }
            if (ordinary_binding_matches_category(
                    binding_record, OrdinaryBindingCategory::TypeName)) {
                assign(DeclContextIndexKind::OrdinaryTypeName);
            }
            if (ordinary_binding_matches_category(
                    binding_record, OrdinaryBindingCategory::TemplateName)) {
                assign(DeclContextIndexKind::OrdinaryTemplateName);
            }
            if (ordinary_binding_matches_category(
                    binding_record, OrdinaryBindingCategory::NamespaceName)) {
                assign(DeclContextIndexKind::OrdinaryNamespace);
            }
            break;
        case LookupNamespace::Tag:
            assign(DeclContextIndexKind::Tag);
            break;
        case LookupNamespace::Label:
            assign(DeclContextIndexKind::Label);
            break;
        case LookupNamespace::None:
            break;
    }
}

Binding* File::mutable_ordinary_binding(DeclContextId context_id,
                                        std::string_view spelling) {
    NameId name_id = find_existing_name(spelling);
    if (!valid(context_id) || !valid(name_id)) {
        return nullptr;
    }
    const DeclContext& context = decl_context(context_id);
    auto found = context.ordinary_latest_bindings.find(id_key(name_id));
    if (found == context.ordinary_latest_bindings.end() || !valid(found->second)) {
        return nullptr;
    }
    record_binding_mutation(found->second);
    return &bindings_[found->second.index];
}

bool File::entity_lookup_visible(EntityId id) const {
    if (!has_module_units() || !valid(id)) {
        return true;
    }
    const Entity& entity = entities_[id.index];
    if (!entity.origin_unit.valid() ||
        entity.origin_unit == visibility_unit_) {
        return true;
    }
    if (id.index < module_redeclared_entities_.size() &&
        module_redeclared_entities_[id.index] != 0) {
        return true;
    }
    auto same_named_module = [&]() {
        if (!visibility_unit_.valid()) {
            return false;
        }
        const ModuleUnitFact& own = module_unit(visibility_unit_);
        const ModuleUnitFact& origin = module_unit(entity.origin_unit);
        return own.module_name.valid() &&
               own.module_name == origin.module_name;
    };
    bool imported = entity.origin_unit.index < visible_units_.size() &&
                    visible_units_[entity.origin_unit.index] != 0;
    if (!imported) {
        return same_named_module();
    }
    if (entity.is_module_exported) {
        return true;
    }

    return same_named_module();
}

bool File::binding_hidden_by_modules(const DeclContext& context,
                                     const Binding& binding) const {
    if (!has_module_units() || module_visibility_bypass_) {
        return false;
    }
    if (context.kind != DeclContextKind::Namespace &&
        context.kind != DeclContextKind::TranslationUnit) {
        return false;
    }
    for (EntityId entity_id : binding.entities) {
        if (entity_lookup_visible(entity_id)) {
            return false;
        }
    }
    return !binding.entities.empty();
}

const Binding* File::find_binding_via_directives(
    const DeclContext& context,
    uint64_t key,
    const OrdinaryBindingCategory* category,
    std::vector<uint32_t>& visited) const {
    for (size_t directive_index = 0;
         directive_index < context.using_directives.size();
         ++directive_index) {
        DeclContextId target = context.using_directives[directive_index];
        if (!valid(target)) {
            continue;
        }

        if (directive_index < context.using_directive_origins.size()) {
            ModuleAttachmentId origin =
                context.using_directive_origins[directive_index];
            if (origin.valid() && origin != visibility_unit_) {
                continue;
            }
        }
        if (std::find(visited.begin(), visited.end(), target.index) !=
            visited.end()) {
            continue;
        }
        visited.push_back(target.index);
        const DeclContext& nominated = decl_context(target);
        auto found = nominated.ordinary_latest_bindings.find(key);
        if (found != nominated.ordinary_latest_bindings.end() &&
            valid(found->second)) {
            const Binding& record = binding(found->second);
            if ((!category ||
                 ordinary_binding_matches_category(record, *category)) &&
                !binding_hidden_by_modules(nominated, record)) {
                return &record;
            }
        }

        if (const Binding* transitive =
                find_binding_via_directives(nominated, key, category, visited)) {
            return transitive;
        }
    }
    return nullptr;
}

const Binding* File::find_qualifier_binding_via_directives(
    const DeclContext& context,
    uint64_t key,
    std::vector<uint32_t>& visited) const {
    for (size_t directive_index = 0;
         directive_index < context.using_directives.size();
         ++directive_index) {
        DeclContextId target = context.using_directives[directive_index];
        if (!valid(target)) {
            continue;
        }

        if (directive_index < context.using_directive_origins.size()) {
            ModuleAttachmentId origin =
                context.using_directive_origins[directive_index];
            if (origin.valid() && origin != visibility_unit_) {
                continue;
            }
        }
        if (std::find(visited.begin(), visited.end(), target.index) !=
            visited.end()) {
            continue;
        }
        visited.push_back(target.index);
        const DeclContext& nominated = decl_context(target);
        auto ordinary = nominated.ordinary_latest_bindings.find(key);
        if (ordinary != nominated.ordinary_latest_bindings.end() &&
            valid(ordinary->second)) {
            const Binding& candidate = binding(ordinary->second);
            if (ordinary_binding_names_qualifier(candidate) &&
                !binding_hidden_by_modules(nominated, candidate)) {
                return &candidate;
            }
        }

        auto tag = nominated.tag_bindings.find(key);
        if (tag != nominated.tag_bindings.end() && valid(tag->second)) {
            const Binding& candidate = binding(tag->second);
            if (!binding_hidden_by_modules(nominated, candidate)) {
                return &candidate;
            }
        }

        if (const Binding* transitive =
                find_qualifier_binding_via_directives(
                    nominated, key, visited)) {
            return transitive;
        }
    }
    return nullptr;
}

const Binding* File::lookup_ordinary_binding(DeclContextId start,
                                             NameId name_id,
                                             bool include_parents) const {
    if (!valid(start) || !valid(name_id)) {
        return nullptr;
    }
    for (DeclContextId context_id = start; valid(context_id);
         context_id = include_parents ? decl_context(context_id).parent : DeclContextId{}) {
        const DeclContext& context = decl_context(context_id);
        auto found = context.ordinary_latest_bindings.find(id_key(name_id));
        if (found != context.ordinary_latest_bindings.end()) {
            if (!valid(found->second)) {
                return nullptr;
            }
            const Binding& record = binding(found->second);
            if (!binding_hidden_by_modules(context, record)) {
                return &record;
            }

        }
        if (!context.using_directives.empty()) {
            std::vector<uint32_t> visited{context_id.index};
            if (const Binding* nominated = find_binding_via_directives(
                    context, id_key(name_id), nullptr, visited)) {
                return nominated;
            }
        }
        if (!include_parents) {
            break;
        }
    }
    return nullptr;
}

const Binding* File::lookup_ordinary_binding(DeclContextId start,
                                             std::string_view spelling,
                                             bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_ordinary_binding(start, name_id, include_parents);
}

const Binding* File::lookup_direct_ordinary_binding(
    DeclContextId context_id,
    NameId name_id) const {
    if (!valid(context_id) || !valid(name_id)) {
        return nullptr;
    }
    const DeclContext& context = decl_context(context_id);
    auto found = context.ordinary_latest_bindings.find(id_key(name_id));
    if (found == context.ordinary_latest_bindings.end() ||
        !valid(found->second)) {
        return nullptr;
    }
    const Binding& record = binding(found->second);
    return binding_hidden_by_modules(context, record) ? nullptr : &record;
}

const Binding* File::lookup_direct_ordinary_binding(
    DeclContextId context,
    std::string_view spelling) const {
    return lookup_direct_ordinary_binding(
        context, find_existing_name(spelling));
}

const Binding* File::lookup_ordinary_category_binding(
    DeclContextId start,
    NameId name_id,
    OrdinaryBindingCategory category,
    bool include_parents) const {
    if (!valid(start) || !valid(name_id)) {
        return nullptr;
    }
    uint64_t key = id_key(name_id);
    for (DeclContextId context_id = start; valid(context_id);
         context_id = include_parents ? decl_context(context_id).parent : DeclContextId{}) {
        const DeclContext& context = decl_context(context_id);
        auto ordinary_found = context.ordinary_latest_bindings.find(key);
        if (ordinary_found == context.ordinary_latest_bindings.end()) {
            if (!context.using_directives.empty()) {
                std::vector<uint32_t> visited{context_id.index};
                if (const Binding* nominated = find_binding_via_directives(
                        context, key, &category, visited)) {
                    return nominated;
                }
            }
            if (!include_parents) {
                break;
            }
            continue;
        }

        const auto* category_map =
            category == OrdinaryBindingCategory::Value
                ? &context.ordinary_value_bindings
                : category == OrdinaryBindingCategory::Callable
                      ? &context.ordinary_callable_bindings
                      : category == OrdinaryBindingCategory::TypeName
                            ? &context.ordinary_type_name_bindings
                            : category == OrdinaryBindingCategory::TemplateName
                                  ? &context.ordinary_template_name_bindings
                                  : &context.ordinary_namespace_bindings;
        auto category_found = category_map->find(key);
        if (category_found != category_map->end() &&
            category_found->second == ordinary_found->second &&
            valid(category_found->second)) {
            const Binding& record = binding(category_found->second);
            if (!binding_hidden_by_modules(context, record)) {
                return &record;
            }

            if (!include_parents) {
                break;
            }
            continue;
        }
        return nullptr;
    }
    return nullptr;
}

const Binding* File::lookup_value_binding(DeclContextId start,
                                          NameId name_id,
                                          bool include_parents) const {
    return lookup_ordinary_category_binding(
        start, name_id, OrdinaryBindingCategory::Value, include_parents);
}

const Binding* File::lookup_value_binding(DeclContextId start,
                                          std::string_view spelling,
                                          bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_value_binding(start, name_id, include_parents);
}

const Binding* File::lookup_callable_binding(DeclContextId start,
                                             NameId name_id,
                                             bool include_parents) const {
    return lookup_ordinary_category_binding(
        start, name_id, OrdinaryBindingCategory::Callable, include_parents);
}

const Binding* File::lookup_callable_binding(DeclContextId start,
                                             std::string_view spelling,
                                             bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_callable_binding(start, name_id, include_parents);
}

const Binding* File::lookup_type_name_binding(DeclContextId start,
                                              NameId name_id,
                                              bool include_parents) const {
    return lookup_ordinary_category_binding(
        start, name_id, OrdinaryBindingCategory::TypeName, include_parents);
}

const Binding* File::lookup_type_name_binding(DeclContextId start,
                                              std::string_view spelling,
                                              bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_type_name_binding(start, name_id, include_parents);
}

const Binding* File::lookup_template_name_binding(DeclContextId start,
                                                  NameId name_id,
                                                  bool include_parents) const {
    return lookup_ordinary_category_binding(
        start, name_id, OrdinaryBindingCategory::TemplateName, include_parents);
}

const Binding* File::lookup_template_name_binding(DeclContextId start,
                                                  std::string_view spelling,
                                                  bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_template_name_binding(start, name_id, include_parents);
}

const Binding* File::lookup_indexed_namespace_binding(
    DeclContextId start,
    NameId name_id,
    LookupNamespace lookup_namespace,
    bool include_parents) const {
    if (!valid(start) || !valid(name_id)) {
        return nullptr;
    }
    uint64_t key = id_key(name_id);
    for (DeclContextId context_id = start; valid(context_id);
         context_id = include_parents ? decl_context(context_id).parent : DeclContextId{}) {
        const DeclContext& context = decl_context(context_id);
        const auto* map = lookup_namespace == LookupNamespace::Tag
                              ? &context.tag_bindings
                              : lookup_namespace == LookupNamespace::Label
                                    ? &context.label_bindings
                                    : nullptr;
        if (!map) {
            return nullptr;
        }
        auto found = map->find(key);
        if (found != map->end()) {
            if (!valid(found->second)) {
                return nullptr;
            }
            const Binding& record = binding(found->second);
            if (!binding_hidden_by_modules(context, record)) {
                return &record;
            }

        }
        if (!include_parents) {
            break;
        }
    }
    return nullptr;
}

const Binding* File::lookup_namespace_name_binding(DeclContextId start,
                                                   NameId name_id,
                                                   bool include_parents) const {
    return lookup_ordinary_category_binding(
        start, name_id, OrdinaryBindingCategory::NamespaceName, include_parents);
}

const Binding* File::lookup_namespace_name_binding(DeclContextId start,
                                                   std::string_view spelling,
                                                   bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_namespace_name_binding(start, name_id, include_parents);
}

const Binding* File::lookup_qualifier_binding(DeclContextId start,
                                              NameId name_id,
                                              bool include_parents) const {
    if (!valid(start) || !valid(name_id)) {
        return nullptr;
    }
    uint64_t key = id_key(name_id);
    for (DeclContextId context_id = start; valid(context_id);
         context_id = include_parents
             ? decl_context(context_id).parent
             : DeclContextId{}) {
        const DeclContext& context = decl_context(context_id);
        auto ordinary = context.ordinary_latest_bindings.find(key);
        if (ordinary != context.ordinary_latest_bindings.end() &&
            valid(ordinary->second)) {
            const Binding& candidate = binding(ordinary->second);
            if (ordinary_binding_names_qualifier(candidate) &&
                !binding_hidden_by_modules(context, candidate)) {
                return &candidate;
            }
        }

        if (!context.using_directives.empty()) {
            std::vector<uint32_t> visited{context_id.index};
            if (const Binding* nominated =
                    find_qualifier_binding_via_directives(
                        context, key, visited)) {
                return nominated;
            }
        }

        auto tag = context.tag_bindings.find(key);
        if (tag != context.tag_bindings.end() && valid(tag->second)) {
            const Binding& candidate = binding(tag->second);
            if (!binding_hidden_by_modules(context, candidate)) {
                return &candidate;
            }
        }

        if (!include_parents) {
            break;
        }
    }
    return nullptr;
}

const Binding* File::lookup_qualifier_binding(DeclContextId start,
                                              std::string_view spelling,
                                              bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_qualifier_binding(start, name_id, include_parents);
}

const Binding* File::lookup_tag_binding(DeclContextId start,
                                        NameId name_id,
                                        bool include_parents) const {
    return lookup_indexed_namespace_binding(
        start, name_id, LookupNamespace::Tag, include_parents);
}

const Binding* File::lookup_tag_binding(DeclContextId start,
                                        std::string_view spelling,
                                        bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_tag_binding(start, name_id, include_parents);
}

const Binding* File::lookup_label_binding(DeclContextId start,
                                          NameId name_id,
                                          bool include_parents) const {
    return lookup_indexed_namespace_binding(
        start, name_id, LookupNamespace::Label, include_parents);
}

const Binding* File::lookup_label_binding(DeclContextId start,
                                          std::string_view spelling,
                                          bool include_parents) const {
    NameId name_id = find_existing_name(spelling);
    if (!name_id.valid()) {
        return nullptr;
    }
    return lookup_label_binding(start, name_id, include_parents);
}

std::vector<BindingId> File::binding_ids() const {
    std::vector<BindingId> ids;
    ids.reserve(bindings_.size() > 0 ? bindings_.size() - 1 : 0);
    for (uint32_t i = 1; i < bindings_.size(); ++i) {
        ids.push_back(BindingId{i, binding_generations_[i]});
    }
    return ids;
}

PlaceFactId File::add_place_fact(PlaceFact fact) {
    return add_record<PlaceFact, PlaceFactId>(place_facts_,
                                              place_fact_generations_,
                                              std::move(fact));
}

const PlaceFact& File::place_fact(PlaceFactId id) const {
    static const PlaceFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    return place_facts_[id.index];
}

PlaceFact& File::place_fact_mut(PlaceFactId id) {
    static PlaceFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_place_fact_mutation(id);
    return place_facts_[id.index];
}

PlaceholderResultFactId File::add_placeholder_result_fact(
    PlaceholderResultFact fact) {
    return add_record<PlaceholderResultFact, PlaceholderResultFactId>(
        placeholder_result_facts_, placeholder_result_fact_generations_,
        std::move(fact));
}

const PlaceholderResultFact& File::placeholder_result_fact(
    PlaceholderResultFactId id) const {
    static const PlaceholderResultFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    return placeholder_result_facts_[id.index];
}

PlaceholderResultFact& File::placeholder_result_fact_mut(
    PlaceholderResultFactId id) {
    static PlaceholderResultFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_placeholder_result_fact_mutation(id);
    return placeholder_result_facts_[id.index];
}

ConstantStateId File::add_constant_state(ConstantStateFact fact) {
    return add_record<ConstantStateFact, ConstantStateId>(
        constant_states_, constant_state_generations_, std::move(fact));
}

const ConstantStateFact& File::constant_state(ConstantStateId id) const {
    static const ConstantStateFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    return constant_states_[id.index];
}

ClosureIdentityId File::add_closure_identity(ClosureIdentityFact fact) {
    return add_record<ClosureIdentityFact, ClosureIdentityId>(
        closure_identities_, closure_identity_generations_, std::move(fact));
}

const ClosureIdentityFact& File::closure_identity(
    ClosureIdentityId id) const {
    static const ClosureIdentityFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    return closure_identities_[id.index];
}

ClosureIdentityFact& File::closure_identity_mut(ClosureIdentityId id) {
    if (!valid(id)) {
        throw std::out_of_range("invalid closure identity id");
    }
    record_closure_identity_mutation(id);
    return closure_identities_[id.index];
}

std::vector<ClosureIdentityId> File::closure_identity_ids() const {
    std::vector<ClosureIdentityId> ids;
    ids.reserve(closure_identities_.size() > 0
                    ? closure_identities_.size() - 1
                    : 0);
    for (uint32_t index = 1; index < closure_identities_.size(); ++index) {
        ids.push_back(ClosureIdentityId{
            index, closure_identity_generations_[index]});
    }
    return ids;
}

SwitchId File::add_switch_fact(SwitchFact fact) {
    return add_record<SwitchFact, SwitchId>(switch_facts_,
                                            switch_fact_generations_,
                                            std::move(fact));
}

const SwitchFact& File::switch_fact(SwitchId id) const {
    static const SwitchFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    return switch_facts_[id.index];
}

std::vector<SwitchId> File::switch_ids() const {
    std::vector<SwitchId> ids;
    ids.reserve(switch_facts_.size() > 0 ? switch_facts_.size() - 1 : 0);
    for (uint32_t i = 1; i < switch_facts_.size(); ++i) {
        ids.push_back(SwitchId{i, switch_fact_generations_[i]});
    }
    return ids;
}

void File::add_coroutine_fact(CoroutineFact fact) {
    coroutine_facts_.push_back(std::move(fact));
}

const CoroutineFact* File::coroutine_fact_for_function(
    EntityId function) const {
    for (const CoroutineFact& fact : coroutine_facts_) {
        if (fact.function == function) {
            return &fact;
        }
    }
    return nullptr;
}

CoroutineFact* File::coroutine_fact_for_function_mut(EntityId function) {
    for (size_t index = 0; index < coroutine_facts_.size(); ++index) {
        if (coroutine_facts_[index].function == function) {
            record_coroutine_fact_mutation(index);
            return &coroutine_facts_[index];
        }
    }
    return nullptr;
}

ModuleAttachmentId File::add_module_unit(ModuleUnitFact fact) {
    return add_record<ModuleUnitFact, ModuleAttachmentId>(
        module_units_, module_unit_generations_, std::move(fact));
}

const ModuleUnitFact& File::module_unit(ModuleAttachmentId id) const {
    static const ModuleUnitFact invalid;
    if (!valid(id)) {
        return invalid;
    }
    return module_units_[id.index];
}

ModuleUnitFact* File::module_unit_mut(ModuleAttachmentId id) {
    if (!valid(id)) {
        return nullptr;
    }
    record_module_unit_mutation(id);
    return &module_units_[id.index];
}

bool File::valid(ModuleAttachmentId id) const {
    return valid_id(module_units_, module_unit_generations_, id);
}

std::vector<ModuleAttachmentId> File::module_unit_ids() const {
    std::vector<ModuleAttachmentId> ids;
    ids.reserve(module_units_.size() > 0 ? module_units_.size() - 1 : 0);
    for (uint32_t i = 1; i < module_units_.size(); ++i) {
        ids.push_back(ModuleAttachmentId{i, module_unit_generations_[i]});
    }
    return ids;
}

InstId File::add_inst(Inst inst) {
    return add_record<Inst, InstId>(insts_, inst_generations_, std::move(inst));
}

const Inst& File::inst(InstId id) const {
    static const Inst invalid;
    if (!valid(id)) {
        return invalid;
    }
    return insts_[id.index];
}

Inst& File::inst_mut(InstId id) {
    static Inst invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_inst_mutation(id);
    return insts_[id.index];
}

uint32_t File::add_payload(InstPayload payload) {
    payloads_.push_back(std::move(payload));
    return static_cast<uint32_t>(payloads_.size() - 1);
}

const InstPayload& File::payload(uint32_t index) const {
    static const InstPayload empty;
    if (index == 0 || index >= payloads_.size()) {
        return empty;
    }
    return payloads_[index];
}

InlineAsmPayloadId File::add_inline_asm_payload(InlineAsmPayload payload) {
    return add_record<InlineAsmPayload, InlineAsmPayloadId>(
        inline_asm_payloads_,
        inline_asm_payload_generations_,
        std::move(payload));
}

const InlineAsmPayload& File::inline_asm_payload(InlineAsmPayloadId id) const {
    static const InlineAsmPayload invalid;
    if (!valid(id)) {
        return invalid;
    }
    return inline_asm_payloads_[id.index];
}

OperandRange File::add_operands(const std::vector<Operand>& operands) {
    OperandRange range;
    range.first = static_cast<uint32_t>(operands_.size());
    range.count = static_cast<uint32_t>(operands.size());
    for (const Operand& operand : operands) {
        operands_.push_back(operand);
    }
    return range;
}

OperandRange File::add_value_operands(const std::vector<InstId>& operands) {
    std::vector<Operand> typed;
    typed.reserve(operands.size());
    for (InstId operand : operands) {
        typed.push_back(Operand::value(operand));
    }
    return add_operands(typed);
}

std::vector<Operand> File::operands(OperandRange range) const {
    std::vector<Operand> out;
    if (range.count == 0) {
        return out;
    }
    if (range.first >= operands_.size() ||
        range.first + range.count > operands_.size()) {
        return out;
    }
    out.reserve(range.count);
    for (uint32_t i = 0; i < range.count; ++i) {
        out.push_back(operands_[range.first + i]);
    }
    return out;
}

std::vector<ValueRef> File::value_operands(OperandRange range) const {
    std::vector<ValueRef> out;
    std::vector<Operand> typed = operands(range);
    out.reserve(typed.size());
    for (const Operand& operand : typed) {
        if (const auto* value = std::get_if<ValueRef>(&operand.data)) {
            out.push_back(*value);
        }
    }
    return out;
}

BlockId File::add_block(Block block) {
    return add_record<Block, BlockId>(blocks_, block_generations_, std::move(block));
}

void File::append_to_block(BlockId block_id, InstId inst_id) {
    if (!valid(block_id)) {
        return;
    }
    record_block_mutation(block_id);
    blocks_[block_id.index].instructions.push_back(inst_id);
}

void File::set_terminator(BlockId block_id, Terminator terminator) {
    if (!valid(block_id)) {
        return;
    }
    record_block_mutation(block_id);
    blocks_[block_id.index].terminator = std::move(terminator);
}

const Block& File::block(BlockId id) const {
    static const Block invalid;
    if (!valid(id)) {
        return invalid;
    }
    return blocks_[id.index];
}

Block& File::block_mut(BlockId id) {
    static Block invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_block_mutation(id);
    return blocks_[id.index];
}

FunctionId File::add_function(Function function) {
    return add_record<Function, FunctionId>(functions_, function_generations_, std::move(function));
}

const Function& File::function(FunctionId id) const {
    static const Function invalid;
    if (!valid(id)) {
        return invalid;
    }
    return functions_[id.index];
}

Function& File::function_mut(FunctionId id) {
    static Function invalid;
    if (!valid(id)) {
        return invalid;
    }
    record_function_mutation(id);
    return functions_[id.index];
}

std::vector<FunctionId> File::function_ids() const {
    std::vector<FunctionId> ids;
    ids.reserve(functions_.size() > 0 ? functions_.size() - 1 : 0);
    for (uint32_t i = 1; i < functions_.size(); ++i) {
        ids.push_back(FunctionId{i, function_generations_[i]});
    }
    return ids;
}

GenericId File::add_generic(Generic generic) {
    return add_record<Generic, GenericId>(generics_, generic_generations_, std::move(generic));
}

SpecificId File::add_specific(Specific specific) {
    return add_record<Specific, SpecificId>(specifics_, specific_generations_, std::move(specific));
}

size_t File::generic_count() const {
    return generics_.size() > 0 ? generics_.size() - 1 : 0;
}

size_t File::specific_count() const {
    return specifics_.size() > 0 ? specifics_.size() - 1 : 0;
}

bool File::valid(NameId id) const {
    return valid_id<std::string, NameId>(names_, name_generations_, id);
}

bool File::valid(EntityId id) const {
    return valid_id<Entity, EntityId>(entities_, entity_generations_, id);
}

bool File::valid(DeclContextId id) const {
    return valid_id<DeclContext, DeclContextId>(decl_contexts_,
                                                decl_context_generations_,
                                                id);
}

bool File::valid(BindingId id) const {
    return valid_id<Binding, BindingId>(bindings_,
                                        binding_generations_,
                                        id);
}

bool File::valid(PlaceFactId id) const {
    return valid_id<PlaceFact, PlaceFactId>(place_facts_, place_fact_generations_, id);
}

bool File::valid(PlaceholderResultFactId id) const {
    return valid_id<PlaceholderResultFact, PlaceholderResultFactId>(
        placeholder_result_facts_, placeholder_result_fact_generations_, id);
}

bool File::valid(ConstantStateId id) const {
    return valid_id<ConstantStateFact, ConstantStateId>(
        constant_states_, constant_state_generations_, id);
}

bool File::valid(ClosureIdentityId id) const {
    return valid_id<ClosureIdentityFact, ClosureIdentityId>(
        closure_identities_, closure_identity_generations_, id);
}

bool File::valid(SwitchId id) const {
    return valid_id<SwitchFact, SwitchId>(switch_facts_, switch_fact_generations_, id);
}

bool File::valid(InstId id) const {
    return valid_id<Inst, InstId>(insts_, inst_generations_, id);
}

bool File::valid(BlockId id) const {
    return valid_id<Block, BlockId>(blocks_, block_generations_, id);
}

bool File::valid(FunctionId id) const {
    return valid_id<Function, FunctionId>(functions_, function_generations_, id);
}

bool File::valid(InlineAsmPayloadId id) const {
    return valid_id<InlineAsmPayload, InlineAsmPayloadId>(
        inline_asm_payloads_,
        inline_asm_payload_generations_,
        id);
}

std::string File::format_type(TypeId id) const {
    return format_type(type_ref(id));
}

std::string File::format_type(TypeRef ref) const {
    TypeId id = ref.type;
    if (!valid(id)) {
        return "<none>";
    }
    const Type& t = type(id);
    const TypePayload& payload = type_payload(id);
    std::string prefix = type_ref_prefix(ref);
    switch (t.kind) {
        case TypeKind::Builtin: {
            const auto* builtin = std::get_if<BuiltinTypePayload>(&payload);
            if (builtin && !builtin->spelling.empty()) {
                return prefix + builtin->spelling;
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("builtin"));
        }
        case TypeKind::Record: {
            const auto* record = std::get_if<RecordTypePayload>(&payload);
            if (record && record->name.valid()) {
                return prefix + name(record->name);
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("record"));
        }
        case TypeKind::Enum: {
            const auto* enum_payload = std::get_if<EnumTypePayload>(&payload);
            if (enum_payload && enum_payload->name.valid()) {
                return prefix + name(enum_payload->name);
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("enum"));
        }
        case TypeKind::Vector: {
            const auto* vector = std::get_if<VectorTypePayload>(&payload);
            if (!vector) {
                return prefix + "<invalid-vector>";
            }
            std::ostringstream out;
            out << prefix << format_type(vector->element_type)
                << " __attribute__((vector_size(" << vector->size_bytes << ")))";
            return out.str();
        }
        case TypeKind::Complex: {
            const auto* complex = std::get_if<ComplexTypePayload>(&payload);
            return complex ? prefix + "_Complex " + format_type(complex->element_type)
                           : prefix + "<invalid-complex>";
        }
        case TypeKind::BitInt: {
            const auto* bit_int = std::get_if<BitIntTypePayload>(&payload);
            if (!bit_int) {
                return prefix + "<invalid-bitint>";
            }
            std::string spelling = bit_int->is_unsigned ? "unsigned _BitInt(" : "_BitInt(";
            return prefix + spelling + std::to_string(bit_int->bits) + ")";
        }
        case TypeKind::Typedef: {
            const auto* typedef_payload = std::get_if<TypedefTypePayload>(&payload);
            if (typedef_payload && typedef_payload->name.valid()) {
                return prefix + name(typedef_payload->name);
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("typedef"));
        }
        case TypeKind::TypeParam: {
            const auto* param = std::get_if<TypeParamTypePayload>(&payload);
            if (param && param->name.valid()) {
                return prefix + name(param->name);
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("type-param"));
        }
        case TypeKind::Dependent: {
            const auto* dependent = std::get_if<DependentTypePayload>(&payload);
            if (dependent && dependent->debug_name.valid()) {
                return prefix + name(dependent->debug_name);
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("<dependent>"));
        }
        case TypeKind::Unknown: {
            const auto* unknown = std::get_if<UnknownTypePayload>(&payload);
            if (unknown && !unknown->debug_name.empty()) {
                return prefix + unknown->debug_name;
            }
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("<unknown>"));
        }
        case TypeKind::Pointer: {
            const auto* pointer = std::get_if<PointerTypePayload>(&payload);
            return pointer ? prefix + "*" + format_type(pointer->pointee)
                           : prefix + "<invalid-pointer>";
        }
        case TypeKind::BlockPointer: {
            const auto* pointer = std::get_if<BlockPointerTypePayload>(&payload);
            return pointer ? prefix + "^" + format_type(pointer->pointee)
                           : prefix + "<invalid-block-pointer>";
        }
        case TypeKind::MemberPointer: {
            const auto* member = std::get_if<MemberPointerTypePayload>(&payload);
            return member ? prefix + format_type(member->class_type) + "::*" +
                                format_type(member->member_type)
                          : prefix + "<invalid-member-pointer>";
        }
        case TypeKind::LValueReference:
        case TypeKind::RValueReference: {
            const auto* reference = std::get_if<ReferenceTypePayload>(&payload);
            if (!reference) {
                return prefix + "<invalid-reference>";
            }
            return prefix + format_type(reference->referred_type) +
                   (reference->reference_kind == ReferenceKind::LValue ? "&" : "&&");
        }
        case TypeKind::Array: {
            const auto* array = std::get_if<ArrayTypePayload>(&payload);
            if (!array) {
                return prefix + "<invalid-array>";
            }
            std::ostringstream out;
            out << prefix << format_type(array->element_type) << '[';
            if (array->size.has_value()) {
                out << *array->size;
            } else if (array->size_kind == ArraySizeKind::Variable) {
                out << "vla";
            }
            out << ']';
            return out.str();
        }
        case TypeKind::Place: {
            const auto* place = std::get_if<PlaceTypePayload>(&payload);
            return place ? prefix + "place<" + format_type(place->object_type) + ">"
                         : prefix + "<invalid-place>";
        }
        case TypeKind::Function: {
            const auto* function = std::get_if<FunctionTypePayload>(&payload);
            if (!function) {
                return prefix + "<invalid-function>";
            }
            std::ostringstream out;
            out << prefix << '(';
            for (size_t i = 0; i < function->parameters.size(); ++i) {
                if (i > 0) out << ", ";
                out << format_type(function->parameters[i]);
            }
            if (function->is_variadic) {
                if (!function->parameters.empty()) out << ", ";
                out << "...";
            }
            out << ')';
            if (function->exception_spec.kind ==
                FunctionExceptionSpecKind::NonThrowing) {
                out << " noexcept";
            } else if (function->exception_spec.kind ==
                       FunctionExceptionSpecKind::Dependent) {
                out << " noexcept(<dependent>)";
            }
            out << " -> " << format_type(function->return_type);
            return out.str();
        }
        case TypeKind::TemplateSpecialization:
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("<template-specialization>"));
        case TypeKind::AliasSpecialization:
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("<alias-specialization>"));
        case TypeKind::DependentName:
            return prefix + (t.debug_name.valid() ? name(t.debug_name) : std::string("<dependent-name>"));
        case TypeKind::Placeholder:
            return prefix + "<placeholder>";
        case TypeKind::Auto:
            return prefix + "auto";
        case TypeKind::TypeofExpr:
            return prefix + "typeof(<expr>)";
        case TypeKind::DecltypeExpr:
            return prefix + "decltype(<expr>)";
        case TypeKind::BuiltinTransform:
            return prefix + "<builtin-transform>";
        case TypeKind::BuiltinPackElement:
            return prefix + "<builtin-pack-element>";
        case TypeKind::PackIndex: {
            const auto* pack_index =
                std::get_if<PackIndexTypePayload>(&payload);
            return pack_index
                ? prefix + format_type(pack_index->pack_type) +
                      "...[<dependent>]"
                : prefix + "<invalid-pack-index>";
        }
        case TypeKind::Error:
            return prefix + "<error>";
        case TypeKind::Invalid:
            break;
    }
    return "<invalid-type>";
}

std::string File::format_entity(EntityId id) const {
    if (!valid(id)) {
        return "<none>";
    }
    const Entity& e = entity(id);
    if (e.name.valid()) {
        return "@" + name(e.name);
    }
    return "@" + std::to_string(id.index);
}

std::string File::format_inst(InstId id) const {
    if (!valid(id)) {
        return "<none>";
    }
    return "%" + std::to_string(id.index);
}

std::string File::format_value(ValueRef ref) const {
    return format_inst(ref.inst);
}

std::string File::format_operand(const Operand& operand) const {
    switch (operand.kind) {
        case OperandKind::None:
            return "<none>";
        case OperandKind::Value:
            if (const auto* value = std::get_if<ValueRef>(&operand.data)) {
                return format_value(*value);
            }
            return "<invalid-value-operand>";
        case OperandKind::Type:
            if (const auto* type = std::get_if<TypeRef>(&operand.data)) {
                return format_type(*type);
            }
            return "<invalid-type-operand>";
        case OperandKind::Entity:
            if (const auto* entity_id = std::get_if<EntityId>(&operand.data)) {
                return format_entity(*entity_id);
            }
            return "<invalid-entity-operand>";
        case OperandKind::Name:
            if (const auto* name_id = std::get_if<NameId>(&operand.data)) {
                return valid(*name_id) ? name(*name_id) : std::string("<invalid-name-operand>");
            }
            return "<invalid-name-operand>";
        case OperandKind::Specific:
            if (const auto* specific_id = std::get_if<SpecificId>(&operand.data)) {
                return specific_id->valid()
                    ? "specific#" + std::to_string(specific_id->index)
                    : std::string("<invalid-specific-operand>");
            }
            return "<invalid-specific-operand>";
    }
    return "<unknown-operand>";
}

void File::add_error(std::string message, SrcLoc loc) {
    errors_.emplace_back(loc, std::move(message));
}

void File::add_warning(std::string message, SrcLoc loc) {
    warnings_.emplace_back(loc, std::move(message));
}

void File::add_note(std::string message, SrcLoc loc) {
    notes_.emplace_back(loc, std::move(message));
}

bool File::is_void_type(TypeId id) const {
    if (!valid(id) || type(id).kind != TypeKind::Builtin) {
        return false;
    }
    const auto* builtin = std::get_if<BuiltinTypePayload>(&type_payload(id));
    return builtin && builtin->kind == BuiltinTypeKind::Void;
}

TypeId File::operand_result_type(InstId id) const {
    if (!valid(id)) {
        return {};
    }
    return inst(id).result_type;
}

TypeId File::operand_result_type(ValueRef ref) const {
    return operand_result_type(ref.inst);
}

bool File::verify_inst(InstId id, std::ostream* err) const {
    bool ok = true;
    auto fail = [&](const std::string& message) {
        ok = false;
        if (err) {
            *err << "CIR verification failed for " << format_inst(id)
                 << ": " << message << '\n';
        }
    };

    const Inst& instruction = inst(id);
    if (instruction.result_type.valid() && !valid(instruction.result_type)) {
        fail("result type is invalid");
    }
    if (instruction.payload_index >= payloads_.size()) {
        fail("payload index is out of bounds");
    }
    if (instruction.operands.first + instruction.operands.count > operands_.size()) {
        fail("operand range is out of bounds");
        return ok;
    }
    std::vector<Operand> ops = operands(instruction.operands);
    for (const Operand& operand : ops) {
        switch (operand.kind) {
            case OperandKind::None:
                fail("operand kind is none");
                break;
            case OperandKind::Value: {
                const auto* value = std::get_if<ValueRef>(&operand.data);
                if (!value || !valid(value->inst)) {
                    fail("value operand is invalid");
                }
                break;
            }
            case OperandKind::Type: {
                const auto* type_operand = std::get_if<TypeRef>(&operand.data);
                if (!type_operand || !type_operand->type.valid() || !valid(type_operand->type)) {
                    fail("type operand is invalid");
                }
                break;
            }
            case OperandKind::Entity: {
                const auto* entity_operand = std::get_if<EntityId>(&operand.data);
                if (!entity_operand || !valid(*entity_operand)) {
                    fail("entity operand is invalid");
                }
                break;
            }
            case OperandKind::Name: {
                const auto* name_operand = std::get_if<NameId>(&operand.data);
                if (!name_operand || !valid(*name_operand)) {
                    fail("name operand is invalid");
                }
                break;
            }
            case OperandKind::Specific: {
                const auto* specific_operand = std::get_if<SpecificId>(&operand.data);
                if (!specific_operand || !specific_operand->valid()) {
                    fail("specific operand is invalid");
                }
                break;
            }
        }
    }
    auto value_at = [&](size_t index) -> ValueRef {
        if (index >= ops.size()) return {};
        const auto* value = std::get_if<ValueRef>(&ops[index].data);
        return value ? *value : ValueRef{};
    };
    auto type_at = [&](size_t index) -> TypeRef {
        if (index >= ops.size()) return {};
        const auto* type_operand = std::get_if<TypeRef>(&ops[index].data);
        return type_operand ? *type_operand : TypeRef{};
    };
    auto entity_at = [&](size_t index) -> EntityId {
        if (index >= ops.size()) return {};
        const auto* entity_operand = std::get_if<EntityId>(&ops[index].data);
        return entity_operand ? *entity_operand : EntityId{};
    };
    const InstPayload& data = payload(instruction.payload_index);
    if (const auto* call = std::get_if<CallPayload>(&data)) {
        if (instruction.kind != InstKind::Call) {
            fail("call payload is only valid on a call");
        }
        if (call->virtual_declaration.valid() &&
            !valid(call->virtual_declaration)) {
            fail("virtual-call payload has an invalid declaration");
        }
        if (!call->virtual_declaration.valid() && !call->must_tail) {
            fail("call payload carries neither a virtual declaration nor "
                 "the must-tail flag");
        }
    }
    const InstSchema& schema = inst_schema(instruction.kind);
    if (schema.kind != instruction.kind) {
        fail("instruction kind has no schema");
    } else {
        if (!inst_operand_count_matches(schema.operand_shape, instruction.operands.count)) {
            fail("operand count does not match instruction schema");
        } else if (!inst_operand_kinds_match(schema.operand_shape, ops)) {
            fail("operand kinds do not match instruction schema");
        }
        if (schema.result_shape == ResultShape::NoResult) {
            if (instruction.result_type.valid()) {
                fail("instruction must not produce a value");
            }
        } else if (!instruction.result_type.valid()) {
            fail("instruction must produce a value");
        }
    }
    if (instruction.result_object_entity.valid()) {
        if (!valid(instruction.result_object_entity)) {
            fail("result-object entity is invalid");
        }
        if (instruction.kind != InstKind::Call) {
            fail("only a call may name a result-object entity");
        }
        if (valid(instruction.result_object_entity) &&
            valid(instruction.result_type) &&
            resolved_type(entity(instruction.result_object_entity).type) !=
                resolved_type(instruction.result_type)) {
            fail("result-object entity type does not match call result");
        }
    }
    if (instruction.runtime_elided_object_operation &&
        instruction.kind != InstKind::Call &&
        instruction.kind != InstKind::ConstructInPlace &&
        instruction.kind != InstKind::Store) {
        fail("runtime object elision is invalid for this instruction kind");
    }

    bool result_is_place =
        valid(instruction.result_type) && type(instruction.result_type).kind == TypeKind::Place;
    if (instruction.place_fact.valid()) {
        if (!valid(instruction.place_fact)) {
            fail("place fact is invalid");
        } else {
            const PlaceFact& fact = place_fact(instruction.place_fact);
            if (!result_is_place) {
                fail("non-place result must not have a place fact");
            }
            if (fact.object_type.type.valid() && !valid(fact.object_type.type)) {
                fail("place fact has invalid object type");
            }
            if (fact.entity.valid() && !valid(fact.entity)) {
                fail("place fact has invalid entity");
            }
            if (fact.base.valid() && !valid(fact.base)) {
                fail("place fact has invalid base");
            }
            if (!fact.source.valid() || fact.source != id) {
                fail("place fact source must name the producing instruction");
            }
            if (result_is_place && fact.object_type != place_object_ref(instruction.result_type)) {
                fail("place fact object type must match result place type");
            }
        }
    } else if (result_is_place) {
        fail("place result must have a place fact");
    }

    auto check_descriptor_type = [&](TypeRef ref, std::string_view label) {
        if (!ref.type.valid()) {
            fail(std::string(label) + " is missing");
        } else if (!valid(ref.type)) {
            fail(std::string(label) + " is invalid");
        }
    };

    switch (instruction.kind) {
        case InstKind::Param: {
            EntityId entity_id = entity_at(0);
            if (!valid(entity_id) || entity(entity_id).kind != EntityKind::Parameter) {
                fail("param operand must name a parameter entity");
            }
            break;
        }
        case InstKind::IntegerLiteral:
            if (const auto* literal = std::get_if<LiteralPayload>(&data)) {
                const auto* value =
                    std::get_if<IntegerValue>(&literal->value);
                if (!value || !value->canonical()) {
                    fail("integer literal payload value is invalid");
                } else if (valid(instruction.result_type) &&
                           is_integer_like_type(
                               *this, instruction.result_type)) {
                    IntegerTypeShape shape = integer_shape_for_type(
                        *this, instruction.result_type);
                    if (value->bit_width != shape.bit_width ||
                        value->is_unsigned != shape.is_unsigned) {
                        fail("integer literal payload shape does not match "
                             "its result type");
                    }
                }
            } else {
                fail("integer literal payload value is invalid");
            }
            if (valid(instruction.result_type) &&
                type(instruction.result_type).kind == TypeKind::Builtin) {
                const auto* builtin =
                    std::get_if<BuiltinTypePayload>(&type_payload(instruction.result_type));
                if (builtin && builtin->kind == BuiltinTypeKind::NullPtr) {
                    fail("integer literal must not have nullptr_t result type");
                }
            }
            break;
        case InstKind::BooleanLiteral:
            if (const auto* literal = std::get_if<LiteralPayload>(&data)) {
                if (!std::holds_alternative<bool>(literal->value)) {
                    fail("boolean literal payload value is invalid");
                }
            } else {
                fail("boolean literal payload value is invalid");
            }
            break;
        case InstKind::NullptrLiteral:
            if (const auto* literal = std::get_if<LiteralPayload>(&data)) {
                if (!std::holds_alternative<std::monostate>(literal->value)) {
                    fail("nullptr literal payload value is invalid");
                }
            } else {
                fail("nullptr literal payload value is invalid");
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Builtin) {
                fail("nullptr literal result type must be nullptr_t");
            } else {
                const auto* builtin =
                    std::get_if<BuiltinTypePayload>(&type_payload(instruction.result_type));
                if (!builtin || builtin->kind != BuiltinTypeKind::NullPtr) {
                    fail("nullptr literal result type must be nullptr_t");
                }
            }
            break;
        case InstKind::FloatingLiteral:
            if (const auto* literal = std::get_if<LiteralPayload>(&data)) {
                const auto* value =
                    std::get_if<FloatingValue>(&literal->value);
                if (!value || !value->canonical()) {
                    fail("floating literal payload value is invalid");
                } else if (value->semantics !=
                           floating::semantics_for_type(
                               *this, instruction.result_type)) {
                    fail("floating literal payload semantics do not match its result type");
                }
            } else {
                fail("floating literal payload value is invalid");
            }
            break;
        case InstKind::CharacterLiteral:
            if (const auto* literal = std::get_if<LiteralPayload>(&data)) {
                if (!std::holds_alternative<LiteralByteArray>(literal->value)) {
                    fail("character literal payload value is invalid");
                }
            } else {
                fail("character literal payload value is invalid");
            }
            break;
        case InstKind::StringLiteral:
            if (const auto* literal = std::get_if<LiteralPayload>(&data)) {
                if (!std::holds_alternative<LiteralByteArray>(literal->value)) {
                    fail("string literal payload value is invalid");
                }
            } else {
                fail("string literal payload value is invalid");
            }
            break;
        case InstKind::UnaryOp: {
            const auto* descriptor = std::get_if<UnaryOpDescriptor>(&data);
            if (!descriptor) {
                fail("unary_op payload must carry a unary descriptor");
                break;
            }
            if (descriptor->op == UnaryOpKind::Invalid) {
                fail("unary_op descriptor has invalid operator");
            }
            check_descriptor_type(descriptor->computation_type, "unary computation type");
            break;
        }
        case InstKind::BinaryOp: {
            const auto* descriptor = std::get_if<BinaryOpDescriptor>(&data);
            if (!descriptor) {
                fail("binary_op payload must carry a binary descriptor");
                break;
            }
            if (descriptor->op == BinaryOpKind::Invalid) {
                fail("binary_op descriptor has invalid operator");
            }
            check_descriptor_type(descriptor->computation_type, "binary computation type");
            break;
        }
        case InstKind::LocalPlace: {
            EntityId entity_id = entity_at(0);
            if (!valid(entity_id)) {
                fail("local_place operand must name an entity");
                break;
            }
            EntityKind kind = entity(entity_id).kind;
            if (kind != EntityKind::Variable && kind != EntityKind::Parameter) {
                fail("local_place operand must name a variable or parameter entity");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("local_place result must be a place");
                break;
            }
            TypeRef expected = type_ref(entity(entity_id).type,
                                        entity(entity_id).qualifiers,
                                        entity(entity_id).memory_space);
            if (place_object_ref(instruction.result_type) != expected) {
                fail("local_place result must match entity type");
            }
            break;
        }
        case InstKind::GlobalPlace: {
            EntityId entity_id = entity_at(0);
            if (!valid(entity_id) ||
                entity(entity_id).kind != EntityKind::Variable) {
                std::string detail =
                    "global_place operand must name a variable entity";
                if (valid(entity_id)) {
                    detail += " (got ";
                    detail += entity_kind_name(entity(entity_id).kind);
                    if (entity(entity_id).name.valid()) {
                        detail += " '";
                        detail += name(entity(entity_id).name);
                        detail += "'";
                    }
                    detail += ")";
                }
                fail(std::move(detail));
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("global_place result must be a place");
                break;
            }
            TypeRef expected = type_ref(entity(entity_id).type,
                                        entity(entity_id).qualifiers,
                                        entity(entity_id).memory_space);
            if (place_object_ref(instruction.result_type) != expected) {
                fail("global_place result must match entity type");
            }
            break;
        }
        case InstKind::Load: {
            if (ops.size() != 1) {
                fail("load expects one operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("load operand must be a place");
                break;
            }
            if (instruction.result_type != place_object_type(place)) {
                fail("load result must match place object type");
            }
            break;
        }
        case InstKind::LValueToRValue: {
            if (ops.size() != 1) {
                fail("lvalue_to_rvalue expects one operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("lvalue_to_rvalue operand must be a place");
                break;
            }
            if (instruction.result_type != place_object_type(place)) {
                fail("lvalue_to_rvalue result must match place object type");
            }
            break;
        }
        case InstKind::FunctionToPointer: {
            EntityId entity_id = entity_at(0);
            const RecordMethodFact* method =
                valid(entity_id) && entity(entity_id).kind == EntityKind::Method
                    ? method_fact(entity_id)
                    : nullptr;
            if (!valid(entity_id) ||
                (entity(entity_id).kind != EntityKind::Function &&
                 !(method && method->is_static))) {
                fail("function_to_pointer operand must name a function or static method entity");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Pointer) {
                fail("function_to_pointer result must be a pointer");
                break;
            }
            TypeId pointee = pointer_pointee_type(instruction.result_type);
            if (pointee != entity(entity_id).type) {
                fail("function_to_pointer result must point to the function type");
            }
            break;
        }
        case InstKind::MemberPointerValue: {
            EntityId entity_id = entity_at(0);
            if (!valid(entity_id) ||
                (entity(entity_id).kind != EntityKind::Field &&
                 entity(entity_id).kind != EntityKind::Method)) {
                fail("member_pointer_value operand must name a field or method entity");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::MemberPointer) {
                fail("member_pointer_value result must be a member pointer");
                break;
            }
            const auto* member_pointer =
                std::get_if<MemberPointerTypePayload>(
                    &type_payload(instruction.result_type));
            if (!member_pointer) {
                fail("member_pointer_value result has malformed member pointer type");
                break;
            }
            EntityId owner = entity(entity_id).declaring_record.valid()
                ? entity(entity_id).declaring_record
                : entity(entity_id).parent;
            if (!valid(owner) || entity(owner).kind != EntityKind::Record) {
                fail("member_pointer_value operand must belong to a record");
                break;
            }
            TypeId target_class =
                resolved_type(member_pointer->class_type.type);
            if (!valid(target_class) ||
                target_class != resolved_type(entity(owner).type)) {
                fail("member_pointer_value result class must match member owner");
            }
            TypeId target_member =
                resolved_type(member_pointer->member_type.type);
            if (entity(entity_id).kind == EntityKind::Field) {
                const RecordFieldFact* field = field_fact(entity_id);
                if (!field) {
                    fail("member_pointer_value field operand is not in record facts");
                    break;
                }
                if (field->is_bitfield) {
                    fail("member_pointer_value cannot name a bit-field");
                }
                if (!valid(target_member) ||
                    target_member != resolved_type(entity(entity_id).type)) {
                    fail("member_pointer_value result member type must match field type");
                }
                break;
            }
            const RecordMethodFact* method = method_fact(entity_id);
            if (!method || method->is_static) {
                fail("member_pointer_value method operand must name a non-static method");
                break;
            }
            if (!valid(target_member) ||
                target_member != resolved_type(method->type.type)) {
                fail("member_pointer_value result member type must match method type");
            }
            break;
        }
        case InstKind::LabelAddress: {
            const auto* label = std::get_if<LabelAddressPayload>(&data);
            if (!label) {
                fail("label_address payload must carry label metadata");
                break;
            }
            if (!valid(label->name)) {
                fail("label_address name is invalid");
            }
            if (!valid(label->target)) {
                fail("label_address target block is invalid");
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Pointer) {
                fail("label_address result must be void*");
                break;
            }
            TypeId pointee = pointer_pointee_type(instruction.result_type);
            if (!valid(pointee) || type(pointee).kind != TypeKind::Builtin) {
                fail("label_address result must be void*");
                break;
            }
            const auto* builtin = std::get_if<BuiltinTypePayload>(&type_payload(pointee));
            if (!builtin || builtin->kind != BuiltinTypeKind::Void) {
                fail("label_address result must be void*");
            }
            break;
        }
        case InstKind::Store: {
            if (ops.size() != 2) {
                fail("store expects two operands");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            TypeId value = operand_result_type(value_at(1));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("store destination must be a place");
                break;
            }
            if (value != place_object_type(place)) {
                fail("store value type must match place object type");
            }
            if (instruction.result_type.valid()) {
                fail("store must not produce a value");
            }
            break;
        }
        case InstKind::ZeroObject: {
            if (ops.size() != 1) {
                fail("zero_object expects one operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("zero_object destination must be a place");
                break;
            }
            if (instruction.result_type.valid()) {
                fail("zero_object must not produce a value");
            }
            break;
        }
        case InstKind::StackAlloc: {
            if (ops.size() != 2) {
                fail("stack_alloc expects a type and a size operand");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("stack_alloc must produce a place");
            }
            break;
        }
        case InstKind::StackSave:
            if (!ops.empty()) {
                fail("stack_save takes no operands");
            }
            break;
        case InstKind::StackRestore:
            if (ops.size() != 1) {
                fail("stack_restore expects one operand");
            }
            if (instruction.result_type.valid()) {
                fail("stack_restore must not produce a value");
            }
            break;
        case InstKind::LifetimeStart:
        case InstKind::LifetimeEnd:

            if (ops.size() > 1) {
                fail("lifetime markers take at most one place operand");
            }
            if (instruction.result_type.valid()) {
                fail("lifetime markers must not produce a value");
            }
            break;
        case InstKind::AtomicLoad: {
            if (ops.size() != 1) {
                fail("atomic_load expects one place operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("atomic_load operand must be a place");
            }
            if (!std::holds_alternative<AtomicPayload>(data)) {
                fail("atomic_load requires an atomic payload");
            }
            break;
        }
        case InstKind::AtomicStore: {
            if (ops.size() != 2) {
                fail("atomic_store expects a place and a value operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("atomic_store destination must be a place");
            }
            if (instruction.result_type.valid()) {
                fail("atomic_store must not produce a value");
            }
            if (!std::holds_alternative<AtomicPayload>(data)) {
                fail("atomic_store requires an atomic payload");
            }
            break;
        }
        case InstKind::AtomicRmw: {
            if (ops.size() != 2) {
                fail("atomic_rmw expects a place and a value operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("atomic_rmw destination must be a place");
            }
            const auto* atomic =
                std::get_if<AtomicPayload>(&data);
            if (!atomic) {
                fail("atomic_rmw requires an atomic payload");
                break;
            }
            TypeId object = place_object_type(place);
            if (resolved_type(instruction.result_type) !=
                resolved_type(object)) {
                fail("atomic_rmw must produce the destination object type");
            }
            TypeId operand = operand_result_type(value_at(1));
            TypeId resolved_object = resolved_type(object);
            bool pointer_arithmetic =
                valid(resolved_object) &&
                type(resolved_object).kind == TypeKind::Pointer &&
                (atomic->rmw_op == AtomicRmwOp::Add ||
                 atomic->rmw_op == AtomicRmwOp::Sub);
            if (pointer_arithmetic) {
                OperatorValueDomain domain =
                    operator_value_domain(type_ref(operand));
                if (domain != OperatorValueDomain::SignedInteger &&
                    domain != OperatorValueDomain::UnsignedInteger) {
                    fail("pointer atomic_rmw requires an integer byte delta");
                }
            }
            break;
        }
        case InstKind::AtomicCmpXchg: {
            if (ops.size() != 3) {
                fail("atomic_cmpxchg expects place, expected place, and desired operands");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            TypeId expected = operand_result_type(value_at(1));
            if (!valid(place) || type(place).kind != TypeKind::Place ||
                !valid(expected) || type(expected).kind != TypeKind::Place) {
                fail("atomic_cmpxchg place operands must be places");
            }
            if (!std::holds_alternative<AtomicPayload>(data)) {
                fail("atomic_cmpxchg requires an atomic payload");
            }
            break;
        }
        case InstKind::ComplexMake:
            if (ops.size() != 2) {
                fail("complex_make expects real and imaginary operands");
            }
            if (!valid(instruction.result_type) ||
                type(resolved_type(instruction.result_type)).kind != TypeKind::Complex) {
                fail("complex_make must produce a complex value");
            }
            break;
        case InstKind::ComplexReal:
        case InstKind::ComplexImag:
            if (ops.size() != 1) {
                fail("complex element extraction expects one operand");
            }
            break;
        case InstKind::ComplexRealPlace:
        case InstKind::ComplexImagPlace: {
            if (ops.size() != 1) {
                fail("complex element place expects one place operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("complex element place operand must be a place");
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("complex element place must produce a place");
            }
            break;
        }
        case InstKind::AtomicFence:
            if (!ops.empty()) {
                fail("atomic_fence takes no operands");
            }
            if (!std::holds_alternative<AtomicPayload>(data)) {
                fail("atomic_fence requires an atomic payload");
            }
            break;
        case InstKind::AddrOf: {
            if (ops.size() != 1) {
                fail("addr_of expects one operand");
                break;
            }
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("addr_of operand must be a place");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Pointer) {
                fail("addr_of result must be a pointer");
                break;
            }
            if (pointer_pointee_ref(instruction.result_type) != place_object_ref(place)) {
                fail("addr_of result must point to the place object type");
            }
            break;
        }
        case InstKind::Deref: {
            if (ops.size() != 1) {
                fail("deref expects one operand");
                break;
            }
            TypeId pointer =
                resolved_type(operand_result_type(value_at(0)));

            bool is_reference =
                valid(pointer) &&
                (type(pointer).kind == TypeKind::LValueReference ||
                 type(pointer).kind == TypeKind::RValueReference);
            if (!valid(pointer) ||
                (type(pointer).kind != TypeKind::Pointer && !is_reference)) {
                fail("deref operand must be a pointer or reference");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("deref result must be a place");
                break;
            }
            TypeRef indirected = is_reference ? reference_referred_ref(pointer)
                                              : pointer_pointee_ref(pointer);
            if (place_object_ref(instruction.result_type) != indirected) {
                fail("deref result must match pointer pointee type");
            }
            break;
        }
        case InstKind::FieldAddr: {
            if (ops.size() != 2) {
                fail("field_addr expects base and field operands");
                break;
            }
            TypeId base = operand_result_type(value_at(0));
            if (!valid(base) || type(base).kind != TypeKind::Place) {
                fail("field_addr base must be a place");
                break;
            }
            EntityId field = entity_at(1);
            if (!valid(field) || entity(field).kind != EntityKind::Field) {
                fail("field_addr field operand must name a field entity");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("field_addr result must be a place");
                break;
            }
            TypeRef expected = type_ref(entity(field).type, entity(field).qualifiers);
            TypeRef base_object = place_object_ref(base);
            if (expected.memory_space == MemorySpace::Default &&
                base_object.memory_space != MemorySpace::Default) {
                expected.memory_space = base_object.memory_space;
            }

            uint8_t inherited =
                base_object.qualifiers & (QualConst | QualVolatile);
            if (const RecordFieldFact* fact = field_fact(field);
                fact && fact->is_mutable) {
                inherited &= ~QualConst;
            }
            expected.qualifiers |= inherited;
            if (place_object_ref(instruction.result_type) != expected) {
                fail("field_addr result must match field type");
            }
            break;
        }
        case InstKind::DataMemberPointerPlace: {
            if (ops.size() != 2) {
                fail("data_member_pointer_place expects base and member pointer operands");
                break;
            }
            TypeId base = operand_result_type(value_at(0));
            if (!valid(base) || type(base).kind != TypeKind::Place) {
                fail("data_member_pointer_place base must be a place");
                break;
            }
            TypeId pointer = operand_result_type(value_at(1));
            pointer = resolved_type(pointer);
            if (!valid(pointer) || type(pointer).kind != TypeKind::MemberPointer) {
                fail("data_member_pointer_place operand must be a member pointer");
                break;
            }
            if (member_pointer_points_to_function(pointer)) {
                fail("data_member_pointer_place requires a data-member pointer");
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("data_member_pointer_place result must be a place");
                break;
            }

            TypeRef base_object = place_object_ref(base);
            TypeRef member_class = member_pointer_class_ref(pointer);
            if (resolved_type(base_object.type) !=
                resolved_type(member_class.type)) {
                fail("data_member_pointer_place base type must match member pointer class");
            }

            TypeRef expected = member_pointer_member_ref(pointer);
            if (expected.memory_space == MemorySpace::Default &&
                base_object.memory_space != MemorySpace::Default) {
                expected.memory_space = base_object.memory_space;
            }
            expected.qualifiers |= base_object.qualifiers & (QualConst | QualVolatile);
            if (place_object_ref(instruction.result_type) != expected) {
                fail("data_member_pointer_place result must match member type");
            }
            break;
        }
        case InstKind::MemberFunctionPointerCallee: {
            if (ops.size() != 2) {
                fail("member_function_pointer_callee expects object and member pointer operands");
                break;
            }
            TypeId object_pointer = resolved_type(operand_result_type(value_at(0)));
            TypeId pointer = resolved_type(operand_result_type(value_at(1)));
            if (!valid(object_pointer) || type(object_pointer).kind != TypeKind::Pointer) {
                fail("member_function_pointer_callee object operand must be a pointer");
                break;
            }
            if (!valid(pointer) || type(pointer).kind != TypeKind::MemberPointer ||
                !member_pointer_points_to_function(pointer)) {
                fail("member_function_pointer_callee operand must be a member function pointer");
                break;
            }
            TypeId result = resolved_type(instruction.result_type);
            if (!valid(result) || type(result).kind != TypeKind::Pointer) {
                fail("member_function_pointer_callee result must be a function pointer");
                break;
            }
            TypeId pointee = resolved_type(pointer_pointee_type(result));
            if (!valid(pointee) || type(pointee).kind != TypeKind::Function) {
                fail("member_function_pointer_callee result must point to a function");
            }
            break;
        }
        case InstKind::MemberFunctionPointerThis: {
            if (ops.size() != 2) {
                fail("member_function_pointer_this expects object and member pointer operands");
                break;
            }
            TypeId object_pointer = resolved_type(operand_result_type(value_at(0)));
            TypeId pointer = resolved_type(operand_result_type(value_at(1)));
            if (!valid(object_pointer) || type(object_pointer).kind != TypeKind::Pointer) {
                fail("member_function_pointer_this object operand must be a pointer");
                break;
            }
            if (!valid(pointer) || type(pointer).kind != TypeKind::MemberPointer ||
                !member_pointer_points_to_function(pointer)) {
                fail("member_function_pointer_this operand must be a member function pointer");
                break;
            }
            TypeId result = resolved_type(instruction.result_type);
            if (!valid(result) || type(result).kind != TypeKind::Pointer) {
                fail("member_function_pointer_this result must be a pointer");
                break;
            }
            TypeId member_class =
                resolved_type(member_pointer_class_ref(pointer).type);
            if (resolved_type(pointer_pointee_type(object_pointer)) != member_class ||
                resolved_type(pointer_pointee_type(result)) != member_class) {
                fail("member_function_pointer_this object/result must point to the member pointer class");
            }
            break;
        }
        case InstKind::ArrayElementPlace: {
            if (ops.size() != 2) {
                fail("array_element_place expects base and index operands");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("array_element_place result must be a place");
                break;
            }

            TypeRef expected_element;
            TypeId base_type = operand_result_type(value_at(0));
            if (valid(base_type) && type(base_type).kind == TypeKind::Pointer) {
                expected_element = pointer_pointee_ref(base_type);
            } else if (valid(base_type) && type(base_type).kind == TypeKind::Place) {
                TypeRef object_type = place_object_ref(base_type);
                if (!valid(object_type.type) || type(object_type.type).kind != TypeKind::Array) {
                    fail("array_element_place place base must name array storage");
                    break;
                }
                expected_element = array_element_ref(object_type.type);

                expected_element.qualifiers = static_cast<uint8_t>(
                    expected_element.qualifiers | object_type.qualifiers);
                if (expected_element.memory_space == MemorySpace::Default &&
                    object_type.memory_space != MemorySpace::Default) {
                    expected_element.memory_space = object_type.memory_space;
                }
            } else {
                fail("array_element_place base must be pointer or place<array>");
                break;
            }

            TypeId index_type = operand_result_type(value_at(1));
            if (!valid(index_type)) {
                fail("array_element_place index must produce a value");
            } else if (type(index_type).kind == TypeKind::Place) {
                fail("array_element_place index must not be a place");
            }
            if (place_object_ref(instruction.result_type) != expected_element) {
                fail("array_element_place result must match element type");
            }
            break;
        }
        case InstKind::VectorElementPlace: {
            if (ops.size() != 2) {
                fail("vector_element_place expects base and index operands");
                break;
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("vector_element_place result must be a place");
                break;
            }

            TypeId base_type = operand_result_type(value_at(0));
            if (!valid(base_type) || type(base_type).kind != TypeKind::Place) {
                fail("vector_element_place base must be a vector place");
                break;
            }
            TypeRef object_type = place_object_ref(base_type);
            if (!valid(object_type.type) || type(object_type.type).kind != TypeKind::Vector) {
                fail("vector_element_place base must name vector storage");
                break;
            }
            TypeRef expected_element = vector_element_ref(object_type.type);

            expected_element.qualifiers = static_cast<uint8_t>(
                expected_element.qualifiers | object_type.qualifiers);
            if (expected_element.memory_space == MemorySpace::Default &&
                object_type.memory_space != MemorySpace::Default) {
                expected_element.memory_space = object_type.memory_space;
            }
            TypeId index_type = operand_result_type(value_at(1));
            if (!valid(index_type)) {
                fail("vector_element_place index must produce a value");
            } else if (type(index_type).kind == TypeKind::Place) {
                fail("vector_element_place index must not be a place");
            }
            if (place_object_ref(instruction.result_type) != expected_element) {
                fail("vector_element_place result must match vector element type");
            }
            break;
        }
        case InstKind::VectorExtract: {
            if (ops.size() != 2) {
                fail("vector_extract expects vector and index operands");
                break;
            }
            TypeId vector_type = operand_result_type(value_at(0));
            if (!valid(vector_type) || type(vector_type).kind != TypeKind::Vector) {
                fail("vector_extract base must be a vector value");
                break;
            }
            TypeId index_type = operand_result_type(value_at(1));
            if (!valid(index_type)) {
                fail("vector_extract index must produce a value");
            } else if (type(index_type).kind == TypeKind::Place) {
                fail("vector_extract index must not be a place");
            }
            if (instruction.result_type != vector_element_type(vector_type)) {
                fail("vector_extract result must match vector element type");
            }
            break;
        }
        case InstKind::SizeofType:
        case InstKind::AlignofType: {
            TypeRef queried = type_at(0);
            if (!queried.type.valid() || !valid(queried.type)) {
                fail("type query operand must name a valid type");
            }
            break;
        }
        case InstKind::Cast: {
            if (!std::holds_alternative<CastPayload>(data)) {
                fail("cast payload must carry cast metadata");
            }
            TypeRef target = type_at(0);
            if (!target.type.valid() || !valid(target.type)) {
                fail("cast target operand must name a valid type");
                break;
            }
            if (target.type != instruction.result_type) {
                fail("cast target operand must match instruction result type");
            }
            break;
        }
        case InstKind::VaStart:
        case InstKind::VaEnd: {
            TypeId place = operand_result_type(value_at(0));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail(std::string(inst_mnemonic(instruction.kind)) +
                     " operand must be a place");
            }
            if (!is_void_type(instruction.result_type)) {
                fail(std::string(inst_mnemonic(instruction.kind)) +
                     " result must be void");
            }
            break;
        }
        case InstKind::VaArg: {
            TypeRef target = type_at(0);
            if (!target.type.valid() || !valid(target.type)) {
                fail("va_arg target operand must name a valid type");
                break;
            }
            if (target.type != instruction.result_type) {
                fail("va_arg target operand must match instruction result type");
            }
            TypeId place = operand_result_type(value_at(1));
            if (!valid(place) || type(place).kind != TypeKind::Place) {
                fail("va_arg list operand must be a place");
            }
            break;
        }
        case InstKind::VaCopy: {
            TypeId dest = operand_result_type(value_at(0));
            TypeId src = operand_result_type(value_at(1));
            if (!valid(dest) || type(dest).kind != TypeKind::Place ||
                !valid(src) || type(src).kind != TypeKind::Place) {
                fail("va_copy operands must be places");
            }
            if (!is_void_type(instruction.result_type)) {
                fail("va_copy result must be void");
            }
            break;
        }
        case InstKind::BuiltinCall: {
            const auto* builtin = std::get_if<BuiltinCallPayload>(&data);
            if (!builtin) {
                fail("builtin_call payload must carry builtin metadata");
                break;
            }
            if (!is_supported_builtin_kind(builtin->kind)) {
                fail("builtin_call payload names an unsupported builtin");
            }
            if (!valid(instruction.result_type)) {
                fail("builtin_call must produce a typed result");
            }
            if (builtin->type_operand.type.valid()) {
                check_descriptor_type(builtin->type_operand, "builtin type operand");
            }
            if (builtin->kind == BuiltinKind::BIT_CAST) {
                if (instruction.operands.count != 1) {
                    fail("bit_cast builtin must carry one value operand");
                    break;
                }
                TypeId source_type = operand_result_type(value_at(0));
                std::optional<TypeSizeAlign> source_layout =
                    size_align_of_type(*this, source_type);
                std::optional<TypeSizeAlign> target_layout =
                    size_align_of_type(*this, instruction.result_type);
                if (!builtin->type_operand.type.valid()) {
                    fail("bit_cast builtin must retain its destination type operand");
                }
                if (!source_layout || !target_layout ||
                    source_layout->size_bytes != target_layout->size_bytes) {
                    fail("bit_cast builtin requires equally sized complete types");
                }
            }
            if (builtin->kind == BuiltinKind::ASSUME_ALIGNED) {
                if (instruction.operands.count < 1 ||
                    instruction.operands.count > 2) {
                    fail("assume_aligned builtin must carry a pointer and optional offset");
                    break;
                }
                TypeId pointer_type = operand_result_type(value_at(0));
                if (!valid(pointer_type) ||
                    type(pointer_type).kind != TypeKind::Pointer) {
                    fail("assume_aligned first operand must be a pointer");
                }
                TypeId result_type = resolved_type(instruction.result_type);
                if (!valid(result_type) ||
                    type(result_type).kind != TypeKind::Pointer ||
                    !is_void_type(pointer_pointee_ref(result_type).type)) {
                    fail("assume_aligned result must be void pointer");
                }
                if (instruction.operands.count == 2) {
                    TypeId offset_type = operand_result_type(value_at(1));
                    OperatorValueDomain offset_domain =
                        operator_value_domain(type_ref(offset_type));
                    if (offset_domain !=
                            OperatorValueDomain::SignedInteger &&
                        offset_domain !=
                            OperatorValueDomain::UnsignedInteger) {
                        fail("assume_aligned offset must be an integer");
                    }
                }
                if (builtin->integer_operands.size() != 1) {
                    fail("assume_aligned must retain one alignment operand");
                } else {
                    int64_t alignment = builtin->integer_operands.front();
                    if (alignment <= 0 ||
                        (static_cast<uint64_t>(alignment) &
                         (static_cast<uint64_t>(alignment) - 1)) != 0) {
                        fail("assume_aligned alignment must be a positive power of two");
                    }
                }
            }
            break;
        }
        case InstKind::CoroBegin: {
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Pointer) {
                fail("coro_begin must produce a pointer result");
            }
            break;
        }
        case InstKind::CoroFrameSize:
        case InstKind::CoroFrameAlign:
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Builtin) {
                fail("coroutine frame size/align must produce an integer "
                     "result");
            }
            break;
        case InstKind::CoroPromisePlace:
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("coro_promise_place must produce a place result");
            }
            break;
        case InstKind::CoroSave: {
            const auto* save = std::get_if<CoroSuspendPayload>(&data);
            if (!save) {
                fail("coro_save payload must carry suspend metadata");
            }
            break;
        }
        case InstKind::CoroTransfer: {
            TypeId frame_type = operand_result_type(value_at(0));
            if (!valid(frame_type) ||
                type(frame_type).kind != TypeKind::Pointer) {
                fail("coro_transfer operand must be a frame pointer");
            }
            break;
        }
        case InstKind::ObjCMessageSend: {
            const auto* send = std::get_if<ObjCMessageSendPayload>(&data);
            if (!send || !send->selector.valid()) {
                fail("objc_msg_send payload must carry a selector");
                break;
            }
            if ((send->receiver_kind == ObjCReceiverKind::Instance ||
                 send->receiver_kind == ObjCReceiverKind::Super) &&
                ops.empty()) {
                fail("objc_msg_send with an instance or super receiver must "
                     "carry the receiver operand");
            }
            break;
        }
        case InstKind::ObjCIvarAddr: {
            if (ops.size() == 2 && ops[1].kind == OperandKind::Entity) {
                const auto* ivar = std::get_if<EntityId>(&ops[1].data);
                if (!ivar || !valid(*ivar) ||
                    entity(*ivar).kind != EntityKind::ObjCIvar) {
                    fail("objc_ivar_addr entity operand must be an ObjCIvar");
                }
            }
            if (!valid(instruction.result_type) ||
                type(instruction.result_type).kind != TypeKind::Place) {
                fail("objc_ivar_addr must produce a place result");
            }
            break;
        }
        case InstKind::ObjCSelectorLiteral: {
            const auto* literal = std::get_if<ObjCSelectorLiteralPayload>(&data);
            if (!literal || !literal->selector.valid()) {
                fail("objc_selector_literal payload must carry a selector");
            }
            break;
        }
        case InstKind::ObjCArcOp: {
            if (!std::get_if<ObjCArcOpPayload>(&data)) {
                fail("objc_arc_op payload must carry the operation kind");
            }
            break;
        }
        case InstKind::ObjCStringLiteral:
            if (!std::get_if<LiteralPayload>(&data)) {
                fail("objc_string_literal payload must carry the string bytes");
            }
            break;
        case InstKind::ReflectValue: {
            const auto* reflect = std::get_if<ReflectPayload>(&data);
            if (!reflect) {
                fail("reflect_value payload must carry a handle kind");
                break;
            }
            if (reflect->kind == MetaInfoKind::Type) {
                if (ops.size() != 1 || ops[0].kind != OperandKind::Type) {
                    fail("reflect_value of a type must carry one type operand");
                }
            } else if (ops.size() != 1 ||
                       ops[0].kind != OperandKind::Entity) {
                fail("reflect_value must carry one entity operand");
            }
            break;
        }
        case InstKind::InlineAsm:
            if (const auto* asm_ref = std::get_if<InlineAsmPayloadRef>(&data);
                asm_ref && valid(asm_ref->payload)) {
                const InlineAsmPayload& asm_payload = inline_asm_payload(asm_ref->payload);
                size_t expected_operands =
                    asm_payload.outputs.size() + asm_payload.inputs.size();
                if (ops.size() != expected_operands) {
                    fail("inline_asm operand count must match asm metadata");
                    break;
                }
                for (size_t index = 0; index < asm_payload.outputs.size(); ++index) {
                    TypeId output_type = operand_result_type(value_at(index));
                    if (!valid(output_type) || type(output_type).kind != TypeKind::Place) {
                        fail("inline_asm output operand must be a place");
                    }
                }
                for (const InlineAsmOperandPayload& operand : asm_payload.outputs) {
                    if (!operand.is_output) {
                        fail("inline_asm output metadata must be marked output");
                    }
                }
                for (const InlineAsmOperandPayload& operand : asm_payload.inputs) {
                    if (operand.is_output) {
                        fail("inline_asm input metadata must not be marked output");
                    }
                }
                if (asm_payload.is_goto) {
                    fail("inline_asm instruction must not be marked asm goto");
                }
            } else {
                fail("inline_asm payload must carry asm metadata");
            }
            if (instruction.result_type.valid()) {
                fail("inline_asm statement must not produce a value");
            }
            break;
        case InstKind::Error:
            if (!std::holds_alternative<ErrorPayload>(data)) {
                fail("error payload must carry error metadata");
            }
            break;
        case InstKind::DependentRegion:
            if (!std::holds_alternative<DependentRegionPayload>(data)) {
                fail("dependent_region payload must carry hole metadata");
            }
            if (instruction.result_type.valid()) {
                fail("dependent_region must not produce a value");
            }
            break;
        default:
            break;
    }
    return ok;
}

bool File::verify_function(const Function& fn,
                           FunctionId function_id,
                           std::ostream* err) const {
    bool ok = true;
    auto fail = [&](const std::string& message) {
        ok = false;
        if (err) {
            *err << "CIR verification failed for function #" << function_id.index
                 << ": " << message << '\n';
        }
    };

    if (!valid(fn.entity)) {
        fail("function entity is invalid");
    } else if (entity(fn.entity).is_deleted) {
        fail("deleted function has an executable body");
    }
    if (!valid(fn.type)) fail("function type is invalid");
    if (!valid(fn.result_type)) fail("function result type is invalid");
    if (!valid(fn.entry_block)) fail("entry block is invalid");

    for (const FunctionParameter& param : fn.parameters) {
        if (!valid(param.entity)) {
            fail("parameter entity is invalid");
        }
        if (!valid(param.value.inst)) {
            fail("parameter instruction is invalid");
            continue;
        }
        const Inst& param_inst = inst(param.value.inst);
        if (param_inst.kind != InstKind::Param) {
            fail("function parameter instruction is not Param");
            continue;
        }
        std::vector<Operand> param_operands = operands(param_inst.operands);
        const auto* param_entity =
            param_operands.empty() ? nullptr : std::get_if<EntityId>(&param_operands[0].data);
        if (!param_entity || *param_entity != param.entity) {
            fail("function parameter entity must match Param instruction operand");
        }
    }

    const CoroutineFact* coro_fact = coroutine_fact_for_function(fn.entity);
    bool coro_pre_split = coro_fact != nullptr && !coroutines_lowered_;
    size_t coro_begin_count = 0;

    std::unordered_map<std::string, BlockId> block_names;
    for (BlockId block_id : fn.blocks) {
        if (!valid(block_id)) {
            fail("function references invalid block");
            continue;
        }
        const Block& b = block(block_id);
        if (b.name.valid()) {
            const std::string& block_name = name(b.name);
            auto [found, inserted] = block_names.emplace(block_name, block_id);
            if (!inserted) {
                fail("duplicate block name '" + block_name + "' in blocks #" +
                     std::to_string(found->second.index) + " and #" +
                     std::to_string(block_id.index));
            }
        }
        if (b.terminator.kind == TerminatorKind::Invalid) {
            fail("block #" + std::to_string(block_id.index) + " has no terminator");
        }
        for (InstId param : b.parameters) {
            if (!valid(param)) fail("block parameter is invalid");
        }
        for (InstId instruction : b.instructions) {
            if (!valid(instruction)) {
                fail("block instruction is invalid");
                continue;
            }
            switch (inst(instruction).kind) {
                case InstKind::CoroBegin:
                    ++coro_begin_count;
                    [[fallthrough]];
                case InstKind::CoroFrameSize:
                case InstKind::CoroFrameAlign:
                case InstKind::CoroPromisePlace:
                case InstKind::CoroSave:
                case InstKind::CoroTransfer:
                    if (!coro_pre_split) {
                        fail("coroutine instruction outside a pre-split "
                             "coroutine function");
                    }
                    break;
                default:
                    break;
            }
            ok = verify_inst(instruction, err) && ok;
        }

        std::vector<Operand> term_ops = operands(b.terminator.operands);
        if (b.terminator.kind != TerminatorKind::Throw) {
            for (const Operand& operand : term_ops) {
                const auto* value = std::get_if<ValueRef>(&operand.data);
                if (operand.kind != OperandKind::Value || !value || !valid(value->inst)) {
                    fail("terminator operand must be a valid value");
                }
            }
        }
        auto term_value_at = [&](size_t index) -> ValueRef {
            if (index >= term_ops.size()) return {};
            const auto* value = std::get_if<ValueRef>(&term_ops[index].data);
            return value ? *value : ValueRef{};
        };
        for (size_t i = 0; i < b.instructions.size(); ++i) {
            if (!valid(b.instructions[i])) {
                continue;
            }
            const Inst& instruction = inst(b.instructions[i]);
            const auto* call_payload =
                std::get_if<CallPayload>(&payload(instruction.payload_index));
            if (!call_payload || !call_payload->must_tail) {
                continue;
            }
            if (i + 1 != b.instructions.size() ||
                b.terminator.kind != TerminatorKind::Return ||
                !term_ops.empty()) {
                fail("a must-tail call must be the block's last instruction "
                     "before an operandless return");
            }
        }
        switch (b.terminator.kind) {
            case TerminatorKind::Return:
                if (is_void_type(fn.result_type)) {
                    if (!term_ops.empty()) fail("void return has operands");
                } else {
                    if (term_ops.size() != 1) {
                        fail("non-void return must have one operand");
                    } else if (operand_result_type(term_value_at(0)) !=
                               fn.result_type) {
                        TypeId op_type = operand_result_type(term_value_at(0));
                        TypeId op_resolved = resolved_type(op_type);
                        bool dependent_pattern_return =
                            valid(fn.entity) &&
                            entity(fn.entity).is_template_pattern &&
                            valid(op_resolved) &&
                            type(op_resolved).kind == TypeKind::Dependent;
                        if (dependent_pattern_return) {

                            break;
                        }
                        auto rec = [&](TypeId t) {
                            EntityId e = record_entity(t);
                            std::string s = "#" + std::to_string(t.index);
                            if (e.valid() && valid(e)) {
                                s += " entity#" + std::to_string(e.index);
                                s += entity(e).is_template_pattern
                                    ? " pattern" : " concrete";
                            }
                            return s;
                        };
                        fail("return operand type does not match function result"
                             " (operand " + rec(op_type) +
                             " vs result " + rec(fn.result_type) + ")");
                    }
                }
                break;
            case TerminatorKind::Branch:
                if (!valid(b.terminator.target)) {
                    fail("branch target is invalid");
                } else if (term_ops.size() != block(b.terminator.target).parameters.size()) {
                    fail("branch target argument count mismatch");
                }
                break;
            case TerminatorKind::CondBranch:
                if (term_ops.empty()) {
                    fail("conditional branch is missing condition operand");
                }
                if (!valid(b.terminator.target) || !valid(b.terminator.false_target)) {
                    fail("conditional branch target is invalid");
                }
                break;
            case TerminatorKind::Switch: {
                if (term_ops.size() != 1) {
                    fail("switch terminator must have one condition operand");
                }
                if (!valid(b.terminator.target)) {
                    fail("switch default target is invalid");
                    break;
                }
                if (!block(b.terminator.target).parameters.empty()) {
                    fail("switch default target must not have block parameters");
                }
                const InstPayload& term_payload = payload(b.terminator.payload_index);
                const auto* switch_payload =
                    std::get_if<SwitchTerminatorPayload>(&term_payload);
                if (!switch_payload) {
                    fail("switch terminator payload must carry switch metadata");
                    break;
                }
                if (!switch_payload->condition_type.type.valid()) {
                    fail("switch condition type is missing");
                } else if (!valid(switch_payload->condition_type.type)) {
                    fail("switch condition type is invalid");
                } else if (term_ops.size() == 1 &&
                           operand_result_type(term_value_at(0)) !=
                               switch_payload->condition_type.type) {
                    fail("switch condition type does not match condition value");
                }
                for (size_t case_index = 0;
                     case_index < switch_payload->cases.size();
                     ++case_index) {
                    const SwitchCaseRange& case_range = switch_payload->cases[case_index];
                    if (case_range.high < case_range.low) {
                        fail("switch case range is empty");
                    }
                    if (!valid(case_range.target)) {
                        fail("switch case target is invalid");
                    } else if (!block(case_range.target).parameters.empty()) {
                        fail("switch case target must not have block parameters");
                    }
                    for (size_t prior_index = 0; prior_index < case_index; ++prior_index) {
                        const SwitchCaseRange& prior = switch_payload->cases[prior_index];
                        if (case_range.low <= prior.high && prior.low <= case_range.high) {
                            fail("switch case ranges overlap");
                            break;
                        }
                    }
                }
                break;
            }
            case TerminatorKind::IndirectBranch:
                if (term_ops.size() != 1) {
                    fail("indirect branch must have one target operand");
                } else {
                    TypeId target_type = operand_result_type(term_value_at(0));
                    if (!valid(target_type) || type(target_type).kind != TypeKind::Pointer) {
                        fail("indirect branch target must have pointer type");
                    }
                }
                break;
            case TerminatorKind::AsmGoto: {
                if (!valid(b.terminator.target)) {
                    fail("asm goto fallthrough target is invalid");
                    break;
                }
                const InstPayload& term_payload = payload(b.terminator.payload_index);
                const auto* asm_ref = std::get_if<InlineAsmPayloadRef>(&term_payload);
                if (!asm_ref || !valid(asm_ref->payload)) {
                    fail("asm goto terminator payload must carry asm metadata");
                    break;
                }
                const InlineAsmPayload& asm_payload = inline_asm_payload(asm_ref->payload);
                if (!asm_payload.is_goto) {
                    fail("asm goto payload must be marked asm goto");
                }
                if (asm_payload.goto_labels.size() != asm_payload.goto_targets.size()) {
                    fail("asm goto label metadata count mismatch");
                }
                for (BlockId target : asm_payload.goto_targets) {
                    if (!valid(target)) {
                        fail("asm goto label target is invalid");
                    }
                }
                size_t expected_operands =
                    asm_payload.outputs.size() + asm_payload.inputs.size();
                if (term_ops.size() != expected_operands) {
                    fail("asm goto operand count must match asm metadata");
                    break;
                }
                for (size_t index = 0; index < asm_payload.outputs.size(); ++index) {
                    TypeId output_type = operand_result_type(term_value_at(index));
                    if (!valid(output_type) || type(output_type).kind != TypeKind::Place) {
                        fail("asm goto output operand must be a place");
                    }
                }
                break;
            }
            case TerminatorKind::Throw: {

                if (term_ops.empty() ||
                    term_ops[0].kind != OperandKind::Value) {
                    fail("throw must carry the exception object value");
                    break;
                }
                if (term_ops.size() < 2 ||
                    term_ops[1].kind != OperandKind::Entity) {
                    fail("throw must carry a typeinfo entity operand");
                    break;
                }
                if (term_ops.size() > 3) {
                    fail("throw has too many operands");
                }
                break;
            }
            case TerminatorKind::Rethrow:
                if (!term_ops.empty()) {
                    fail("rethrow takes no operands");
                }
                break;
            case TerminatorKind::Resume:
                if (term_ops.size() != 2) {
                    fail("resume must carry exception pointer and selector");
                }
                break;
            case TerminatorKind::CoroSuspend: {
                if (!coro_pre_split) {
                    fail("coro_suspend outside a pre-split coroutine "
                         "function");
                    break;
                }
                if (!term_ops.empty()) {
                    fail("coro_suspend takes no operands");
                }
                if (!valid(b.terminator.target) ||
                    !valid(b.terminator.false_target)) {
                    fail("coro_suspend must carry resume and destroy "
                         "targets");
                    break;
                }
                if (!block(b.terminator.target).parameters.empty() ||
                    !block(b.terminator.false_target).parameters.empty()) {
                    fail("coro_suspend successors must not have block "
                         "parameters");
                }
                const auto* coro_payload = std::get_if<CoroSuspendPayload>(
                    &payload(b.terminator.payload_index));
                if (!coro_payload) {
                    fail("coro_suspend payload must carry suspend metadata");
                }
                break;
            }
            case TerminatorKind::CoroEnd:
                if (!coro_pre_split) {
                    fail("coro_end outside a pre-split coroutine function");
                    break;
                }
                if (!term_ops.empty()) {
                    fail("coro_end takes no operands");
                }
                break;
            case TerminatorKind::Unreachable:
            case TerminatorKind::Invalid:
                break;
        }
    }

    if (coro_pre_split && coro_begin_count != 1) {
        fail("pre-split coroutine function must contain exactly one "
             "coro_begin");
    }

    auto first_body_inst = [&](const Block& candidate) -> const Inst* {
        for (InstId inst_id : candidate.instructions) {
            if (!valid(inst_id)) continue;
            const Inst& record = inst(inst_id);
            if (record.kind == InstKind::Param) continue;
            return &record;
        }
        return nullptr;
    };
    auto is_pad_block = [&](BlockId candidate) -> bool {
        if (!valid(candidate)) return false;
        const Inst* first = first_body_inst(block(candidate));
        return first && first->kind == InstKind::EhLandingPad;
    };
    for (BlockId block_id : fn.blocks) {
        if (!valid(block_id)) continue;
        const Block& b = block(block_id);
        const Inst* previous = nullptr;
        bool seen_body_inst = false;
        for (InstId inst_id : b.instructions) {
            if (!valid(inst_id)) continue;
            const Inst& record = inst(inst_id);
            if (record.kind == InstKind::Param) continue;
            if (record.kind == InstKind::EhLandingPad && seen_body_inst) {
                fail("eh_landing_pad must be the first instruction of its block");
            }
            if (record.kind == InstKind::EhLandingPad) {
                const auto* pad = std::get_if<EhLandingPadPayload>(
                    &payload(record.payload_index));
                if (!pad) {
                    fail("eh_landing_pad must carry landing-pad metadata");
                } else if (!pad->is_cleanup && !pad->has_catch_all &&
                           pad->clause_typeinfos.empty()) {
                    fail("eh_landing_pad must have a clause or be a cleanup");
                }
            }
            if (record.kind == InstKind::EhSelector &&
                (!previous || previous->kind != InstKind::EhLandingPad)) {
                fail("eh_selector must immediately follow its landing pad");
            }
            previous = &record;
            seen_body_inst = true;
        }
        if (b.unwind_target.valid()) {
            if (!valid(b.unwind_target)) {
                fail("block unwind target is invalid");
            } else if (!is_pad_block(b.unwind_target)) {
                fail("block unwind target must begin with eh_landing_pad");
            }
        }
        auto check_normal_edge = [&](BlockId target) {
            if (valid(target) && is_pad_block(target)) {
                fail("normal control-flow edge targets a landing-pad block");
            }
        };
        switch (b.terminator.kind) {
            case TerminatorKind::Branch:
                check_normal_edge(b.terminator.target);
                break;
            case TerminatorKind::CondBranch:
                check_normal_edge(b.terminator.target);
                check_normal_edge(b.terminator.false_target);
                break;
            case TerminatorKind::Switch: {
                check_normal_edge(b.terminator.target);
                if (const auto* switch_payload = std::get_if<SwitchTerminatorPayload>(
                        &payload(b.terminator.payload_index))) {
                    for (const SwitchCaseRange& case_range : switch_payload->cases) {
                        check_normal_edge(case_range.target);
                    }
                }
                break;
            }
            default:
                break;
        }
    }

    return ok;
}

bool File::verify(std::ostream* err) const {
    bool ok = true;
    auto fail = [&](const std::string& message) {
        ok = false;
        if (err) {
            *err << "CIR verification failed: " << message << '\n';
        }
    };

    for (uint32_t i = 1; i < types_.size(); ++i) {
        const Type& t = types_[i];
        std::string label = "type #" + std::to_string(i);
        if (t.payload_index == 0 || t.payload_index >= type_payloads_.size()) {
            fail(label + " has invalid payload index");
            continue;
        }
        if (t.debug_name.valid() && !valid(t.debug_name)) {
            fail(label + " has invalid debug name");
        }
        if (t.canonical.valid() && !valid(t.canonical)) {
            fail(label + " has invalid canonical type");
        }
        if (t.desugared.valid() && !valid(t.desugared)) {
            fail(label + " has invalid desugared type");
        }
        if (t.resolved.valid() && !valid(t.resolved)) {
            fail(label + " has invalid resolved type");
        }

        const TypePayload& payload = type_payload(t.payload_index);
        if (type_payload_kind(payload) != t.kind) {
            fail(label + " kind does not match payload");
            continue;
        }

        auto check_type_ref = [&](TypeRef ref, std::string_view field) {
            if (ref.type.valid() && !valid(ref.type)) {
                fail(label + " has invalid " + std::string(field));
            }
        };
        auto check_entity = [&](EntityId entity, std::string_view field) {
            if (entity.valid() && !valid(entity)) {
                fail(label + " has invalid " + std::string(field));
            }
        };
        auto check_name = [&](NameId name_id, std::string_view field) {
            if (name_id.valid() && !valid(name_id)) {
                fail(label + " has invalid " + std::string(field));
            }
        };
        auto check_inst = [&](InstId inst_id, std::string_view field) {
            if (inst_id.valid() && !valid(inst_id)) {
                fail(label + " has invalid " + std::string(field));
            }
        };
        std::function<void(const TemplateArgument&)> check_template_argument;
        std::function<void(const TemplateValueExpression&, std::string_view)>
            check_template_value_expression;
        check_template_value_expression =
            [&](const TemplateValueExpression& expression,
                std::string_view field) {
                if (!expression.valid()) {
                    return;
                }
                if (!expression.canonical_id.valid() ||
                    !valid(expression.canonical_id)) {
                    fail(label + " has non-canonical " +
                         std::string(field));
                }
                for (size_t node_index = 0;
                     node_index < expression.nodes.size(); ++node_index) {
                    const TemplateValueExprNode& node =
                        expression.nodes[node_index];
                    auto check_child = [&](uint32_t child,
                                           std::string_view child_field) {
                        if (child != TemplateValueExprNoNode &&
                            child >= expression.nodes.size()) {
                            fail(label + " has " + std::string(field) +
                                 " with invalid " +
                                 std::string(child_field));
                        }
                    };
                    check_child(node.lhs, "lhs");
                    check_child(node.rhs, "rhs");
                    check_child(node.third, "third operand");
                    for (uint32_t operand : node.operands) {
                        check_child(operand, "ordered operand");
                    }
                    if (node.type.valid() && !valid(node.type)) {
                        fail(label + " has " + std::string(field) +
                             " with invalid operand type");
                    }
                    check_type_ref(node.result_type,
                                   "value expression result type");
                    check_type_ref(node.qualifier_type,
                                   "value expression qualifier type");
                    check_entity(node.entity,
                                 "value expression entity");
                    check_name(node.name, "value expression name");
                    if (node.kind == TemplateValueExprKind::Integer) {
                        if (!node.integer_value.canonical()) {
                            fail(label + " has " + std::string(field) +
                                 " with invalid integer payload");
                        } else {
                            TypeId result_type =
                                resolved_type(node.result_type.type);
                            if (valid(result_type) &&
                                is_integer_like_type(*this, result_type)) {
                                IntegerTypeShape shape =
                                    integer_shape_for_type(*this, result_type);
                                if (node.integer_value.bit_width !=
                                        shape.bit_width ||
                                    node.integer_value.is_unsigned !=
                                        shape.is_unsigned) {
                                    fail(label + " has " +
                                         std::string(field) +
                                         " with integer payload shape that "
                                         "does not match its result type");
                                }
                            }
                        }
                    }
                    for (const TemplateValuePackReference& reference :
                         node.pack_references) {
                        check_entity(reference.declaration,
                                     "value expression pack declaration");
                        check_entity(reference.owner,
                                     "value expression pack owner");
                        if (reference.parameter_type.valid() &&
                            !valid(reference.parameter_type)) {
                            fail(label + " has " + std::string(field) +
                                 " with an invalid pack parameter type");
                        }
                        check_name(reference.name,
                                   "value expression pack name");
                        if (static_cast<uint32_t>(reference.kind) >
                            static_cast<uint32_t>(
                                TemplateValuePackKind::Template)) {
                            fail(label + " has " + std::string(field) +
                                 " with an unknown pack kind");
                        }
                        if (reference.index ==
                            TemplateValueExprNoParameter) {
                            fail(label + " has " + std::string(field) +
                                 " with an unindexed pack reference");
                        }
                    }
                    for (const TemplateArgument& template_argument :
                         node.template_arguments.values()) {
                        check_template_argument(template_argument);
                    }
                    if (node.kind == TemplateValueExprKind::ConceptId) {
                        bool has_target =
                            node.entity.valid() ||
                            node.parameter_index !=
                                TemplateValueExprNoParameter ||
                            node.name.valid() ||
                            node.qualifier_type.type.valid();
                        TypeId result_type =
                            resolved_type(node.result_type.type);
                        if (!has_target ||
                            result_type != builtin_type(
                                BuiltinTypeKind::Bool) ||
                            node.lhs != TemplateValueExprNoNode ||
                            node.rhs != TemplateValueExprNoNode ||
                            node.third != TemplateValueExprNoNode ||
                            !node.operands.empty() ||
                            !node.pack_references.empty()) {
                            fail(label + " has malformed concept-id value "
                                 "expression");
                        }
                    } else if (!node.template_arguments.empty()) {
                        bool is_explicit_argument_descriptor =
                            node.kind ==
                                TemplateValueExprKind::TypeOperand &&
                            node.template_arguments.size() == 1 &&
                            node.value >= static_cast<int64_t>(
                                TemplateArgumentKind::Type) &&
                            node.value <= static_cast<int64_t>(
                                TemplateArgumentKind::Template) &&
                            static_cast<int64_t>(
                                node.template_arguments.values()
                                    .front()
                                    .kind) == node.value &&
                            node.third == TemplateValueExprNoNode &&
                            node.operands.empty();
                        if (!is_explicit_argument_descriptor) {
                            fail(label + " has value expression with "
                                 "template arguments outside a concept-id "
                                 "or explicit-argument descriptor");
                        }
                    }
                    if (node.kind == TemplateValueExprKind::Noexcept &&
                        node.lhs == TemplateValueExprNoNode) {
                        fail(label + " has noexcept value expression "
                             "without an operand");
                    }
                    if (node.kind == TemplateValueExprKind::Fold) {
                        bool binary =
                            node.fold_kind ==
                                TemplateValueFoldKind::BinaryLeft ||
                            node.fold_kind ==
                                TemplateValueFoldKind::BinaryRight;
                        bool valid_form =
                            node.fold_kind ==
                                TemplateValueFoldKind::UnaryLeft ||
                            node.fold_kind ==
                                TemplateValueFoldKind::UnaryRight ||
                            binary;
                        if (!valid_form ||
                            node.op == TemplateValueExprOp::None ||
                            node.lhs == TemplateValueExprNoNode ||
                            node.pack_references.empty() ||
                            (binary !=
                             (node.rhs != TemplateValueExprNoNode))) {
                            fail(label + " has malformed fold value expression");
                        }
                    }
                    if (node.kind == TemplateValueExprKind::PackIndex &&
                        node.lhs == TemplateValueExprNoNode) {
                        fail(label + " has pack-index value expression "
                             "without an index");
                    }
                    if (node.kind == TemplateValueExprKind::TypeTrait &&
                        (node.trait_kind == BuiltinTypeTraitKind::None ||
                         node.operands.empty())) {
                        fail(label + " has type-trait value expression "
                             "without semantic identity and operands");
                    }
                    if (node.kind == TemplateValueExprKind::TypeTrait) {
                        for (uint32_t operand : node.operands) {
                            if (operand < expression.nodes.size() &&
                                expression.nodes[operand].kind !=
                                    TemplateValueExprKind::TypeOperand) {
                                fail(label + " has type-trait value "
                                     "expression with a non-type operand");
                            }
                        }
                    }
                    if (node.kind == TemplateValueExprKind::TypeOperand &&
                        (static_cast<uint64_t>(node.value) &
                         static_cast<uint32_t>(
                             TemplateCalleeFlag::MemberAccess)) != 0) {
                        constexpr uint32_t known_member_flags =
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::MemberAccess) |
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::MemberArrow);
                        if (node.lhs == TemplateValueExprNoNode ||
                            !node.name.valid() ||
                            node.rhs != TemplateValueExprNoNode ||
                            node.third != TemplateValueExprNoNode ||
                            !node.operands.empty() ||
                            (static_cast<uint64_t>(node.value) &
                             ~static_cast<uint64_t>(known_member_flags)) != 0) {
                            fail(label + " has malformed member-access value "
                                 "operand");
                        }
                    }
                    if (node.kind == TemplateValueExprKind::Unary &&
                        (node.op == TemplateValueExprOp::None ||
                         node.lhs == TemplateValueExprNoNode)) {
                        fail(label + " has malformed unary value expression");
                    }
                    if (node.kind == TemplateValueExprKind::Binary &&
                        (node.op == TemplateValueExprOp::MemberPointerDot ||
                         node.op ==
                             TemplateValueExprOp::MemberPointerArrow) &&
                        (node.lhs == TemplateValueExprNoNode ||
                         node.rhs == TemplateValueExprNoNode)) {
                        fail(label + " has member-pointer value expression "
                             "without both operands");
                    }
                    if (node.kind == TemplateValueExprKind::Callee) {
                        bool expression_target =
                            node.lhs != TemplateValueExprNoNode;
                        bool named_target = node.entity.valid() ||
                            node.name.valid() || !node.semantic_key.empty();
                        if (expression_target == named_target) {
                            fail(label + " has callee value expression "
                                 "without exactly one target form");
                        }
                        if (expression_target &&
                            (node.rhs != TemplateValueExprNoNode ||
                             !node.operands.empty())) {
                            fail(label + " has expression callee with named "
                                 "lookup state");
                        }
                        if (node.rhs != TemplateValueExprNoNode &&
                            node.rhs < expression.nodes.size() &&
                            expression.nodes[node.rhs].kind !=
                                TemplateValueExprKind::TypeOperand) {
                            fail(label + " has member callee with a non-type "
                                 "base descriptor");
                        }
                        for (uint32_t candidate : node.operands) {
                            if (candidate < expression.nodes.size() &&
                                expression.nodes[candidate].kind !=
                                    TemplateValueExprKind::TypeOperand) {
                                fail(label + " has callee lookup set with a "
                                     "non-candidate descriptor");
                            }
                        }
                        constexpr uint32_t known_callee_flags =
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::QualifiedName) |
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::
                                    SuppressArgumentDependentLookup) |
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::
                                    UnresolvedUnqualifiedName) |
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::
                                    HasExplicitTemplateArguments) |
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::MemberArrow) |
                            static_cast<uint32_t>(
                                TemplateCalleeFlag::
                                    BuiltinCallDesignator);
                        if ((static_cast<uint64_t>(node.value) &
                             ~static_cast<uint64_t>(known_callee_flags)) != 0) {
                            fail(label + " has callee value expression with "
                                 "unknown flags");
                        }
                    }
                    if (node.expands_parameter_pack &&
                        node.kind != TemplateValueExprKind::TypeOperand) {
                        fail(label + " has a non-type operand marked as a "
                             "type-parameter-pack expansion");
                    }
                    if (!node.pack_references.empty() &&
                        node.kind != TemplateValueExprKind::TypeOperand &&
                        node.kind != TemplateValueExprKind::Fold &&
                        node.kind != TemplateValueExprKind::PackSize) {
                        fail(label + " has a non-type operand carrying a "
                             "pack-expansion identity");
                    }
                    if (node.kind == TemplateValueExprKind::PackSize &&
                        !node.pack_references.empty()) {
                        const TemplateValuePackReference& first =
                            node.pack_references.front();
                        if (first.kind ==
                                TemplateValuePackKind::Function ||
                            node.parameter_index != first.index ||
                            (first.declaration.valid() &&
                             node.entity != first.declaration)) {
                            fail(label + " has malformed coordinated "
                                 "pack-size identity");
                        }
                        for (size_t reference_index = 0;
                             reference_index <
                                 node.pack_references.size();
                             ++reference_index) {
                            const TemplateValuePackReference& reference =
                                node.pack_references[reference_index];
                            if (reference.kind ==
                                TemplateValuePackKind::Function) {
                                fail(label + " has function-pack identity "
                                     "on a structural pack-size node");
                            }
                            auto current =
                                node.pack_references.begin() +
                                reference_index;
                            if (std::find(
                                    node.pack_references.begin(),
                                    current,
                                    reference) != current) {
                                fail(label + " has duplicate coordinated "
                                     "pack-size identity");
                            }
                        }
                    }
                    if (node.kind == TemplateValueExprKind::Call) {
                        if (node.third == TemplateValueExprNoNode ||
                            (node.third < expression.nodes.size() &&
                             expression.nodes[node.third].kind !=
                                 TemplateValueExprKind::Callee)) {
                            fail(label + " has call value expression without "
                                 "a canonical callee");
                        }
                        if (node.entity.valid() || node.name.valid() ||
                            node.qualifier_type.type.valid() ||
                            !node.semantic_key.empty() || node.value != 0) {
                            fail(label + " has call value expression with "
                                 "non-canonical inline callee identity");
                        }
                    }
                }
            };
        check_template_argument = [&](const TemplateArgument& root) {
            std::vector<const TemplateArgument*> stack;
            stack.push_back(&root);
            while (!stack.empty()) {
                const TemplateArgument& argument = *stack.back();
                stack.pop_back();
                check_type_ref(argument.type, "template argument type");
                check_type_ref(argument.value_type, "template argument value type");
                check_type_ref(argument.generated_pack_count_type,
                               "generated template pack count type");
                check_type_ref(argument.dependent_value_qualifier,
                               "dependent template argument value qualifier");
                check_entity(argument.value_entity, "template argument value entity");
                check_entity(argument.template_entity, "template argument entity");
                if (argument.constant_state.valid() &&
                    !valid(argument.constant_state)) {
                    fail(label + " has invalid constant-state identity");
                }
                check_name(argument.dependent_value_name,
                           "dependent template argument value name");
                check_type_ref(argument.dependent_template_qualifier,
                               "dependent template argument template qualifier");
                check_name(argument.template_name, "template argument name");
                check_template_value_expression(
                    argument.dependent_value_expr,
                    "template argument value expression");
                check_template_value_expression(
                    argument.generated_pack_count_expr,
                    "generated template pack count expression");
                if (argument.generated_pack_kind !=
                        TemplateGeneratedPackKind::None &&
                    (argument.kind != TemplateArgumentKind::Value ||
                     !argument.value_type.type.valid() ||
                     !argument.generated_pack_count_type.type.valid() ||
                     !argument.generated_pack_count_expr.valid() ||
                     !argument.is_dependent)) {
                    fail(label + " has malformed generated template pack");
                }
                for (const TemplateArgument& element :
                     argument.value_elements) {
                    stack.push_back(&element);
                }
                if (argument.kind != TemplateArgumentKind::Value) {
                    continue;
                }
                TypeId value_type = resolved_type(argument.value_type.type);
                bool has_dependent_value_identity =
                    argument.is_dependent ||
                    argument.value_param_index !=
                        ArrayTypePayload::no_extent_param ||
                    argument.dependent_value_qualifier.type.valid() ||
                    argument.dependent_value_name.valid();
                switch (argument.value_kind) {
                    case TemplateValueKind::Integer:
                        if (!argument.integer_value.canonical()) {
                            fail(label +
                                 " has integer template argument with invalid payload");
                        } else if (!has_dependent_value_identity &&
                                   valid(value_type) &&
                                   is_integer_like_type(*this, value_type)) {
                            IntegerTypeShape shape =
                                integer_shape_for_type(*this, value_type);
                            if (argument.integer_value.bit_width !=
                                    shape.bit_width ||
                                argument.integer_value.is_unsigned !=
                                    shape.is_unsigned) {
                                fail(label +
                                     " has integer template argument with payload shape that does not match its type");
                            }
                        }
                        break;
                    case TemplateValueKind::Boolean:
                        if (!argument.integer_value.canonical()) {
                            fail(label +
                                 " has boolean template argument with invalid payload");
                        }
                        break;
                    case TemplateValueKind::Null:
                        if (argument.null_kind == TemplateNullKind::None) {
                            fail(label +
                                 " has null template argument without null flavor");
                        } else if (!template_type_accepts_null_kind(
                                       value_type,
                                       argument.null_kind)) {
                            fail(label +
                                 " has null template argument with incompatible type");
                        }
                        if (argument.value_entity.valid() ||
                            argument.value_byte_offset != 0) {
                            fail(label +
                                 " has null template argument with identity payload");
                        }
                        break;
                    case TemplateValueKind::MemberPointer:
                        if (template_value_kind_for_type(value_type) !=
                            TemplateValueKind::MemberPointer) {
                            fail(label +
                                 " has member pointer template argument with non-member-pointer type");
                        }
                        if (!has_dependent_value_identity &&
                            !argument.value_entity.valid()) {
                            fail(label +
                                 " has non-null member pointer template argument without a member entity");
                        }
                        break;
                    case TemplateValueKind::StructuralObject:
                        if (template_value_kind_for_type(value_type) !=
                            TemplateValueKind::StructuralObject) {
                            fail(label +
                                 " has structural object template argument with non-object type");
                        }
                        if (argument.value_byte_offset != 0) {
                            fail(label +
                                 " has structural object template argument with identity payload");
                        }
                        if (argument.value_entity.valid()) {
                            const RecordFacts* facts =
                                record_facts_for_type(value_type);
                            bool is_active_union_member = facts &&
                                facts->kind == RecordKind::Union &&
                                std::any_of(
                                    facts->fields.begin(), facts->fields.end(),
                                    [&](const RecordFieldFact& field) {
                                        return field.entity ==
                                            argument.value_entity;
                                    });
                            if (!is_active_union_member) {
                                fail(label +
                                     " has invalid union active-member identity");
                            }
                        }
                        break;
                    case TemplateValueKind::Closure: {
                        const RecordFacts* facts =
                            record_facts_for_type(value_type);
                        if (!facts || !facts->is_lambda_closure ||
                            facts->lambda_has_capture ||
                            !valid(argument.closure_identity) ||
                            facts->closure_identity !=
                                argument.closure_identity ||
                            argument.value_entity.valid() ||
                            argument.value_byte_offset != 0 ||
                            !argument.value_elements.empty()) {
                            fail(label +
                                 " has invalid closure template argument identity");
                        }
                        break;
                    }
                    default:
                        break;
                }
            }
        };

        std::visit(
            [&](const auto& data) {
                using Payload = std::decay_t<decltype(data)>;
                if constexpr (std::is_same_v<Payload, PointerTypePayload>) {
                    check_type_ref(data.pointee, "pointee type");
                } else if constexpr (std::is_same_v<Payload, BlockPointerTypePayload>) {
                    check_type_ref(data.pointee, "block pointer pointee type");
                } else if constexpr (std::is_same_v<Payload, MemberPointerTypePayload>) {
                    check_type_ref(data.class_type, "member pointer class type");
                    check_type_ref(data.member_type, "member pointer member type");
                } else if constexpr (std::is_same_v<Payload, ReferenceTypePayload>) {
                    check_type_ref(data.referred_type, "reference type");
                } else if constexpr (std::is_same_v<Payload, ArrayTypePayload>) {
                    check_type_ref(data.element_type, "array element type");
                    check_inst(data.size_expr, "array size expression");
                    check_template_value_expression(
                        data.dependent_size_expr,
                        "dependent array size expression");
                } else if constexpr (std::is_same_v<Payload, FunctionTypePayload>) {
                    check_type_ref(data.return_type, "function return type");
                    for (TypeRef param : data.parameters) {
                        check_type_ref(param, "function parameter type");
                    }
                    if (data.exception_spec.kind ==
                            FunctionExceptionSpecKind::Dependent &&
                        !data.exception_spec.predicate.valid()) {
                        fail(label +
                             " has dependent function exception specification "
                             "without a canonical predicate");
                    }
                    if (data.exception_spec.kind !=
                            FunctionExceptionSpecKind::Dependent &&
                        data.exception_spec.predicate.valid()) {
                        fail(label +
                             " has concrete function exception specification "
                             "with a dependent predicate");
                    }
                    check_template_value_expression(
                        data.exception_spec.predicate,
                        "dependent function exception specification");
                } else if constexpr (std::is_same_v<Payload, RecordTypePayload>) {
                    check_entity(data.entity, "record entity");
                    check_name(data.name, "record name");
                } else if constexpr (std::is_same_v<Payload, EnumTypePayload>) {
                    check_entity(data.entity, "enum entity");
                    check_name(data.name, "enum name");
                    check_type_ref(data.underlying_type, "enum underlying type");
                } else if constexpr (std::is_same_v<Payload, VectorTypePayload>) {
                    check_type_ref(data.element_type, "vector element type");
                } else if constexpr (std::is_same_v<Payload, ComplexTypePayload>) {
                    check_type_ref(data.element_type, "complex element type");
                } else if constexpr (std::is_same_v<Payload, TypedefTypePayload>) {
                    check_entity(data.entity, "typedef entity");
                    check_name(data.name, "typedef name");
                    check_type_ref(data.underlying_type, "typedef underlying type");
                } else if constexpr (std::is_same_v<Payload, TypeParamTypePayload>) {
                    check_entity(data.entity, "type parameter entity");
                    check_name(data.name, "type parameter name");
                } else if constexpr (std::is_same_v<Payload, TemplateSpecializationTypePayload>) {
                    check_name(data.template_name, "template specialization name");
                    check_entity(data.primary_template, "primary template entity");
                    check_template_value_expression(
                        data.splice_operand,
                        "dependent splice template operand");
                    for (const TemplateArgument& argument : data.arguments) {
                        check_template_argument(argument);
                    }
                } else if constexpr (std::is_same_v<Payload, AliasSpecializationTypePayload>) {
                    check_name(data.template_name, "alias specialization name");
                    check_entity(data.alias_template,
                                 "alias specialization template entity");
                    for (const TemplateArgument& argument : data.arguments) {
                        check_template_argument(argument);
                    }
                    check_type_ref(data.associated_type,
                                   "alias specialization associated type");
                } else if constexpr (std::is_same_v<Payload, DependentNameTypePayload>) {
                    check_type_ref(data.qualifier_type, "dependent qualifier type");
                    check_name(data.member_name, "dependent member name");
                    for (const TemplateArgument& argument : data.template_arguments) {
                        check_template_argument(argument);
                    }
                } else if constexpr (std::is_same_v<Payload, DependentTypePayload>) {
                    check_name(data.debug_name, "dependent debug name");
                } else if constexpr (std::is_same_v<Payload, TypeofExprTypePayload>) {
                    check_inst(data.expr, "typeof expression");
                } else if constexpr (std::is_same_v<Payload, DecltypeExprTypePayload>) {
                    check_inst(data.expr, "decltype expression");
                    check_type_ref(data.operand_type,
                                   "decltype operand type");
                    check_type_ref(data.dependent_value_qualifier,
                                   "decltype dependent value qualifier");
                    check_name(data.dependent_value_name,
                               "decltype dependent value name");
                    check_template_value_expression(
                        data.operand_expression,
                        "dependent decltype operand expression");
                } else if constexpr (std::is_same_v<Payload, BuiltinTypeTransformTypePayload>) {
                    check_type_ref(data.operand_type, "builtin transform operand type");
                } else if constexpr (std::is_same_v<Payload, BuiltinPackElementTypePayload>) {
                    if (data.arguments.size() < 2) {
                        fail(label + " has builtin pack-element type without "
                             "an index and type pack");
                    } else {
                        if (data.arguments.front().kind !=
                            TemplateArgumentKind::Value) {
                            fail(label + " has non-value builtin "
                                 "pack-element index");
                        }
                        for (size_t argument_index = 1;
                             argument_index < data.arguments.size();
                             ++argument_index) {
                            if (data.arguments[argument_index].kind !=
                                TemplateArgumentKind::Type) {
                                fail(label + " has non-type builtin "
                                     "pack-element operand");
                            }
                        }
                    }
                    for (const TemplateArgument& argument : data.arguments) {
                        check_template_argument(argument);
                    }
                } else if constexpr (std::is_same_v<Payload, PackIndexTypePayload>) {
                    check_type_ref(data.pack_type, "pack-index source pack");
                    check_template_value_expression(
                        data.index_expression, "pack-index expression");
                    for (TypeRef expansion : data.expansions) {
                        check_type_ref(expansion, "pack-index expansion");
                    }
                    if (!data.index_expression.valid()) {
                        fail(label + " has pack-index type without an index");
                    }
                    if (!data.fully_substituted &&
                        !data.expansions.empty()) {
                        fail(label + " has unbound pack-index type with "
                             "substituted expansions");
                    }
                } else if constexpr (std::is_same_v<Payload, PlaceTypePayload>) {
                    check_type_ref(data.object_type, "place object type");
                }
            },
            payload);
    }
    for (uint32_t i = 1; i < constant_states_.size(); ++i) {
        std::vector<const ConstantStateFact*> stack{&constant_states_[i]};
        while (!stack.empty()) {
            const ConstantStateFact& state = *stack.back();
            stack.pop_back();
            if (state.type.type.valid() && !valid(state.type.type)) {
                fail("constant state has invalid type #" +
                     std::to_string(i));
            }
            if (state.kind == ConstantStateKind::Integer) {
                if (!state.integer_value.canonical()) {
                    fail("constant state has invalid integer payload #" +
                         std::to_string(i));
                } else if (state.type.type.valid() &&
                           valid(state.type.type) &&
                           is_integer_like_type(*this, state.type.type)) {
                    IntegerTypeShape shape =
                        integer_shape_for_type(*this, state.type.type);
                    if (state.integer_value.bit_width != shape.bit_width ||
                        state.integer_value.is_unsigned != shape.is_unsigned) {
                        fail("constant state integer payload shape does not "
                             "match its type #" + std::to_string(i));
                    }
                }
            }
            if (state.kind == ConstantStateKind::Complex &&
                state.complex_is_integer &&
                (!state.complex_integer_real.canonical() ||
                 !state.complex_integer_imag.canonical())) {
                fail("constant state has invalid complex integer payload #" +
                     std::to_string(i));
            }
            auto check_state_entity = [&](EntityId entity_id) {
                if (entity_id.valid() && !valid(entity_id)) {
                    fail("constant state has invalid entity #" +
                         std::to_string(i));
                }
            };
            check_state_entity(state.address_entity);
            check_state_entity(state.member_entity);
            check_state_entity(state.subobject_entity);
            check_state_entity(state.active_union_member);
            TypeId state_type = state.type.type.valid()
                ? resolved_type(state.type.type)
                : TypeId{};
            const RecordFacts* state_record = valid(state_type)
                ? record_facts_for_type(state_type)
                : nullptr;
            bool closure_state = state.kind == ConstantStateKind::Record &&
                state_record && state_record->is_lambda_closure;
            if (state.closure_identity.valid() || closure_state) {
                if (!valid(state.closure_identity)) {
                    fail("constant state has invalid closure identity #" +
                         std::to_string(i));
                } else {
                    if (!closure_state ||
                        state_record->closure_identity !=
                            state.closure_identity) {
                        fail("constant state has inconsistent closure identity #" +
                             std::to_string(i));
                    }
                }
            }
            if (state.address_string_literal.valid() &&
                !valid(state.address_string_literal)) {
                fail("constant state has invalid string literal #" +
                     std::to_string(i));
            }
            for (const ConstantStateFact& child : state.elements) {
                stack.push_back(&child);
            }
        }
    }
    for (uint32_t i = 1; i < closure_identities_.size(); ++i) {
        const ClosureIdentityFact& closure = closure_identities_[i];
        if (!closure.record.valid() || !valid(closure.record) ||
            entity(closure.record).kind != EntityKind::Record) {
            fail("closure identity has invalid record #" +
                 std::to_string(i));
        }
        if (!closure.type.type.valid() || !valid(closure.type.type) ||
            record_entity(resolved_type(closure.type.type)) !=
                closure.record) {
            fail("closure identity has invalid closure type #" +
                 std::to_string(i));
        }
        if (!closure.call_operator.valid() ||
            !valid(closure.call_operator) ||
            entity(closure.call_operator).kind != EntityKind::Method ||
            entity(closure.call_operator).parent != closure.record) {
            fail("closure identity has invalid call operator #" +
                 std::to_string(i));
        }
        if (closure.invoker.valid() &&
            (!valid(closure.invoker) ||
             (entity(closure.invoker).kind != EntityKind::Function &&
              entity(closure.invoker).kind != EntityKind::Method))) {
            fail("closure identity has invalid invoker #" +
                 std::to_string(i));
        }
        if (closure.lexical_owner.valid() &&
            !valid(closure.lexical_owner)) {
            fail("closure identity has invalid lexical owner #" +
                 std::to_string(i));
        }
        if (closure.abi_context_name.valid() &&
            !valid(closure.abi_context_name)) {
            fail("closure identity has invalid ABI context name #" +
                 std::to_string(i));
        }
        if (closure.abi_context_decl.valid() &&
            !valid(closure.abi_context_decl)) {
            fail("closure identity has invalid ABI declaration context #" +
                 std::to_string(i));
        }
        if (closure.abi_context ==
                ClosureAbiContextKind::VariableInitializer &&
            (!closure.abi_context_name.valid() ||
             !closure.abi_context_decl.valid())) {
            fail("variable-initializer closure identity is incomplete #" +
                 std::to_string(i));
        }
    }
    for (uint32_t i = 1; i < entities_.size(); ++i) {
        const Entity& e = entities_[i];
        if (static_cast<uint32_t>(
                e.symbol_policy.definition_emission) >
            static_cast<uint32_t>(
                DefinitionEmissionKind::Required)) {
            fail("entity has unknown definition-emission policy #" +
                 std::to_string(i));
        }
        if (e.symbol_policy.finalized &&
            e.symbol_policy.definition_emission ==
                DefinitionEmissionKind::Required &&
            ((!e.is_definition &&
              e.attr_facts.alias_target.empty() &&
              e.attr_facts.weakref_target.empty() &&
              e.attr_facts.ifunc_target.empty()) ||
             e.is_deleted ||
             e.decl_flags.is_consteval ||
             e.is_template_pattern ||
             e.result_type_only_definition ||
             e.suppressed_by_explicit_instantiation_declaration ||
             e.suppressed_as_unselected_template_candidate ||
             (e.symbol_policy.imported_definition &&
              e.symbol_policy.emission != LinkageKind::LinkOnceODR))) {
            fail("entity has an unavailable required definition #" +
                 std::to_string(i));
        }
        if (e.is_explicit_instantiation_definition &&
            e.suppressed_by_explicit_instantiation_declaration) {
            fail("entity is both an explicit instantiation definition and "
                 "a suppressed explicit instantiation declaration #" +
                 std::to_string(i));
        }
        if (e.is_deleted) {
            bool callable =
                e.kind == EntityKind::Function ||
                e.kind == EntityKind::Method ||
                e.kind == EntityKind::Constructor ||
                e.kind == EntityKind::Destructor;
            if (!callable) {
                fail("non-callable entity is marked deleted #" +
                     std::to_string(i));
            }
            if (!e.is_definition &&
                (!e.linkage_predecessor.valid() ||
                 !valid(e.linkage_predecessor) ||
                 !entity(e.linkage_predecessor).is_deleted)) {
                fail("deleted callable has no deleted definition predecessor #" +
                     std::to_string(i));
            }
        }
        if (e.name.valid() && !valid(e.name)) fail("entity has invalid name #" + std::to_string(i));
        if (e.unnamed_type_linkage_name.valid() &&
            !valid(e.unnamed_type_linkage_name)) {
            fail("entity has invalid unnamed-type linkage name #" +
                 std::to_string(i));
        } else if (e.unnamed_type_linkage_name.valid() &&
                   (e.kind != EntityKind::Record || !e.is_unnamed_record)) {
            fail("entity has misplaced unnamed-type linkage name #" +
                 std::to_string(i));
        }
        if (e.unnamed_type_ordinal != Entity::NoUnnamedTypeOrdinal) {
            bool record_scope_identity =
                e.kind == EntityKind::Record && e.is_unnamed_record &&
                !e.unnamed_type_linkage_name.valid() &&
                !e.local_enclosing_function.valid() &&
                e.lexical_context.valid() && valid(e.lexical_context) &&
                decl_context(e.lexical_context).kind ==
                    DeclContextKind::Record;
            if (!record_scope_identity) {
                fail("entity has misplaced unnamed-type ordinal #" +
                     std::to_string(i));
            }
        }
        if (e.type.valid() && !valid(e.type)) fail("entity has invalid type #" + std::to_string(i));
        if (e.parent.valid() && !valid(e.parent)) fail("entity has invalid parent #" + std::to_string(i));
        if (e.local_source_name.valid() && !valid(e.local_source_name)) {
            fail("entity has invalid local source name #" + std::to_string(i));
        }
        if (e.local_enclosing_function.valid() &&
            !valid(e.local_enclosing_function)) {
            fail("entity has invalid local enclosing function #" +
                 std::to_string(i));
        }
        if (e.local_source_name.valid() !=
            e.local_enclosing_function.valid()) {
            fail("entity has incomplete local-name identity #" +
                 std::to_string(i));
        } else if (e.local_enclosing_function.valid() &&
                   entity(e.local_enclosing_function).kind !=
                       EntityKind::Function &&
                   entity(e.local_enclosing_function).kind !=
                       EntityKind::Method &&
                   entity(e.local_enclosing_function).kind !=
                       EntityKind::Constructor &&
                   entity(e.local_enclosing_function).kind !=
                       EntityKind::Destructor) {
            fail("entity local-name owner is not a function #" +
                 std::to_string(i));
        }
        if (e.lexical_context.valid() && !valid(e.lexical_context)) {
            fail("entity has invalid lexical context #" + std::to_string(i));
        }
        if (e.semantic_context.valid() && !valid(e.semantic_context)) {
            fail("entity has invalid semantic context #" + std::to_string(i));
        }
        if (e.owning_function.valid() && !valid(e.owning_function)) {
            fail("entity has invalid owning function #" + std::to_string(i));
        } else if (e.owning_function.valid() &&
                   entity(e.owning_function).kind != EntityKind::Function &&
                   entity(e.owning_function).kind != EntityKind::Method &&
                   entity(e.owning_function).kind != EntityKind::Constructor &&
                   entity(e.owning_function).kind != EntityKind::Destructor) {
            fail("entity owning function is not a function #" +
                 std::to_string(i));
        }
        if (e.placeholder_result.valid() &&
            !valid(e.placeholder_result)) {
            fail("entity has invalid placeholder-result fact #" +
                 std::to_string(i));
        }
        if (e.generated_symbol_role == GeneratedSymbolRole::ArrayCleanup) {
            if (e.kind != EntityKind::Function) {
                fail("array cleanup helper is not a function #" +
                     std::to_string(i));
            }
            if (!e.abi_owner.valid() || !valid(e.abi_owner) ||
                entity(e.abi_owner).kind != EntityKind::Record) {
                fail("array cleanup helper has invalid class owner #" +
                     std::to_string(i));
            }
            TypeId function_type = resolved_type(e.type);
            const auto* function = valid(function_type) &&
                    type(function_type).kind == TypeKind::Function
                ? std::get_if<FunctionTypePayload>(
                      &type_payload(function_type))
                : nullptr;
            bool signature_ok = function &&
                is_void_type(function->return_type.type) &&
                function->parameters.size() == 1;
            if (signature_ok) {
                TypeId pointer =
                    resolved_type(function->parameters.front().type);
                TypeId pointee = valid(pointer) &&
                        type(pointer).kind == TypeKind::Pointer
                    ? resolved_type(pointer_pointee_type(pointer))
                    : TypeId{};
                signature_ok = valid(pointee) &&
                    type(pointee).kind == TypeKind::Array;
            }
            if (!signature_ok) {
                fail("array cleanup helper has invalid signature #" +
                     std::to_string(i));
            }
        }
        if (e.constant_state.valid() && !valid(e.constant_state)) {
            fail("entity has invalid constant state #" + std::to_string(i));
        }
        if (e.has_constant_value &&
            e.constant_value_kind == TemplateValueKind::Integer) {
            if (!e.constant_integer_value.canonical()) {
                fail("entity has invalid integer constant payload #" +
                     std::to_string(i));
            } else {
                TypeId constant_type = resolved_type(e.type);
                if (valid(constant_type) &&
                    is_integer_like_type(*this, constant_type)) {
                    IntegerTypeShape shape =
                        integer_shape_for_type(*this, constant_type);
                    if (e.constant_integer_value.bit_width != shape.bit_width ||
                        e.constant_integer_value.is_unsigned !=
                            shape.is_unsigned) {
                        std::string entity_name = e.name.valid()
                            ? std::string(name(e.name))
                            : "<unnamed>";
                        fail("entity integer constant payload shape does not "
                             "match its type #" + std::to_string(i) +
                             " (" + entity_name + ", payload " +
                             std::to_string(e.constant_integer_value.bit_width) +
                             (e.constant_integer_value.is_unsigned
                                  ? "-bit unsigned, expected "
                                  : "-bit signed, expected ") +
                             std::to_string(shape.bit_width) +
                             (shape.is_unsigned
                                  ? "-bit unsigned)"
                                  : "-bit signed)"));
                    }
                }
            }
        }
        if (e.has_constant_value &&
            e.constant_value_kind == TemplateValueKind::Boolean &&
            !e.constant_integer_value.canonical()) {
            fail("entity has invalid boolean constant payload #" +
                 std::to_string(i));
        }
        if (e.constant_closure_identity.valid()) {
            if (!valid(e.constant_closure_identity) ||
                e.constant_value_kind != TemplateValueKind::Closure) {
                fail("entity has invalid constant closure identity #" +
                     std::to_string(i));
            }
        } else if (e.has_constant_value &&
                   e.constant_value_kind == TemplateValueKind::Closure) {
            fail("entity is missing constant closure identity #" +
                 std::to_string(i));
        }
        if (e.object_storage_alias.valid() &&
            e.object_storage_alias_place.valid()) {
            fail("entity has two object-storage aliases #" +
                 std::to_string(i));
        }
        if (e.object_storage_alias.valid()) {
            if (!valid(e.object_storage_alias)) {
                fail("entity has invalid object-storage entity alias #" +
                     std::to_string(i));
            } else if (e.object_storage_alias.index == i) {
                fail("entity aliases its own object storage #" +
                     std::to_string(i));
            } else if (resolved_type(e.type) !=
                       resolved_type(entity(e.object_storage_alias).type)) {
                fail("entity object-storage alias has a different type #" +
                     std::to_string(i));
            }
        }
        if (e.object_storage_alias_place.valid()) {
            if (!valid(e.object_storage_alias_place)) {
                fail("entity has invalid object-storage place alias #" +
                     std::to_string(i));
            } else {
                TypeId place_type = inst(e.object_storage_alias_place).result_type;
                TypeId object_type = place_object_type(place_type);
                if (!object_type.valid() ||
                    resolved_type(e.type) != resolved_type(object_type)) {
                    fail("entity object-storage place alias has a different type #" +
                         std::to_string(i));
                }
            }
        }
        if ((e.is_function_result_object ||
             e.is_exception_declaration ||
             e.is_parameter_argument_object) &&
            e.kind != EntityKind::Variable) {
            fail("non-variable entity has object-ownership flags #" +
                 std::to_string(i));
        }
        if (e.is_parameter_argument_object &&
            e.storage_duration != StorageDuration::Temporary) {
            fail("parameter argument object is not temporary #" +
                 std::to_string(i));
        }
    }
    auto check_required_dependency =
        [&](EntityId owner, EntityId dependency) {
            if (!valid(owner) || !valid(dependency)) {
                return;
            }
            const Entity& target = entity(dependency);
            bool has_backend_symbol =
                target.kind == EntityKind::Function ||
                target.kind == EntityKind::Method ||
                target.kind == EntityKind::Constructor ||
                target.kind == EntityKind::Destructor ||
                target.kind == EntityKind::Variable;
            if (has_backend_symbol &&
                target.symbol_policy.finalized &&
                target.symbol_policy.definition_emission ==
                    DefinitionEmissionKind::Deferred) {
                fail("required definition " + format_entity(owner) +
                     " references deferred definition " +
                     format_entity(dependency));
            }
        };
    for (uint32_t i = 1; i < functions_.size(); ++i) {
        const Function& function = functions_[i];
        if (!valid(function.entity) ||
            entity(function.entity)
                    .symbol_policy.definition_emission !=
                DefinitionEmissionKind::Required) {
            continue;
        }
        for (BlockId block_id : function.blocks) {
            if (!valid(block_id)) {
                continue;
            }
            for (InstId inst_id : block(block_id).instructions) {
                if (!valid(inst_id)) {
                    continue;
                }
                for (const Operand& operand :
                     operands(inst(inst_id).operands)) {
                    if (const auto* dependency =
                            std::get_if<EntityId>(&operand.data)) {
                        check_required_dependency(function.entity,
                                                  *dependency);
                    }
                }
            }
        }
    }
    for (uint32_t i = 1; i < entities_.size(); ++i) {
        EntityId owner{i, entity_generations_[i]};
        const Entity& e = entities_[i];
        if (e.kind != EntityKind::Variable ||
            e.symbol_policy.definition_emission !=
                DefinitionEmissionKind::Required) {
            continue;
        }
        for (const StaticInitializerRelocation& relocation :
             e.static_initializer_relocations) {
            check_required_dependency(owner, relocation.entity);
        }
    }
    auto check_attribute_target =
        [&](EntityId owner, const std::string& target_name) {
            if (target_name.empty()) {
                return;
            }
            for (uint32_t i = 1; i < entities_.size(); ++i) {
                EntityId dependency{i, entity_generations_[i]};
                const Entity& target = entities_[i];
                if (dependency == owner || !target.name.valid() ||
                    name(target.name) != target_name) {
                    continue;
                }
                check_required_dependency(owner, dependency);
            }
        };
    for (uint32_t i = 1; i < entities_.size(); ++i) {
        EntityId owner{i, entity_generations_[i]};
        const Entity& e = entities_[i];
        if (e.symbol_policy.definition_emission !=
            DefinitionEmissionKind::Required) {
            continue;
        }
        check_attribute_target(owner, e.attr_facts.alias_target);
        check_attribute_target(owner, e.attr_facts.weakref_target);
        check_attribute_target(owner, e.attr_facts.ifunc_target);
    }
    for (uint32_t i = 1; i < placeholder_result_facts_.size(); ++i) {
        const PlaceholderResultFact& fact = placeholder_result_facts_[i];
        if (!valid(fact.declared_function_type) ||
            !valid(fact.declared_return_pattern.type)) {
            fail("placeholder-result fact has an invalid declared pattern #" +
                 std::to_string(i));
        }
        if (fact.state == PlaceholderResultState::Deducing) {
            fail("placeholder-result deduction remained active #" +
                 std::to_string(i));
        }
        if (fact.state == PlaceholderResultState::Complete &&
            (!fact.result.type.valid() || !valid(fact.result.type))) {
            fail("completed placeholder-result fact has no valid result #" +
                 std::to_string(i));
        }
        if (fact.candidate.type.valid() && !valid(fact.candidate.type)) {
            fail("placeholder-result fact has an invalid candidate #" +
                 std::to_string(i));
        }
    }
    for (const auto& [key, specialization] : template_specializations_) {
        uint32_t owner_index = static_cast<uint32_t>(key);
        uint32_t owner_generation = static_cast<uint32_t>(key >> 32);
        if (owner_index == 0 || owner_index >= entities_.size()) {
            fail("template specialization fact has invalid owner");
            continue;
        }
        EntityId owner{owner_index, owner_generation};
        if (!valid(owner)) {
            fail("template specialization fact has stale owner");
            continue;
        }
        if (specialization.template_entity.valid() &&
            !valid(specialization.template_entity)) {
            fail("template specialization fact has invalid template entity");
        }
        if (specialization.selected_template_entity.valid() &&
            !valid(specialization.selected_template_entity)) {
            fail("template specialization fact has invalid selected template entity");
        }
        std::unordered_set<uint64_t> demand_keys;
        for (const InstantiationDemandFact& demand :
             specialization.instantiation_demands) {
            if (demand.subject.valid() && !valid(demand.subject)) {
                fail("class instantiation demand has invalid subject");
            }
            uint64_t demand_key =
                (static_cast<uint64_t>(demand.subject.index) << 8) |
                static_cast<uint64_t>(demand.kind);
            if (!demand_keys.insert(demand_key).second) {
                fail("class instantiation demand is duplicated");
            }
            if (demand.status == InstantiationDemandStatus::Active) {
                fail("class instantiation demand remained active");
            }
            bool needs_declaration_set =
                demand.kind != InstantiationDemandKind::Identity;
            if (needs_declaration_set &&
                demand.status == InstantiationDemandStatus::Satisfied &&
                entity(owner).kind == EntityKind::Record) {
                const RecordFacts* facts = record_facts(owner);
                if (!facts || facts->is_incomplete) {
                    fail("satisfied class instantiation demand has an incomplete owner");
                }
                if (!specialization.selected_template_entity.valid()) {
                    fail("materialized class specialization has no selected template");
                }
            }
        }
    }
    for (const auto& [key, comparison] : defaulted_comparison_facts_) {
        uint32_t function_index = static_cast<uint32_t>(key);
        uint32_t function_generation = static_cast<uint32_t>(key >> 32);
        EntityId function{function_index, function_generation};
        if (!valid(function) || comparison.function != function) {
            fail("defaulted comparison fact has invalid function identity");
            continue;
        }
        if (!comparison.owner_record.valid() ||
            !valid(comparison.owner_record) ||
            entity(comparison.owner_record).kind != EntityKind::Record) {
            fail("defaulted comparison fact has invalid owning record");
        }
        if (comparison.result_type.type.valid() &&
            !valid(comparison.result_type.type)) {
            fail("defaulted comparison fact has invalid result type");
        }
        if (comparison.implicit_equality_origin.valid() &&
            !valid(comparison.implicit_equality_origin)) {
            fail("defaulted comparison fact has invalid implicit equality origin");
        }
        for (const ComparisonSubobjectFact& subobject :
             comparison.subobjects) {
            if (!subobject.entity.valid() || !valid(subobject.entity)) {
                fail("defaulted comparison fact has invalid subobject entity");
            }
            if (!subobject.type.type.valid() ||
                !valid(subobject.type.type)) {
                fail("defaulted comparison fact has invalid subobject type");
            }
            if (!subobject.array_extents.empty()) {
                if (!subobject.array_leaf_type.type.valid() ||
                    !valid(subobject.array_leaf_type.type)) {
                    fail("defaulted comparison array has invalid leaf type");
                }
                size_t count = 1;
                for (size_t extent : subobject.array_extents) {
                    count *= extent;
                }
                if (count != subobject.array_element_count) {
                    fail("defaulted comparison array has inconsistent extent");
                }
            }
        }
    }
    for (uint32_t i = 1; i < decl_contexts_.size(); ++i) {
        const DeclContext& context = decl_contexts_[i];
        DeclContextId context_id{i, decl_context_generations_[i]};
        if (context.kind == DeclContextKind::Invalid) {
            fail("declaration context has invalid kind #" + std::to_string(i));
        }
        if (context.owner.valid() && !valid(context.owner)) {
            fail("declaration context has invalid owner #" + std::to_string(i));
        }
        if (context.parent.valid() && !valid(context.parent)) {
            fail("declaration context has invalid parent #" + std::to_string(i));
        }
        for (DeclContextId child : context.children) {
            if (!valid(child)) {
                fail("declaration context has invalid child #" + std::to_string(i));
            } else if (decl_context(child).parent != context_id) {
                fail("declaration context child does not point back to parent");
            }
        }
        for (BindingId binding_id : context.bindings) {
            if (!valid(binding_id)) {
                fail("declaration context has invalid binding #" + std::to_string(i));
            } else if (binding(binding_id).context != context_id) {
                fail("declaration context binding does not point back to owner");
            }
        }
        std::unordered_map<uint64_t, BindingId> expected_ordinary_latest;
        std::unordered_map<uint64_t, BindingId> expected_ordinary_values;
        std::unordered_map<uint64_t, BindingId> expected_ordinary_callables;
        std::unordered_map<uint64_t, BindingId> expected_ordinary_type_names;
        std::unordered_map<uint64_t, BindingId> expected_ordinary_template_names;
        std::unordered_map<uint64_t, BindingId> expected_tags;
        std::unordered_map<uint64_t, BindingId> expected_labels;
        for (BindingId binding_id : context.bindings) {
            if (!valid(binding_id)) {
                continue;
            }
            const Binding& b = binding(binding_id);
            if (b.context != context_id || !valid(b.name)) {
                continue;
            }
            uint64_t key = id_key(b.name);
            switch (b.lookup_namespace) {
                case LookupNamespace::Ordinary:
                    expected_ordinary_latest[key] = binding_id;
                    if (ordinary_binding_matches_category(
                            b, OrdinaryBindingCategory::Value)) {
                        expected_ordinary_values[key] = binding_id;
                    }
                    if (ordinary_binding_matches_category(
                            b, OrdinaryBindingCategory::Callable)) {
                        expected_ordinary_callables[key] = binding_id;
                    }
                    if (ordinary_binding_matches_category(
                            b, OrdinaryBindingCategory::TypeName)) {
                        expected_ordinary_type_names[key] = binding_id;
                    }
                    if (ordinary_binding_matches_category(
                            b, OrdinaryBindingCategory::TemplateName)) {
                        expected_ordinary_template_names[key] = binding_id;
                    }
                    break;
                case LookupNamespace::Tag:
                    expected_tags[key] = binding_id;
                    break;
                case LookupNamespace::Label:
                    expected_labels[key] = binding_id;
                    break;
                case LookupNamespace::None:
                    break;
            }
        }
        auto check_index =
            [&](const std::unordered_map<uint64_t, BindingId>& actual,
                const std::unordered_map<uint64_t, BindingId>& expected,
                const char* label) {
                if (actual.size() != expected.size()) {
                    fail(std::string("declaration context ") + label +
                         " lookup index has wrong size");
                    return;
                }
                for (const auto& [key, expected_id] : expected) {
                    auto found = actual.find(key);
                    if (found == actual.end()) {
                        fail(std::string("declaration context ") + label +
                             " lookup index is missing a binding");
                    } else if (found->second != expected_id) {

                        auto callable =
                            context.ordinary_callable_bindings.find(key);
                        bool callable_reassertion =
                            std::string_view(label) == "ordinary" &&
                            callable !=
                                context.ordinary_callable_bindings.end() &&
                            callable->second == found->second;
                        if (!callable_reassertion) {
                            fail(std::string("declaration context ") + label +
                                 " lookup index points at the wrong binding");
                        }
                    }
                }
            };
        check_index(context.ordinary_latest_bindings,
                    expected_ordinary_latest,
                    "ordinary");
        check_index(context.ordinary_value_bindings,
                    expected_ordinary_values,
                    "ordinary value");
        check_index(context.ordinary_callable_bindings,
                    expected_ordinary_callables,
                    "ordinary callable");
        check_index(context.ordinary_type_name_bindings,
                    expected_ordinary_type_names,
                    "ordinary type-name");
        check_index(context.ordinary_template_name_bindings,
                    expected_ordinary_template_names,
                    "ordinary template-name");
        check_index(context.tag_bindings, expected_tags, "tag");
        check_index(context.label_bindings, expected_labels, "label");
    }
    for (uint32_t i = 1; i < bindings_.size(); ++i) {
        const Binding& b = bindings_[i];
        if (!b.name.valid() || !valid(b.name)) {
            fail("binding has invalid name #" + std::to_string(i));
        }
        if (!b.context.valid() || !valid(b.context)) {
            fail("binding has invalid context #" + std::to_string(i));
        }
        if (b.lookup_namespace == LookupNamespace::None) {
            fail("binding has no lookup namespace #" + std::to_string(i));
        }
        for (EntityId entity_id : b.entities) {
            if (!valid(entity_id)) {
                fail("binding has invalid entity #" + std::to_string(i));
            }
        }
        if (b.type.valid() && !valid(b.type.type)) {
            fail("binding has invalid type #" + std::to_string(i));
        }
        if (b.place.valid() && !valid(b.place)) {
            fail("binding has invalid place #" + std::to_string(i));
        }
    }
    for (const auto& [key, fact] : structured_binding_facts_) {
        (void)key;
        if (!fact.backing.valid() || !valid(fact.backing) ||
            entity(fact.backing).kind != EntityKind::Variable ||
            entity(fact.backing).object_origin !=
                EntityObjectOrigin::StructuredBindingBacking) {
            fail("structured-binding facts have an invalid backing object");
            continue;
        }
        const std::string label =
            "structured binding " + format_entity(fact.backing);
        if (!fact.decomposed_type.type.valid() ||
            !valid(fact.decomposed_type.type)) {
            fail(label + " has an invalid decomposed type");
        }
        for (NameId source_name : fact.source_names) {
            if (!source_name.valid() || !valid(source_name)) {
                fail(label + " has an invalid source name");
            }
        }
        if (fact.has_pack &&
            fact.pack_position >= fact.source_names.size()) {
            fail(label + " has an invalid pack position");
        }
        for (size_t index = 0; index < fact.projections.size(); ++index) {
            const StructuredBindingProjectionFact& projection =
                fact.projections[index];
            if (!projection.binding.valid() ||
                !valid(projection.binding) ||
                entity(projection.binding).kind !=
                    EntityKind::StructuredBinding) {
                fail(label + " has an invalid projection binding");
                continue;
            }
            const Entity& binding_entity = entity(projection.binding);
            if (binding_entity.structured_binding_backing != fact.backing ||
                binding_entity.structured_binding_index != index) {
                fail(label + " has a projection with inconsistent identity");
            }
            if (!projection.type.type.valid() ||
                !valid(projection.type.type) ||
                !projection.referenced_type.type.valid() ||
                !valid(projection.referenced_type.type)) {
                fail(label + " has a projection with an invalid type");
            }
            if (projection.holder.valid() &&
                (!valid(projection.holder) ||
                 entity(projection.holder).kind != EntityKind::Variable)) {
                fail(label + " has an invalid tuple reference holder");
            }
            if (projection.member.valid() &&
                (!valid(projection.member) ||
                 entity(projection.member).kind != EntityKind::Field)) {
                fail(label + " has an invalid member projection");
            }
            for (EntityId base : projection.base_path) {
                if (!valid(base) || entity(base).kind != EntityKind::Field) {
                    fail(label + " has an invalid base projection path");
                }
            }
        }
    }
    for (const auto& [key, facts] : record_facts_) {
        (void)key;
        if (!valid(facts.entity) || entity(facts.entity).kind != EntityKind::Record) {
            fail("record facts have invalid record entity");
            continue;
        }
        if (facts.type.valid() && !valid(facts.type.type)) {
            fail("record facts for " + format_entity(facts.entity) + " have invalid type");
        }
        if (facts.is_lambda_closure) {
            if (!valid(facts.closure_identity)) {
                fail("lambda record facts for " +
                     format_entity(facts.entity) +
                     " have invalid closure identity");
            } else {
                const ClosureIdentityFact& closure =
                    closure_identity(facts.closure_identity);
                if (closure.record != facts.entity ||
                    closure.type.type != facts.type.type ||
                    closure.is_structural !=
                        !facts.lambda_has_capture) {
                    fail("lambda record facts for " +
                         format_entity(facts.entity) +
                         " have inconsistent closure identity");
                }
            }
        } else if (facts.closure_identity.valid()) {
            fail("non-lambda record facts have closure identity");
        }
        if (!facts.is_incomplete && facts.alignment == 0) {
            fail("record facts for " + format_entity(facts.entity) + " have zero alignment");
        }
        for (const RecordBaseFact& base : facts.bases) {
            if (base.name.valid() && !valid(base.name)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid base name");
            }
            if (base.type.valid() && !valid(base.type.type)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid base type");
            }
            if (base.record_entity.valid() &&
                (!valid(base.record_entity) || entity(base.record_entity).kind != EntityKind::Record)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid base entity");
            }
        }
        for (const RecordDependentBaseFact& base : facts.dependent_bases) {
            if (base.type.valid() && !valid(base.type.type)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid dependent base type");
            }
        }
        for (const RecordInheritedConstructorNominationFact& nomination :
             facts.inherited_constructor_nominations) {
            bool concrete = nomination.nominated_record.valid();
            bool dependent = nomination.dependent_qualifier.type.valid();
            if (concrete == dependent) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have a non-canonical inherited-constructor nomination");
            }
            if (concrete &&
                (!valid(nomination.nominated_record) ||
                 entity(nomination.nominated_record).kind !=
                     EntityKind::Record)) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have an invalid inherited-constructor base");
            }
            if (dependent &&
                !valid(nomination.dependent_qualifier.type)) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have an invalid dependent inherited-constructor base");
            }
        }
        for (const RecordFieldFact& field : facts.fields) {
            if (field.name.valid() && !valid(field.name)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid field name");
            }
            if (!valid(field.entity) || entity(field.entity).kind != EntityKind::Field) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid field entity");
            }
            if (valid(field.entity) && entity(field.entity).parent != facts.entity) {
                fail("field entity parent does not match owning record facts");
            }
            if (field.type.valid() && !valid(field.type.type)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid field type");
            }
            bool is_capture = field.lambda_capture_kind !=
                LambdaCaptureFieldKind::None;
            if (is_capture && !facts.is_lambda_closure) {
                fail("non-closure record has a lambda capture field");
            }
            bool captures_entity = field.lambda_capture_kind ==
                LambdaCaptureFieldKind::Entity;
            if (captures_entity != field.lambda_capture_source.valid() ||
                (field.lambda_capture_source.valid() &&
                 !valid(field.lambda_capture_source))) {
                fail("lambda capture field has an invalid source binding");
            }
            if (field.is_no_unique_address &&
                !field.is_potentially_overlapping) {
                fail("no_unique_address field is not potentially overlapping");
            }
            if (field.subobject_size == SubobjectSizeKind::Zero &&
                (!field.is_potentially_overlapping || field.is_bitfield)) {
                fail("zero-size record field has invalid overlap classification");
            }
            if (field.is_anonymous_union_object &&
                entity(field.entity).object_origin !=
                    EntityObjectOrigin::AnonymousUnion) {
                fail("anonymous-union field lacks anonymous object origin");
            }
        }
        if (facts.anonymous_union_object_kind !=
                AnonymousUnionObjectKind::None) {
            if (facts.kind != RecordKind::Union ||
                !facts.anonymous_union_object.valid() ||
                !valid(facts.anonymous_union_object) ||
                entity(facts.anonymous_union_object).object_origin !=
                    EntityObjectOrigin::AnonymousUnion) {
                fail("anonymous-union facts have an invalid object");
            }
            if (valid(facts.anonymous_union_object)) {
                EntityKind expected =
                    facts.anonymous_union_object_kind ==
                            AnonymousUnionObjectKind::Member
                        ? EntityKind::Field
                        : EntityKind::Variable;
                if (entity(facts.anonymous_union_object).kind != expected) {
                    fail("anonymous-union object kind does not match its scope");
                }
            }
            for (const AnonymousUnionPromotionFact& promotion :
                 facts.anonymous_union_promotions) {
                if (!promotion.name.valid() || !valid(promotion.name) ||
                    !promotion.member.valid() ||
                    !valid(promotion.member) || promotion.path.empty() ||
                    promotion.path.back() != promotion.member) {
                    fail("anonymous-union promotion has an invalid path");
                }
                for (EntityId step : promotion.path) {
                    if (!step.valid() || !valid(step) ||
                        entity(step).kind != EntityKind::Field) {
                        fail("anonymous-union promotion path has an invalid field");
                    }
                }
            }
        }
        for (const VariantMemberFact& variant : facts.variant_members) {
            if (!variant.member.valid() || !valid(variant.member) ||
                !variant.owning_union.valid() ||
                !valid(variant.owning_union) || variant.path.empty() ||
                variant.path.back() != variant.member) {
                fail("record has an invalid variant-member path");
            }
            for (EntityId step : variant.path) {
                if (!step.valid() || !valid(step) ||
                    entity(step).kind != EntityKind::Field) {
                    fail("record variant-member path has an invalid field");
                }
            }
        }
        for (const RecordMethodFact& method : facts.methods) {
            bool concrete_explicit =
                method.explicit_specifier == ExplicitSpecifierKind::True;
            if (method.is_explicit != concrete_explicit) {
                fail("record method fact has inconsistent explicit-specifier state");
            }
            if (method.explicit_specifier ==
                    ExplicitSpecifierKind::Dependent) {
                if (!method.explicit_value_expression.valid() &&
                    method.explicit_expression_begin >=
                        method.explicit_expression_end) {
                    fail("dependent explicit-specifier has no substitution recipe");
                }
                if (method.explicit_declaration_context.valid() &&
                    !valid(method.explicit_declaration_context)) {
                    fail("dependent explicit-specifier has an invalid declaration context");
                }
            }
            if (method.explicit_value_expression.valid() &&
                (!method.explicit_value_expression.canonical_id.valid() ||
                 !valid(method.explicit_value_expression.canonical_id))) {
                fail("record method fact has a non-canonical explicit-specifier expression");
            }
            if (method.name.valid() && !valid(method.name)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid method name");
            }
            if (method.type.valid() && !valid(method.type.type)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid method type");
            }
            if (method.entity.valid() && !valid(method.entity)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid method entity");
            }
            if (valid(method.entity) && entity(method.entity).parent != facts.entity) {
                fail("method entity parent does not match owning record facts");
            }
            if (method.is_key_function_candidate &&
                (!method.is_virtual ||
                 method.is_pure ||
                 method.is_implicitly_declared ||
                 (method.is_defaulted && !method.is_user_provided) ||
                 method.is_deleted ||
                 method.is_constexpr ||
                 method.is_consteval ||
                 method.is_function_template)) {
                fail("record method has an invalid key-function candidate "
                     "classification");
            }
            if (method.inherited_constructor) {
                const InheritedConstructorFact& inherited =
                    *method.inherited_constructor;
                if (!valid(inherited.origin_constructor) ||
                    entity(inherited.origin_constructor).kind !=
                        EntityKind::Constructor ||
                    !valid(inherited.origin_record) ||
                    entity(inherited.origin_record).kind !=
                        EntityKind::Record ||
                    entity(inherited.origin_constructor).parent !=
                        inherited.origin_record ||
                    inherited.routes.empty()) {
                    fail("record method fact has an invalid inherited-constructor origin");
                }
                for (const InheritedConstructorRouteFact& route :
                     inherited.routes) {
                    if (!valid(route.nominated_direct_base) ||
                        entity(route.nominated_direct_base).kind !=
                            EntityKind::Record ||
                        route.origin_subobject >=
                            facts.virtual_subobjects.size()) {
                        fail("record method fact has an invalid inherited-constructor route");
                    } else if (facts.virtual_subobjects[
                                   route.origin_subobject]
                                   .record_entity !=
                               inherited.origin_record) {
                        fail("inherited-constructor route does not reach its origin record");
                    }
                }
            }
            if (method.constructor_delegation) {
                const ConstructorDelegationFact& delegation =
                    *method.constructor_delegation;
                if (!method.entity.valid() || !valid(method.entity) ||
                    entity(method.entity).kind != EntityKind::Constructor) {
                    fail("non-constructor method has a delegation fact");
                }
                if (delegation.resolved()) {
                    EntityId target = delegation.target_constructor;
                    if (!target.valid() || !valid(target) ||
                        entity(target).kind != EntityKind::Constructor ||
                        entity(target).parent != facts.entity) {
                        fail("constructor delegation has an invalid target");
                    }
                } else if (delegation.target_constructor.valid()) {
                    fail("dependent constructor delegation has a target");
                }
            }
            if (method.deleting_destructor_deallocation.valid()) {
                EntityId selected =
                    method.deleting_destructor_deallocation.entity;
                if (!valid(selected) ||
                    (entity(selected).kind != EntityKind::Function &&
                     entity(selected).kind != EntityKind::Method)) {
                    fail("record method fact has invalid deleting-destructor "
                         "deallocation entity");
                }
                const DeallocationFunctionForm& form =
                    method.deleting_destructor_deallocation.form;
                if (form.is_array || form.is_placement) {
                    fail("deleting destructor selected a non-scalar usual "
                         "deallocation form");
                }
            }
            for (const PotentiallyConstructedSubobjectFact& subobject :
                 method.potentially_constructed_subobjects) {
                if (!subobject.entity.valid() || !valid(subobject.entity)) {
                    fail("record method fact has invalid potentially-constructed subobject entity");
                }
                if (!subobject.type.valid() || !valid(subobject.type.type)) {
                    fail("record method fact has invalid potentially-constructed subobject type");
                }
            }
        }
        if (facts.key_function.valid()) {
            bool found_candidate = false;
            for (const RecordMethodFact& method : facts.methods) {
                if (method.entity == facts.key_function &&
                    method.is_key_function_candidate) {
                    found_candidate = true;
                    break;
                }
            }
            if (!valid(facts.key_function) ||
                entity(facts.key_function).parent != facts.entity ||
                !found_candidate) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have an invalid key function");
            }
        }
        for (const RecordStaticDataMemberFact& member : facts.static_data_members) {
            if (member.name.valid() && !valid(member.name)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid static data member name");
            }
            if (member.type.valid() && !valid(member.type.type)) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid static data member type");
            }
            if (!valid(member.entity) || entity(member.entity).kind != EntityKind::Variable) {
                fail("record facts for " + format_entity(facts.entity) + " have invalid static data member entity");
            }
            if (valid(member.entity) && entity(member.entity).parent != facts.entity) {
                fail("static data member entity parent does not match owning record facts");
            }
            if (member.initializer_context.valid() &&
                !valid(member.initializer_context)) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have invalid static data member initializer context");
            }
            if (member.initializer_value_expression.valid() &&
                (!member.initializer_value_expression.canonical_id.valid() ||
                 !valid(member.initializer_value_expression.canonical_id))) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have non-canonical static data member initializer");
            }
            if (member.initializer_value_expression.valid() &&
                (!member.has_in_class_initializer ||
                 member.initializer_begin >= member.initializer_end)) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have inconsistent static data member initializer recipe");
            }
        }
        auto check_virtual_entity = [&](EntityId member,
                                        std::string_view role) {
            if (!member.valid() || !valid(member)) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have invalid virtual " + std::string(role));
            }
        };
        auto check_virtual_path = [&](const std::vector<EntityId>& path,
                                      std::string_view role) {
            for (EntityId step : path) {
                if (!step.valid() || !valid(step) ||
                    entity(step).kind != EntityKind::Field) {
                    fail("record facts for " + format_entity(facts.entity) +
                         " have invalid " + std::string(role) + " path");
                    break;
                }
            }
        };
        for (size_t index = 0; index < facts.virtual_subobjects.size();
             ++index) {
            const VirtualSubobjectFact& subobject =
                facts.virtual_subobjects[index];
            if (subobject.id != index) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have non-canonical virtual subobject ids");
            }
            if (!subobject.record_entity.valid() ||
                !valid(subobject.record_entity) ||
                entity(subobject.record_entity).kind != EntityKind::Record) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have invalid virtual subobject record");
            }
            if (!subobject.type.valid() || !valid(subobject.type.type)) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have invalid virtual subobject type");
            }
            check_virtual_path(subobject.storage_path,
                               "virtual subobject storage");
        }
        for (const VirtualSubobjectEdgeFact& edge :
             facts.virtual_subobject_edges) {
            if (edge.derived_subobject >= facts.virtual_subobjects.size() ||
                edge.base_subobject >= facts.virtual_subobjects.size()) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have a virtual subobject edge outside the graph");
            }
        }
        for (const VirtualOverrideEdgeFact& edge :
             facts.virtual_override_edges) {
            check_virtual_entity(edge.overriding, "overrider");
            check_virtual_entity(edge.overridden, "declaration");
            if (edge.overriding_subobject >= facts.virtual_subobjects.size() ||
                edge.overridden_subobject >= facts.virtual_subobjects.size()) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have an override edge outside the subobject graph");
            }
            check_virtual_path(edge.covariance_path, "covariant return");
        }
        for (const VirtualFinalOverriderFact& final :
             facts.virtual_final_overriders) {
            check_virtual_entity(final.virtual_declaration,
                                 "final-overrider declaration");
            if (final.declaration_subobject >=
                facts.virtual_subobjects.size()) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have a final-overrider declaration outside the graph");
            }
            if (final.final_overrider.valid()) {
                check_virtual_entity(final.final_overrider,
                                     "final overrider");
                if (final.final_subobject >= facts.virtual_subobjects.size()) {
                    fail("record facts for " + format_entity(facts.entity) +
                         " have a final overrider outside the graph");
                }
            }
            for (EntityId candidate : final.conflict_candidates) {
                check_virtual_entity(candidate,
                                     "final-overrider conflict candidate");
            }
        }
        auto check_slot = [&](const VirtualTableSlotFact& slot) {
            check_virtual_entity(slot.declaration, "slot declaration");
            check_virtual_entity(slot.final_overrider,
                                 "slot final overrider");
            if (!facts.virtual_subobjects.empty() &&
                (slot.declaration_subobject >=
                     facts.virtual_subobjects.size() ||
                 slot.final_subobject >= facts.virtual_subobjects.size())) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have a vtable slot outside the subobject graph");
            }
            check_virtual_path(slot.this_adjustment.path,
                               "vtable this-adjustment");
            check_virtual_path(slot.result_adjustment.path,
                               "vtable result-adjustment");
        };
        if (facts.primary_vtable_slot_facts.size() !=
            facts.vtable_slots.size()) {
            fail("record facts for " + format_entity(facts.entity) +
                 " have mismatched primary vtable slot facts");
        }
        for (const VirtualTableSlotFact& slot :
             facts.primary_vtable_slot_facts) {
            check_slot(slot);
        }
        for (const RecordFacts::SecondaryVtable& table :
             facts.secondary_vtables) {
            check_virtual_path(table.storage_path,
                               "secondary vtable storage");
            if (table.slot_facts.size() != table.slots.size()) {
                fail("record facts for " + format_entity(facts.entity) +
                     " have mismatched secondary vtable slot facts");
            }
            for (const VirtualTableSlotFact& slot : table.slot_facts) {
                check_slot(slot);
            }
        }
    }
    for (uint32_t i = 1; i < switch_facts_.size(); ++i) {
        const SwitchFact& sw = switch_facts_[i];
        std::string label = "switch #" + std::to_string(i);
        if (!valid(sw.condition.inst)) {
            fail(label + " has invalid condition value");
        } else if (sw.condition_type.valid() &&
                   operand_result_type(sw.condition) != sw.condition_type.type) {
            fail(label + " condition type does not match condition value");
        }
        if (sw.condition_type.valid() && !valid(sw.condition_type.type)) {
            fail(label + " has invalid condition type");
        }
        if (!valid(sw.dispatch_block)) {
            fail(label + " has invalid dispatch block");
        }
        if (!valid(sw.default_block)) {
            fail(label + " has invalid default block");
        }
        if (!valid(sw.end_block)) {
            fail(label + " has invalid end block");
        }
        for (size_t case_index = 0; case_index < sw.cases.size(); ++case_index) {
            const SwitchCaseRange& case_fact = sw.cases[case_index];
            if (case_fact.high < case_fact.low) {
                fail(label + " has empty case range");
            }
            if (!valid(case_fact.target)) {
                fail(label + " has invalid case target");
            }
            for (size_t prior_index = 0; prior_index < case_index; ++prior_index) {
                const SwitchCaseRange& prior = sw.cases[prior_index];
                if (case_fact.low <= prior.high && prior.low <= case_fact.high) {
                    fail(label + " has overlapping case ranges");
                    break;
                }
            }
        }
    }

    std::vector<FunctionId> block_owners(blocks_.size());
    std::vector<FunctionId> inst_owners(insts_.size());
    for (uint32_t i = 1; i < functions_.size(); ++i) {
        FunctionId owner{i, function_generations_[i]};
        const Function& fn = functions_[i];
        for (const FunctionParameter& parameter : fn.parameters) {
            if (valid(parameter.value.inst)) {
                FunctionId& prior = inst_owners[parameter.value.inst.index];
                if (prior.valid() && prior != owner) {
                    fail("instruction belongs to more than one function");
                } else {
                    prior = owner;
                }
            }
        }
        for (BlockId block_id : fn.blocks) {
            if (!valid(block_id)) {
                continue;
            }
            FunctionId& block_owner = block_owners[block_id.index];
            if (block_owner.valid() && block_owner != owner) {
                fail("block belongs to more than one function");
            } else {
                block_owner = owner;
            }
            const Block& body_block = block(block_id);
            auto claim_inst = [&](InstId inst_id) {
                if (!valid(inst_id)) {
                    return;
                }
                FunctionId& prior = inst_owners[inst_id.index];
                if (prior.valid() && prior != owner) {
                    fail("instruction belongs to more than one function");
                } else {
                    prior = owner;
                }
            };
            for (InstId parameter : body_block.parameters) {
                claim_inst(parameter);
            }
            for (InstId instruction : body_block.instructions) {
                claim_inst(instruction);
            }
        }
    }

    auto check_function_value = [&](FunctionId owner,
                                    const Operand& operand,
                                    std::string_view consumer) {
        if (operand.kind != OperandKind::Value) {
            return;
        }
        const auto* value = std::get_if<ValueRef>(&operand.data);
        if (!value || !valid(value->inst)) {
            return;
        }
        FunctionId source = inst_owners[value->inst.index];
        if (source.valid() && source != owner) {
            fail(std::string(consumer) +
                 " consumes a value owned by another function");
        }
    };
    auto check_function_target = [&](FunctionId owner,
                                     BlockId target,
                                     std::string_view edge) {
        if (!valid(target)) {
            return;
        }
        FunctionId target_owner = block_owners[target.index];
        if (target_owner.valid() && target_owner != owner) {
            fail(std::string(edge) + " targets a block owned by another"
                 " function (fn #" + std::to_string(owner.index) +
                 " -> block #" + std::to_string(target.index) +
                 " of fn #" + std::to_string(target_owner.index) + ")");
        }
    };
    for (uint32_t i = 1; i < functions_.size(); ++i) {
        FunctionId owner{i, function_generations_[i]};
        const Function& fn = functions_[i];
        for (BlockId block_id : fn.blocks) {
            if (!valid(block_id)) {
                continue;
            }
            const Block& body_block = block(block_id);
            check_function_target(owner, body_block.unwind_target,
                                  "unwind edge");
            for (InstId instruction_id : body_block.instructions) {
                if (!valid(instruction_id)) {
                    continue;
                }
                const Inst& instruction = inst(instruction_id);
                for (const Operand& operand : operands(instruction.operands)) {
                    check_function_value(owner, operand, "instruction");
                }
                if (instruction.kind == InstKind::LocalPlace) {
                    for (const Operand& operand : operands(instruction.operands)) {
                        const auto* local = std::get_if<EntityId>(&operand.data);
                        if (!local || !valid(*local)) {
                            continue;
                        }
                        EntityId semantic_owner = entity(*local).owning_function;
                        if (semantic_owner.valid() &&
                            semantic_owner != fn.entity) {
                            fail("local_place names an entity owned by another "
                                 "function");
                        }
                    }
                }
            }
            for (const Operand& operand : operands(body_block.terminator.operands)) {
                check_function_value(owner, operand, "terminator");
            }
            check_function_target(owner, body_block.terminator.target,
                                  "control-flow edge");
            check_function_target(owner, body_block.terminator.false_target,
                                  "control-flow edge");
            if (body_block.terminator.kind == TerminatorKind::Switch) {
                if (const auto* switch_payload =
                        std::get_if<SwitchTerminatorPayload>(
                            &payload(body_block.terminator.payload_index))) {
                    for (const SwitchCaseRange& case_range :
                         switch_payload->cases) {
                        check_function_target(owner, case_range.target,
                                              "switch edge");
                    }
                }
            }
        }
    }

    for (uint32_t i = 1; i < insts_.size(); ++i) {
        ok = verify_inst(InstId{i, inst_generations_[i]}, err) && ok;
    }
    for (uint32_t i = 1; i < functions_.size(); ++i) {
        ok = verify_function(functions_[i], FunctionId{i, function_generations_[i]}, err) && ok;
    }
    return ok;
}

void File::dump(std::ostream& out) const {
    out << "CIR\n";
    if (module_units_.size() > 1) {
        out << "module_units:\n";
        for (uint32_t i = 1; i < module_units_.size(); ++i) {
            const ModuleUnitFact& unit = module_units_[i];
            const char* kind_name = "primary-interface";
            switch (unit.kind) {
                case ModuleUnitFact::Kind::PrimaryInterface:
                    kind_name = "primary-interface";
                    break;
                case ModuleUnitFact::Kind::InterfacePartition:
                    kind_name = "interface-partition";
                    break;
                case ModuleUnitFact::Kind::ImplementationPartition:
                    kind_name = "implementation-partition";
                    break;
                case ModuleUnitFact::Kind::Implementation:
                    kind_name = "implementation";
                    break;
                case ModuleUnitFact::Kind::HeaderUnit:
                    kind_name = "header-unit";
                    break;
            }
            out << "  unit #" << i << ' ' << kind_name << " '"
                << name(unit.module_name) << '\'';
            if (unit.partition_name.valid()) {
                out << " partition '" << name(unit.partition_name) << '\'';
            }
            out << '\n';
        }
    }
    if (decl_contexts_.size() > 1) {
        out << "contexts:\n";
        for (uint32_t i = 1; i < decl_contexts_.size(); ++i) {
            DeclContextId context_id{i, decl_context_generations_[i]};
            const DeclContext& context = decl_contexts_[i];
            out << "  context #" << context_id.index << ' '
                << decl_context_kind_name(context.kind);
            if (context.owner.valid()) {
                out << " owner=" << format_entity(context.owner);
            }
            if (context.parent.valid()) {
                out << " parent=#" << context.parent.index;
            }
            out << '\n';
            for (BindingId binding_id : context.bindings) {
                if (!valid(binding_id)) {
                    continue;
                }
                const Binding& b = binding(binding_id);
                out << "    " << lookup_namespace_name(b.lookup_namespace)
                    << ' ' << (b.name.valid() ? name(b.name) : std::string("<unnamed>"));
                if (!b.entities.empty()) {
                    out << " ->";
                    for (EntityId entity_id : b.entities) {
                        out << ' ' << format_entity(entity_id);
                    }
                }
                if (b.type.valid()) {
                    out << " : " << format_type(b.type);
                }
                if (b.place.valid()) {
                    out << " place=" << format_inst(b.place);
                }
                if (b.is_type_name) {
                    out << " typename";
                }
                if (b.is_template_name) {
                    out << " template";
                }
                if (b.is_definition) {
                    out << " definition";
                }
                out << '\n';
            }
        }
    }
    if (!structured_binding_facts_.empty()) {
        out << "structured_bindings:\n";
        std::vector<const StructuredBindingFact*> bindings;
        bindings.reserve(structured_binding_facts_.size());
        for (const auto& [key, fact] : structured_binding_facts_) {
            (void)key;
            bindings.push_back(&fact);
        }
        std::sort(bindings.begin(), bindings.end(),
                  [](const StructuredBindingFact* lhs,
                     const StructuredBindingFact* rhs) {
                      return lhs->backing.index < rhs->backing.index;
                  });
        for (const StructuredBindingFact* fact : bindings) {
            out << "  " << format_entity(fact->backing)
                << " strategy="
                << structured_binding_strategy_name(fact->strategy)
                << " type=" << format_type(fact->decomposed_type)
                << " names=[";
            for (size_t index = 0; index < fact->source_names.size(); ++index) {
                if (index != 0) {
                    out << ", ";
                }
                if (fact->has_pack && index == fact->pack_position) {
                    out << "...";
                }
                out << name(fact->source_names[index]);
            }
            out << ']';
            if (fact->is_condition) {
                out << " condition";
            }
            if (fact->is_dependent) {
                out << " dependent";
            }
            out << '\n';
            for (const StructuredBindingProjectionFact& projection :
                 fact->projections) {
                out << "    #" << projection.index << ' '
                    << format_entity(projection.binding)
                    << ": " << format_type(projection.type)
                    << " refers="
                    << format_type(projection.referenced_type);
                if (projection.holder.valid()) {
                    out << " holder=" << format_entity(projection.holder);
                }
                if (projection.member.valid()) {
                    out << " member=" << format_entity(projection.member);
                }
                if (!projection.base_path.empty()) {
                    out << " base_path=";
                    for (EntityId base : projection.base_path) {
                        out << format_entity(base);
                    }
                }
                if (projection.is_bitfield) {
                    out << " bitfield";
                }
                if (projection.is_pack_element) {
                    out << " pack_element";
                }
                if (projection.is_dependent) {
                    out << " dependent";
                }
                out << '\n';
            }
        }
    }
    if (!defaulted_comparison_facts_.empty()) {
        out << "defaulted_comparisons:\n";
        std::vector<const DefaultedComparisonFact*> comparisons;
        comparisons.reserve(defaulted_comparison_facts_.size());
        for (const auto& [key, comparison] :
             defaulted_comparison_facts_) {
            (void)key;
            comparisons.push_back(&comparison);
        }
        std::sort(comparisons.begin(), comparisons.end(),
                  [](const DefaultedComparisonFact* lhs,
                     const DefaultedComparisonFact* rhs) {
                      return lhs->function.index < rhs->function.index;
                  });
        auto comparison_kind_name = [](DefaultedComparisonKind kind) {
            switch (kind) {
                case DefaultedComparisonKind::Equal: return "equal";
                case DefaultedComparisonKind::NotEqual: return "not_equal";
                case DefaultedComparisonKind::Less: return "less";
                case DefaultedComparisonKind::LessEqual: return "less_equal";
                case DefaultedComparisonKind::Greater: return "greater";
                case DefaultedComparisonKind::GreaterEqual:
                    return "greater_equal";
                case DefaultedComparisonKind::ThreeWay: return "three_way";
            }
            return "unknown";
        };
        for (const DefaultedComparisonFact* comparison : comparisons) {
            out << "  " << format_entity(comparison->function)
                << " owner=" << format_entity(comparison->owner_record)
                << " kind=" << comparison_kind_name(comparison->kind);
            if (comparison->result_type.type.valid()) {
                out << " result=" << format_type(comparison->result_type);
            }
            if (comparison->is_implicit_equality) {
                out << " implicit_equality";
                if (comparison->implicit_equality_origin.valid()) {
                    out << " origin="
                        << format_entity(
                               comparison->implicit_equality_origin);
                }
            }
            if (comparison->is_deleted) {
                out << " deleted";
                if (!comparison->deletion_reason.empty()) {
                    out << " reason='" << comparison->deletion_reason
                        << "'";
                }
            }
            out << '\n';
            for (const ComparisonSubobjectFact& subobject :
                 comparison->subobjects) {
                out << "    "
                    << (subobject.kind ==
                                ComparisonSubobjectKind::DirectBase
                            ? "base "
                            : "field ")
                    << format_entity(subobject.entity) << ": "
                    << format_type(subobject.type);
                if (!subobject.array_extents.empty()) {
                    out << " array=";
                    for (size_t extent : subobject.array_extents) {
                        out << '[' << extent << ']';
                    }
                    out << " leaf="
                        << format_type(subobject.array_leaf_type);
                }
                out << '\n';
            }
        }
    }
    if (!record_facts_.empty()) {
        out << "records:\n";
        std::vector<const RecordFacts*> records;
        records.reserve(record_facts_.size());
        for (const auto& [key, facts] : record_facts_) {
            (void)key;
            records.push_back(&facts);
        }
        std::sort(records.begin(), records.end(), [](const RecordFacts* lhs, const RecordFacts* rhs) {
            return lhs->entity.index < rhs->entity.index;
        });
        for (const RecordFacts* facts : records) {
            out << "  " << record_kind_name(facts->kind) << ' '
                << format_entity(facts->entity);
            if (facts->is_incomplete) {
                out << " incomplete";
            } else {
                out << " size=" << ((facts->size_bits + 7) / 8)
                    << " align=" << facts->alignment;
            }
            if (facts->is_packed) {
                out << " packed";
            }
            if (facts->pack_alignment > 0) {
                out << " pack=" << facts->pack_alignment;
            }
            if (facts->requested_alignment > 0) {
                out << " requested_align=" << facts->requested_alignment;
            }

            if (facts->is_literal_class_type) {
                out << " literal_class";
            }
            if (facts->is_consteval_only == ClassPropertyState::True) {
                out << " consteval_only";
            } else if (facts->is_consteval_only ==
                       ClassPropertyState::Dependent) {
                out << " consteval_only=dependent";
            }
            if (facts->is_empty == ClassPropertyState::True) {
                out << " empty";
            } else if (facts->is_empty == ClassPropertyState::Dependent) {
                out << " empty=dependent";
            }
            out << '\n';
            for (const RecordFieldFact& field : facts->fields) {
                out << "    field " << format_entity(field.entity)
                    << ": " << format_type(field.type)
                    << " offset=" << field.offset;
                if (field.is_flexible_array_member) {
                    out << " flexible";
                }
                if (field.is_bitfield) {
                    out << " bits=" << field.bit_offset << ':' << field.bit_width
                        << " storage=" << field.storage_size;
                    if (field.bit_width_is_dependent) {
                        out << " dependent-width";
                    }
                }
                if (field.forced_alignment > 0) {
                    out << " forced_align=" << field.forced_alignment;
                }
                if (field.is_no_unique_address) {
                    out << " no_unique_address";
                }
                if (field.is_potentially_overlapping) {
                    out << " potentially_overlapping";
                }
                if (field.subobject_size == SubobjectSizeKind::Zero) {
                    out << " zero_size";
                } else if (field.subobject_size ==
                           SubobjectSizeKind::Dependent) {
                    out << " size=dependent";
                }
                if (field.declared_access != RecordMemberAccess::Public) {
                    out << ' ' << record_member_access_name(field.declared_access);
                }
                out << '\n';
            }
            for (const RecordStaticDataMemberFact& member : facts->static_data_members) {
                out << "    static " << format_entity(member.entity)
                    << ": " << format_type(member.type);
                if (member.declared_access != RecordMemberAccess::Public) {
                    out << ' ' << record_member_access_name(member.declared_access);
                }
                if (member.is_constexpr) {
                    out << " constexpr";
                }
                if (member.is_consteval) {
                    out << " consteval";
                }
                if (member.is_inline) {
                    out << " inline";
                }
                out << '\n';
            }
            for (const RecordMethodFact& method : facts->methods) {
                out << "    method " << format_entity(method.entity)
                    << ": " << format_type(method.type);
                if (method.declared_access != RecordMemberAccess::Public) {
                    out << ' ' << record_member_access_name(method.declared_access);
                }
                if (method.is_static) {
                    out << " static";
                }
                if (method.is_virtual) {
                    out << " virtual";
                }
                if (method.is_deleted) {
                    out << " deleted";
                }
                if (method.is_defaulted) {
                    out << " defaulted";
                }
                if (method.is_pure) {
                    out << " pure";
                }
                if (method.is_constexpr) {
                    out << " constexpr";
                }
                if (method.is_consteval) {
                    out << " consteval";
                }
                if (method.is_explicit) {
                    out << " explicit";
                }
                if (method.deleting_destructor_deallocation.valid()) {
                    const DeallocationFunctionSelectionFact& selected =
                        method.deleting_destructor_deallocation;
                    out << " delete=" << format_entity(selected.entity);
                    if (selected.form.is_sized) {
                        out << ":sized";
                    }
                    if (selected.form.is_aligned) {
                        out << ":aligned";
                    }
                    if (selected.form.is_destroying) {
                        out << ":destroying";
                    }
                }
                if (method.constructor_delegation) {
                    const ConstructorDelegationFact& delegation =
                        *method.constructor_delegation;
                    out << " delegates=";
                    if (delegation.resolved()) {
                        out << format_entity(delegation.target_constructor);
                    } else {
                        out << "dependent";
                    }
                    out << (delegation.initialization_kind ==
                                    ConstructorDelegationInitializationKind::Braced
                                ? ":braced"
                                : ":parenthesized");
                }
                out << '\n';
            }
            for (const VirtualSubobjectFact& subobject :
                 facts->virtual_subobjects) {
                out << "    virtual subobject #" << subobject.id << ' '
                    << format_type(subobject.type)
                    << " offset=" << subobject.static_offset_bytes;
                if (subobject.is_virtual) {
                    out << " shared";
                }
                out << '\n';
            }
            for (const VirtualOverrideEdgeFact& edge :
                 facts->virtual_override_edges) {
                out << "    override " << format_entity(edge.overriding)
                    << "@#" << edge.overriding_subobject << " -> "
                    << format_entity(edge.overridden) << "@#"
                    << edge.overridden_subobject;
                switch (edge.return_relation) {
                    case VirtualReturnRelation::Identical:
                        out << " return=identical";
                        break;
                    case VirtualReturnRelation::Covariant:
                        out << " return=covariant";
                        break;
                    case VirtualReturnRelation::Invalid:
                        out << " return=invalid";
                        break;
                    case VirtualReturnRelation::Dependent:
                        out << " return=dependent";
                        break;
                }
                out << '\n';
            }
            for (const VirtualFinalOverriderFact& final :
                 facts->virtual_final_overriders) {
                out << "    final "
                    << format_entity(final.virtual_declaration) << "@#"
                    << final.declaration_subobject << " -> ";
                if (final.final_overrider.valid()) {
                    out << format_entity(final.final_overrider) << "@#"
                        << final.final_subobject;
                } else {
                    out << "conflict(" << final.conflict_candidates.size()
                        << ')';
                }
                out << '\n';
            }
            for (const RecordClassFriendGrant& grant :
                 facts->class_friends) {
                out << "    friend class ";
                switch (grant.kind) {
                    case RecordClassFriendGrantKind::ExactRecord:
                        out << "exact " << format_entity(grant.entity);
                        break;
                    case RecordClassFriendGrantKind::PrimaryClassTemplate:
                        out << "template " << format_entity(grant.entity);
                        break;
                    case RecordClassFriendGrantKind::DependentRecipe:
                        if (grant.recipe_kind ==
                            RecordClassFriendRecipeKind::
                                MemberOfClassTemplate) {
                            out << "dependent-member "
                                << format_type(grant.type_pattern) << "::"
                                << (grant.member_name.valid()
                                        ? name(grant.member_name)
                                        : std::string_view("<invalid>"));
                        } else {
                            out << "dependent "
                                << format_type(grant.type_pattern);
                            if (grant.is_pack_expansion) {
                                out << "...";
                            }
                        }
                        break;
                }
                out << '\n';
            }
            for (const RecordFunctionFriendGrant& grant :
                 facts->function_friends) {
                out << "    friend function ";
                switch (grant.kind) {
                    case RecordFunctionFriendGrantKind::ExactFunction:
                        out << "exact " << format_entity(grant.entity);
                        break;
                    case RecordFunctionFriendGrantKind::
                            PrimaryFunctionTemplate:
                        out << "template " << format_entity(grant.entity);
                        break;
                    case RecordFunctionFriendGrantKind::
                            FunctionTemplateSpecialization:
                        out << "specialization "
                            << format_entity(grant.entity) << '<'
                            << grant.arguments.size() << " args>";
                        break;
                    case RecordFunctionFriendGrantKind::
                            DependentMemberFunction:
                        out << "dependent-member "
                            << format_type(grant.qualifier_pattern) << "::"
                            << (grant.member_name.valid()
                                    ? name(grant.member_name)
                                    : std::string_view("<invalid>"));
                        break;
                    case RecordFunctionFriendGrantKind::
                            DependentMemberFunctionTemplate:
                        out << "dependent-member-template "
                            << format_type(grant.qualifier_pattern) << "::"
                            << (grant.member_name.valid()
                                    ? name(grant.member_name)
                                    : std::string_view("<invalid>"));
                        break;
                }
                out << '\n';
            }
        }
    }
    if (!objc_interface_facts_.empty()) {
        out << "objc:\n";
        std::vector<const ObjCInterfaceFacts*> interfaces;
        interfaces.reserve(objc_interface_facts_.size());
        for (const auto& [fact_key, facts] : objc_interface_facts_) {
            (void)fact_key;
            interfaces.push_back(&facts);
        }
        std::sort(interfaces.begin(), interfaces.end(),
                  [](const ObjCInterfaceFacts* lhs,
                     const ObjCInterfaceFacts* rhs) {
                      return lhs->entity.index < rhs->entity.index;
                  });
        for (const ObjCInterfaceFacts* facts : interfaces) {
            out << "  interface " << name(facts->name);
            if (facts->super_class.valid()) {
                const ObjCInterfaceFacts* super =
                    objc_interface_facts(facts->super_class);
                out << " : " << (super ? name(super->name) : "<invalid>");
            }
            if (facts->is_forward_only) {
                out << " forward";
            }
            if (facts->implementation.valid()) {
                out << " implemented";
            }
            if (facts->layout_computed) {
                out << " start=" << facts->instance_start_bytes
                    << " size=" << facts->instance_size_bytes;
            }
            out << '\n';
            for (const ObjCIvarFact& ivar : facts->ivars) {
                out << "    ivar @" << name(ivar.name) << ": "
                    << format_type(ivar.type)
                    << " offset=" << ivar.offset_bytes << '\n';
            }
            auto dump_methods = [&](const std::vector<ObjCMethodFact>& list,
                                    char sign) {
                for (const ObjCMethodFact& method : list) {
                    out << "    method " << sign
                        << selector_spelling(method.selector) << ": "
                        << format_type(method.function_type);
                    if (method.definition.valid()) {
                        out << " defined";
                    }
                    out << '\n';
                }
            };
            dump_methods(facts->instance_methods, '-');
            dump_methods(facts->class_methods, '+');
        }
    }
    if (switch_facts_.size() > 1) {
        out << "switches:\n";
        for (uint32_t i = 1; i < switch_facts_.size(); ++i) {
            const SwitchFact& sw = switch_facts_[i];
            out << "  switch #" << i
                << " cond=" << format_value(sw.condition);
            if (sw.condition_type.valid()) {
                out << " : " << format_type(sw.condition_type);
            }
            out << " dispatch=^" << name(block(sw.dispatch_block).name)
                << " default=^" << name(block(sw.default_block).name)
                << " end=^" << name(block(sw.end_block).name)
                << '\n';
            for (const SwitchCaseRange& case_fact : sw.cases) {
                out << "    case " << case_fact.low;
                if (case_fact.low != case_fact.high) {
                    out << " ... " << case_fact.high;
                }
                out << " -> ^" << name(block(case_fact.target).name)
                    << '\n';
            }
        }
    }
    if (functions_.size() <= 1) {
        out << "<no functions>\n";
    }

    for (uint32_t i = 1; i < functions_.size(); ++i) {
        const Function& fn = functions_[i];
        const Entity& entity_record = entity(fn.entity);
        out << "fn " << format_entity(fn.entity) << '(';
        for (size_t p = 0; p < fn.parameters.size(); ++p) {
            if (p > 0) out << ", ";
            InstId parameter_inst = fn.parameters[p].value.inst;
            out << format_value(fn.parameters[p].value) << ": "
                << format_type(inst(parameter_inst).result_type);
        }
        out << ") -> " << format_type(fn.result_type) << " {\n";

        for (BlockId block_id : fn.blocks) {
            const Block& b = block(block_id);
            out << '^' << (b.name.valid() ? name(b.name) : ("block" + std::to_string(block_id.index)));
            if (!b.parameters.empty()) {
                out << '(';
                for (size_t p = 0; p < b.parameters.size(); ++p) {
                    if (p > 0) out << ", ";
                    out << format_inst(b.parameters[p]) << ": "
                        << format_type(inst(b.parameters[p]).result_type);
                }
                out << ')';
            }
            if (valid(b.unwind_target)) {
                const Block& pad = block(b.unwind_target);
                out << " unwind ^"
                    << (pad.name.valid()
                            ? name(pad.name)
                            : ("block" + std::to_string(b.unwind_target.index)));
            }
            out << ":\n";
            for (InstId instruction_id : b.instructions) {
                const Inst& instruction = inst(instruction_id);
                if (instruction.kind == InstKind::Param) {
                    continue;
                }
                const InstPayload& data = payload(instruction.payload_index);
                out << "  ";
                if (instruction.result_type.valid() && inst_has_result(instruction.kind)) {
                    out << format_inst(instruction_id) << ": "
                        << format_type(instruction.result_type) << " = ";
                }
                out << inst_mnemonic(instruction.kind);

                std::vector<Operand> ops = operands(instruction.operands);
                std::vector<ValueRef> value_ops = value_operands(instruction.operands);
                auto entity_at = [&](size_t index) -> EntityId {
                    if (index >= ops.size()) return {};
                    const auto* entity_operand = std::get_if<EntityId>(&ops[index].data);
                    return entity_operand ? *entity_operand : EntityId{};
                };
                auto type_at = [&](size_t index) -> TypeRef {
                    if (index >= ops.size()) return {};
                    const auto* type_operand = std::get_if<TypeRef>(&ops[index].data);
                    return type_operand ? *type_operand : TypeRef{};
                };
                auto name_at = [&](size_t index) -> NameId {
                    if (index >= ops.size()) return {};
                    const auto* name_operand = std::get_if<NameId>(&ops[index].data);
                    return name_operand ? *name_operand : NameId{};
                };

                switch (instruction.kind) {
                    case InstKind::IntegerLiteral: {
                        const auto* literal = std::get_if<LiteralPayload>(&data);
                        const auto* value = literal
                            ? std::get_if<IntegerValue>(&literal->value)
                            : nullptr;
                        out << ' ' << (value ? value->decimal() : "<invalid>");
                        if (literal && !literal->spelling.empty()) {
                            out << " ; " << literal->spelling;
                        }
                        break;
                    }
                    case InstKind::BooleanLiteral: {
                        const auto* literal = std::get_if<LiteralPayload>(&data);
                        const auto* value =
                            literal ? std::get_if<bool>(&literal->value) : nullptr;
                        out << ' ' << (value && *value ? "true" : "false");
                        if (literal && !literal->spelling.empty()) {
                            out << " ; " << literal->spelling;
                        }
                        break;
                    }
                    case InstKind::NullptrLiteral: {
                        const auto* literal = std::get_if<LiteralPayload>(&data);
                        out << " nullptr";
                        if (literal && !literal->spelling.empty() &&
                            literal->spelling != "nullptr") {
                            out << " ; " << literal->spelling;
                        }
                        break;
                    }
                    case InstKind::FloatingLiteral: {
                        const auto* literal = std::get_if<LiteralPayload>(&data);
                        const auto* value =
                            literal ? std::get_if<FloatingValue>(&literal->value) : nullptr;
                        if (value) {
                            out << ' ' << floating::display(*value)
                                << " [0x" << floating::bit_pattern_hex(*value)
                                << ']';
                        } else {
                            out << " <invalid>";
                        }
                        if (literal && !literal->spelling.empty()) {
                            out << " ; " << literal->spelling;
                        }
                        break;
                    }
                    case InstKind::CharacterLiteral: {
                        const auto* literal = std::get_if<LiteralPayload>(&data);
                        const auto* bytes =
                            literal ? std::get_if<LiteralByteArray>(&literal->value) : nullptr;
                        out << ' ' << (bytes ? std::to_string(integer_from_bytes(*bytes)) : "<invalid>");
                        if (bytes && !bytes->empty()) {
                            out << " \"";
                            dump_escaped_bytes(out, *bytes);
                            out << '"';
                        }
                        if (literal && !literal->spelling.empty()) {
                            out << " ; " << literal->spelling;
                        }
                        break;
                    }
                    case InstKind::StringLiteral: {
                        const auto* literal = std::get_if<LiteralPayload>(&data);
                        const auto* bytes =
                            literal ? std::get_if<LiteralByteArray>(&literal->value) : nullptr;
                        out << " \"";
                        if (bytes) {
                            dump_escaped_bytes(out, *bytes);
                        }
                        out << '"';
                        if (literal && !literal->spelling.empty()) {
                            out << " ; " << literal->spelling;
                        }
                        break;
                    }
                    case InstKind::NameRef:
                        if (NameId operand_name = name_at(0); valid(operand_name)) {
                            out << ' ' << name(operand_name);
                        }
                        break;
                    case InstKind::LocalPlace:
                    case InstKind::GlobalPlace:
                        out << ' ' << format_entity(entity_at(0));
                        break;
                    case InstKind::FunctionToPointer:
                    case InstKind::MemberPointerValue:
                        out << ' ' << format_entity(entity_at(0));
                        break;
                    case InstKind::LabelAddress:
                        if (const auto* label = std::get_if<LabelAddressPayload>(&data)) {
                            out << ' ';
                            if (valid(label->name)) {
                                out << name(label->name);
                            } else {
                                out << "<invalid>";
                            }
                            if (valid(label->target) && block(label->target).name.valid()) {
                                out << " -> ^" << name(block(label->target).name);
                            }
                        }
                        break;
                    case InstKind::SizeofType:
                    case InstKind::AlignofType:
                        out << ' ' << format_type(type_at(0));
                        break;
                    case InstKind::UnaryOp:
                        if (const auto* descriptor = std::get_if<UnaryOpDescriptor>(&data)) {
                            out << ' ' << unary_op_spelling(descriptor->op);
                        } else {
                            out << " <invalid>";
                        }
                        break;
                    case InstKind::BinaryOp:
                        if (const auto* descriptor = std::get_if<BinaryOpDescriptor>(&data)) {
                            out << ' ' << binary_op_spelling(descriptor->op);
                        } else {
                            out << " <invalid>";
                        }
                        break;
                    case InstKind::Cast:
                        out << " to " << format_type(type_at(0));
                        if (const auto* cast = std::get_if<CastPayload>(&data);
                            cast && !cast->kind.empty()) {
                            out << " kind=" << cast->kind;
                        }
                        break;
                    case InstKind::Call:
                        if (EntityId callee = entity_at(0); valid(callee)) {
                            out << ' ' << format_entity(callee);
                        } else if (const auto* call =
                                       std::get_if<CallPayload>(&data);
                                   call &&
                                   valid(call->virtual_declaration)) {
                            out << " virtual "
                                << format_entity(
                                       call->virtual_declaration);
                        }
                        break;
                    case InstKind::VaArg:
                        out << ' ' << format_type(type_at(0));
                        break;
                    case InstKind::BuiltinCall:
                        if (const auto* builtin = std::get_if<BuiltinCallPayload>(&data)) {
                            out << ' ';
                            if (!builtin->name.empty()) {
                                out << builtin->name;
                            } else {
                                out << "builtin#" << static_cast<int>(builtin->kind);
                            }
                            if (builtin->type_operand.valid()) {
                                out << " type=" << format_type(builtin->type_operand);
                            }
                            if (!builtin->integer_operands.empty()) {
                                out << " ints=[";
                                for (size_t int_index = 0;
                                     int_index < builtin->integer_operands.size();
                                     ++int_index) {
                                    if (int_index > 0) out << ", ";
                                    out << builtin->integer_operands[int_index];
                                }
                                out << ']';
                            }
                        }
                        break;
                    case InstKind::InlineAsm:
                        if (const auto* asm_ref = std::get_if<InlineAsmPayloadRef>(&data);
                            asm_ref && valid(asm_ref->payload)) {
                            const InlineAsmPayload& asm_payload =
                                inline_asm_payload(asm_ref->payload);
                            out << " \"";
                            dump_escaped_string(out, asm_payload.asm_string);
                            out << "\"";
                            if (!asm_payload.constraints.empty()) {
                                out << " constraints=\"";
                                dump_escaped_string(out, asm_payload.constraints);
                                out << "\"";
                            }
                            if (!asm_payload.outputs.empty()) {
                                out << " outputs=" << asm_payload.outputs.size();
                            }
                            if (!asm_payload.inputs.empty()) {
                                out << " inputs=" << asm_payload.inputs.size();
                            }
                            if (asm_payload.has_side_effects) {
                                out << " side_effects";
                            }
                        }
                        break;
                    case InstKind::DependentCall:
                        if (NameId operand_name = name_at(0); valid(operand_name)) {
                            out << ' ' << name(operand_name);
                        }
                        break;
                    case InstKind::FieldAddr:
                        out << ' ' << format_entity(entity_at(1));
                        break;
                    case InstKind::ConstructInPlace:
                        out << ' ' << format_entity(entity_at(1));
                        break;
                    case InstKind::Destroy:
                        if (EntityId destructor = entity_at(1); valid(destructor)) {
                            out << ' ' << format_entity(destructor);
                        }
                        break;
                    case InstKind::Error:
                        if (const auto* error = std::get_if<ErrorPayload>(&data);
                            error && !error->message.empty()) {
                            out << ' ' << error->message;
                        }
                        break;
                    case InstKind::DependentRegion:
                        if (const auto* hole =
                                std::get_if<DependentRegionPayload>(&data)) {
                            out << " hole#" << hole->hole;
                            if (!hole->display.empty()) {
                                out << " ; " << hole->display;
                            }
                        }
                        break;
                    case InstKind::EhLandingPad:
                        if (const auto* pad =
                                std::get_if<EhLandingPadPayload>(&data)) {
                            out << " [";
                            bool first = true;
                            for (EntityId clause : pad->clause_typeinfos) {
                                if (!first) out << ", ";
                                out << format_entity(clause);
                                first = false;
                            }
                            if (pad->has_catch_all) {
                                if (!first) out << ", ";
                                out << "catch_all";
                                first = false;
                            }
                            out << ']';
                            if (pad->is_cleanup) {
                                out << " cleanup";
                            }
                        }
                        break;
                    case InstKind::EhTypeId:
                        out << ' ' << format_entity(entity_at(0));
                        break;
                    default:
                        break;
                }

                if (!value_ops.empty()) {
                    out << " (";
                    for (size_t op_index = 0; op_index < value_ops.size(); ++op_index) {
                        if (op_index > 0) out << ", ";
                        out << format_value(value_ops[op_index]);
                    }
                    out << ')';
                }
                if (instruction.result_object_entity.valid()) {
                    out << " ; result_object="
                        << format_entity(instruction.result_object_entity);
                }
                if (instruction.runtime_elided_object_operation) {
                    out << " ; runtime_elided";
                }
                if (instruction.place_fact.valid() && valid(instruction.place_fact)) {
                    const PlaceFact& fact = place_fact(instruction.place_fact);
                    bool print_fact =
                        fact.object_type.memory_space != MemorySpace::Default ||
                        !fact.addressable ||
                        !fact.modifiable;
                    if (print_fact) {
                        out << " ; place";
                        if (fact.object_type.memory_space != MemorySpace::Default) {
                            out << " memory=" << memory_space_name(fact.object_type.memory_space);
                        }
                        if (fact.storage_duration != StorageDuration::Unknown) {
                            out << " storage=" << storage_duration_name(fact.storage_duration);
                        }
                        if (!fact.addressable) out << " nonaddressable";
                        if (!fact.modifiable) out << " readonly";
                    }
                }
                out << '\n';
            }

            std::vector<ValueRef> term_ops = value_operands(b.terminator.operands);
            out << "  ";
            switch (b.terminator.kind) {
                case TerminatorKind::Return:
                    out << "return";
                    if (!term_ops.empty()) out << ' ' << format_value(term_ops[0]);
                    break;
                case TerminatorKind::Branch:
                    out << "branch ^" << name(block(b.terminator.target).name);
                    break;
                case TerminatorKind::CondBranch:
                    out << "cond_branch";
                    if (!term_ops.empty()) out << ' ' << format_value(term_ops[0]);
                    out << ", ^" << name(block(b.terminator.target).name);
                    out << ", ^" << name(block(b.terminator.false_target).name);
                    break;
                case TerminatorKind::Switch:
                    out << "switch";
                    if (!term_ops.empty()) out << ' ' << format_value(term_ops[0]);
                    out << ", default ^" << name(block(b.terminator.target).name);
                    if (const auto* switch_payload =
                            std::get_if<SwitchTerminatorPayload>(
                                &payload(b.terminator.payload_index))) {
                        for (const SwitchCaseRange& case_range : switch_payload->cases) {
                            out << ", case " << case_range.low;
                            if (case_range.low != case_range.high) {
                                out << " ... " << case_range.high;
                            }
                            out << " -> ^" << name(block(case_range.target).name);
                        }
                    }
                    break;
                case TerminatorKind::IndirectBranch:
                    out << "indirect_branch";
                    if (!term_ops.empty()) out << ' ' << format_value(term_ops[0]);
                    break;
                case TerminatorKind::AsmGoto:
                    out << "asm_goto";
                    if (const auto* asm_ref =
                            std::get_if<InlineAsmPayloadRef>(&payload(b.terminator.payload_index));
                        asm_ref && valid(asm_ref->payload)) {
                        const InlineAsmPayload& asm_payload =
                            inline_asm_payload(asm_ref->payload);
                        out << " \"";
                        dump_escaped_string(out, asm_payload.asm_string);
                        out << "\"";
                        if (!asm_payload.constraints.empty()) {
                            out << " constraints=\"";
                            dump_escaped_string(out, asm_payload.constraints);
                            out << "\"";
                        }
                        if (!asm_payload.outputs.empty()) {
                            out << " outputs=" << asm_payload.outputs.size();
                        }
                        if (!asm_payload.inputs.empty()) {
                            out << " inputs=" << asm_payload.inputs.size();
                        }
                    }
                    out << " -> ^" << name(block(b.terminator.target).name);
                    if (const auto* asm_ref =
                            std::get_if<InlineAsmPayloadRef>(&payload(b.terminator.payload_index));
                        asm_ref && valid(asm_ref->payload)) {
                        const InlineAsmPayload& asm_payload =
                            inline_asm_payload(asm_ref->payload);
                        for (BlockId target : asm_payload.goto_targets) {
                            if (valid(target) && block(target).name.valid()) {
                                out << ", ^" << name(block(target).name);
                            }
                        }
                    }
                    break;
                case TerminatorKind::Unreachable:
                    out << "unreachable";
                    break;
                case TerminatorKind::Throw: {
                    out << "throw";
                    if (!term_ops.empty()) out << ' ' << format_value(term_ops[0]);
                    std::vector<Operand> raw_ops = operands(b.terminator.operands);
                    for (const Operand& op : raw_ops) {
                        if (const auto* op_entity = std::get_if<EntityId>(&op.data);
                            op_entity && valid(*op_entity)) {
                            out << ", " << format_entity(*op_entity);
                        }
                    }
                    break;
                }
                case TerminatorKind::Rethrow:
                    out << "rethrow";
                    break;
                case TerminatorKind::Resume:
                    out << "resume";
                    for (size_t op_index = 0; op_index < term_ops.size(); ++op_index) {
                        out << (op_index == 0 ? " " : ", ")
                            << format_value(term_ops[op_index]);
                    }
                    break;
                case TerminatorKind::CoroSuspend: {
                    out << "coro_suspend";
                    if (const auto* coro_payload =
                            std::get_if<CoroSuspendPayload>(
                                &payload(b.terminator.payload_index))) {
                        out << " [" << coro_payload->index;
                        switch (coro_payload->kind) {
                            case CoroSaveKind::Initial:
                                out << ", initial";
                                break;
                            case CoroSaveKind::User:
                                break;
                            case CoroSaveKind::Final:
                                out << ", final";
                                break;
                        }
                        out << ']';
                    }
                    if (valid(b.terminator.target)) {
                        out << " resume ^"
                            << name(block(b.terminator.target).name);
                    }
                    if (valid(b.terminator.false_target)) {
                        out << ", destroy ^"
                            << name(block(b.terminator.false_target).name);
                    }
                    break;
                }
                case TerminatorKind::CoroEnd:
                    out << "coro_end";
                    break;
                case TerminatorKind::Invalid:
                    out << "<missing terminator>";
                    break;
            }
            if ((b.terminator.kind == TerminatorKind::Branch ||
                 b.terminator.kind == TerminatorKind::CondBranch) &&
                !term_ops.empty()) {
                size_t start = b.terminator.kind == TerminatorKind::CondBranch ? 1 : 0;
                if (start < term_ops.size()) {
                    out << " args=(";
                    for (size_t op_index = start; op_index < term_ops.size(); ++op_index) {
                        if (op_index > start) out << ", ";
                        out << format_value(term_ops[op_index]);
                    }
                    out << ')';
                }
            }
            out << '\n';
        }

        out << "}\n";
        (void)entity_record;
    }

    if (generics_.size() > 1) {
        out << "generics:\n";
        for (uint32_t i = 1; i < generics_.size(); ++i) {
            out << "  ";
            dump_id(out, i, generic_generations_[i]);
            out << " entity=" << format_entity(generics_[i].entity);
            if (generics_[i].pattern_function.valid()) {
                out << " pattern_fn=#" << generics_[i].pattern_function.index;
            }
            out << '\n';
        }
    }
    if (placeholder_result_facts_.size() > 1) {
        out << "placeholder_results:\n";
        for (uint32_t i = 1; i < placeholder_result_facts_.size(); ++i) {
            PlaceholderResultFactId id{
                i, placeholder_result_fact_generations_[i]};
            const PlaceholderResultFact& fact =
                placeholder_result_facts_[i];
            out << "  #" << id.index << " state=";
            switch (fact.state) {
                case PlaceholderResultState::Undeduced:
                    out << "undeduced";
                    break;
                case PlaceholderResultState::Deducing:
                    out << "deducing";
                    break;
                case PlaceholderResultState::Complete:
                    out << "complete";
                    break;
                case PlaceholderResultState::Failed:
                    out << "failed";
                    break;
            }
            out << " pattern=" << format_type(fact.declared_return_pattern);
            if (fact.candidate.type.valid()) {
                out << " candidate=" << format_type(fact.candidate);
            }
            if (fact.result.type.valid()) {
                out << " result=" << format_type(fact.result);
            }
            if (fact.defining_entity.valid()) {
                out << " definition=" << format_entity(fact.defining_entity);
            }
            if (fact.result_only_materialization) {
                out << " result_only";
            }
            out << " owners=";
            bool first_owner = true;
            for (uint32_t entity_index = 1;
                 entity_index < entities_.size(); ++entity_index) {
                const Entity& owner = entities_[entity_index];
                if (owner.placeholder_result != id) {
                    continue;
                }
                if (!first_owner) {
                    out << ',';
                }
                first_owner = false;
                out << format_entity(EntityId{
                    entity_index, entity_generations_[entity_index]});
            }
            if (first_owner) {
                out << "<none>";
            }
            out << '\n';
        }
    }
    if (specifics_.size() > 1) {
        out << "specifics:\n";
        for (uint32_t i = 1; i < specifics_.size(); ++i) {
            out << "  ";
            dump_id(out, i, specific_generations_[i]);
            out << " generic=#" << specifics_[i].generic.index;
            out << " function=#" << specifics_[i].function.index << '\n';
        }
    }
    if (!errors_.empty()) {
        out << "errors:\n";
        for (const auto& [loc, message] : errors_) {
            out << "  loc=" << loc.offset << " " << message << '\n';
        }
    }
}

std::string File::debug_semantic_fingerprint() const {
    std::ostringstream out;
    dump(out);
    return out.str();
}

} // namespace aburi::cir
