#include "lowerer.h"

#include <string>
#include <variant>
#include <vector>

#include "../cir/inst_schema.h"
#include "../cir/layout.h"

namespace aburi::cir2llvm {
namespace {

bool is_integer_like(cir::OperatorValueDomain domain) {
    return domain == cir::OperatorValueDomain::Bool ||
           domain == cir::OperatorValueDomain::SignedInteger ||
           domain == cir::OperatorValueDomain::UnsignedInteger;
}

bool is_numeric_like(cir::OperatorValueDomain domain) {
    return is_integer_like(domain) ||
           domain == cir::OperatorValueDomain::Floating ||
           domain == cir::OperatorValueDomain::Complex;
}

bool is_supported_unary(cir::UnaryOpKind op, cir::OperatorValueDomain domain) {
    switch (op) {
        case cir::UnaryOpKind::Plus:
        case cir::UnaryOpKind::Minus:
            return is_numeric_like(domain);
        case cir::UnaryOpKind::LogicalNot:
            return domain != cir::OperatorValueDomain::Unknown;
        case cir::UnaryOpKind::BitwiseNot:
            return is_integer_like(domain) ||
                   domain == cir::OperatorValueDomain::Complex;
        case cir::UnaryOpKind::Invalid:
            return false;
    }
    return false;
}

bool is_supported_binary(cir::BinaryOpKind op, cir::OperatorValueDomain domain) {
    switch (op) {
        case cir::BinaryOpKind::Add:
        case cir::BinaryOpKind::Sub:
            return is_numeric_like(domain) ||
                   domain == cir::OperatorValueDomain::Pointer;
        case cir::BinaryOpKind::Mul:
            return is_numeric_like(domain);
        case cir::BinaryOpKind::Div:
        case cir::BinaryOpKind::Mod:
            return is_numeric_like(domain);
        case cir::BinaryOpKind::Less:
        case cir::BinaryOpKind::LessEqual:
        case cir::BinaryOpKind::Greater:
        case cir::BinaryOpKind::GreaterEqual:
            return is_numeric_like(domain) ||
                   domain == cir::OperatorValueDomain::Pointer;
        case cir::BinaryOpKind::Equal:
        case cir::BinaryOpKind::NotEqual:
            return domain != cir::OperatorValueDomain::Unknown;
        case cir::BinaryOpKind::LogicalAnd:
        case cir::BinaryOpKind::LogicalOr:
            return true;
        case cir::BinaryOpKind::BitAnd:
        case cir::BinaryOpKind::BitOr:
        case cir::BinaryOpKind::BitXor:
        case cir::BinaryOpKind::Shl:
        case cir::BinaryOpKind::Shr:
            return is_integer_like(domain);
        case cir::BinaryOpKind::Comma:
            return true;
        case cir::BinaryOpKind::Invalid:
            return false;
    }
    return false;
}

} // namespace

void Lowerer::preflight() {

    for (cir::EntityId entity_id : file_.entity_ids()) {
        check_entity(entity_id);
    }
    for (cir::FunctionId function_id : file_.function_ids()) {
        const cir::Entity& entity =
            file_.entity(file_.function(function_id).entity);

        if (entity.is_deleted ||
            entity.is_template_pattern ||
            entity.result_type_only_definition ||
            entity.decl_flags.is_consteval) {
            continue;
        }
        if (!definition_required(entity)) {
            continue;
        }
        check_function(function_id);
    }
}

void Lowerer::check_entity(cir::EntityId entity_id) {
    const cir::Entity& entity = file_.entity(entity_id);
    auto context_is_nonlowered_function = [&](cir::DeclContextId context) {
        size_t remaining = file_.decl_context_ids().size() + 1;
        while (context.valid() && file_.valid(context) && remaining-- > 0) {
            const cir::DeclContext& declaration_context =
                file_.decl_context(context);
            if (declaration_context.kind == cir::DeclContextKind::Function &&
                declaration_context.owner.valid() &&
                file_.valid(declaration_context.owner)) {
                const cir::Entity& function =
                    file_.entity(declaration_context.owner);
                return function.is_template_pattern ||
                       function.result_type_only_definition ||
                       !definition_required(function);
            }
            context = declaration_context.parent;
        }
        return false;
    };

    if (entity.is_deleted ||
        entity.is_template_pattern || entity.result_type_only_definition ||
        (entity.parent.valid() && file_.valid(entity.parent) &&
         (file_.entity(entity.parent).is_template_pattern ||
          file_.entity(entity.parent).result_type_only_definition)) ||
        context_is_nonlowered_function(entity.semantic_context) ||
        context_is_nonlowered_function(entity.lexical_context)) {
        return;
    }
    if (entity.is_definition &&
        (entity.kind == cir::EntityKind::Function ||
         entity.kind == cir::EntityKind::Method ||
         entity.kind == cir::EntityKind::Constructor ||
         entity.kind == cir::EntityKind::Destructor ||
         entity.kind == cir::EntityKind::Variable) &&
        !definition_required(entity)) {
        return;
    }
    switch (entity.kind) {
        case cir::EntityKind::Invalid:
        case cir::EntityKind::TranslationUnit:

        case cir::EntityKind::Concept:
        case cir::EntityKind::StructuredBinding:
        case cir::EntityKind::Namespace:
        case cir::EntityKind::NamespaceAlias:

        case cir::EntityKind::ObjCInterface:
        case cir::EntityKind::ObjCProtocol:
        case cir::EntityKind::ObjCCategory:
        case cir::EntityKind::ObjCImplementation:
        case cir::EntityKind::ObjCMethod:
        case cir::EntityKind::ObjCIvar:
        case cir::EntityKind::ObjCProperty:
            return;
        case cir::EntityKind::Function:
        case cir::EntityKind::Parameter:
        case cir::EntityKind::Variable:
            if (entity.memory_space != cir::MemorySpace::Default) {
                error("non-default memory space on entity " +
                          file_.format_entity(entity_id) +
                          " is not supported yet",
                      entity.loc);
            }

            if (!entity.is_definition) {
                return;
            }
            check_type(entity.type, entity.loc, "entity " + file_.format_entity(entity_id));
            return;
        case cir::EntityKind::TypeAlias:

            return;
        case cir::EntityKind::Enum:
            check_type(entity.type, entity.loc, "enum " + file_.format_entity(entity_id));
            return;
        case cir::EntityKind::Enumerator:
            check_type(entity.type, entity.loc, "enumerator " + file_.format_entity(entity_id));
            return;
        case cir::EntityKind::Record:

            return;
        case cir::EntityKind::Field:
            if (const cir::RecordFieldFact* field = file_.field_fact(entity_id);
                field && field->is_flexible_array_member) {
                return;
            }
            check_type(entity.type, entity.loc, "field " + file_.format_entity(entity_id));
            return;
        case cir::EntityKind::Method:
        case cir::EntityKind::Constructor:
        case cir::EntityKind::Destructor:

            if (!entity.is_definition) {
                return;
            }
            check_type(entity.type, entity.loc,
                       "member function " + file_.format_entity(entity_id));
            return;
        case cir::EntityKind::TemplateParam:

            return;
    }
}

void Lowerer::check_function(cir::FunctionId function_id) {
    const cir::Function& function = file_.function(function_id);
    const cir::Entity& entity = file_.entity(function.entity);
    if (entity.kind != cir::EntityKind::Function &&
        entity.kind != cir::EntityKind::Method &&
        entity.kind != cir::EntityKind::Constructor &&
        entity.kind != cir::EntityKind::Destructor) {
        error("only function entities can be lowered", function.loc);
    }
    if (function.execution_space != cir::ExecutionSpace::Host &&
        function.execution_space != cir::ExecutionSpace::Unspecified) {
        error("non-host function execution spaces are not supported yet", function.loc);
    }
    check_type(function.type, function.loc, "function type");
    check_type(function.result_type, function.loc, "function result type");

    for (cir::BlockId block_id : function.blocks) {
        const cir::Block& block = file_.block(block_id);
        for (cir::InstId inst_id : block.instructions) {
            check_inst(inst_id);
        }

        std::vector<cir::ValueRef> term_ops = file_.value_operands(block.terminator.operands);
        switch (block.terminator.kind) {
            case cir::TerminatorKind::Branch: {
                if (file_.valid(block.terminator.target) &&
                    term_ops.size() != file_.block(block.terminator.target).parameters.size()) {
                    error("branch target argument count does not match target parameters",
                          block.terminator.loc);
                }
                break;
            }
            case cir::TerminatorKind::CondBranch: {
                size_t arg_count = term_ops.empty() ? 0 : term_ops.size() - 1;
                if (file_.valid(block.terminator.target) &&
                    arg_count != file_.block(block.terminator.target).parameters.size()) {
                    error("conditional true-target argument count does not match target parameters",
                          block.terminator.loc);
                }
                if (file_.valid(block.terminator.false_target) &&
                    arg_count != file_.block(block.terminator.false_target).parameters.size()) {
                    error("conditional false-target argument count does not match target parameters",
                          block.terminator.loc);
                }
                break;
            }
            case cir::TerminatorKind::Switch: {
                if (term_ops.size() != 1) {
                    error("switch terminator must have one condition operand",
                          block.terminator.loc);
                    break;
                }
                if (!file_.valid(block.terminator.target)) {
                    error("switch default target is invalid", block.terminator.loc);
                    break;
                }
                if (!file_.block(block.terminator.target).parameters.empty()) {
                    error("switch default target parameters are not supported",
                          block.terminator.loc);
                }
                const cir::InstPayload& payload =
                    file_.payload(block.terminator.payload_index);
                const auto* switch_payload =
                    std::get_if<cir::SwitchTerminatorPayload>(&payload);
                if (!switch_payload) {
                    error("switch terminator payload is missing", block.terminator.loc);
                    break;
                }
                if (!switch_payload->condition_type.type.valid() ||
                    !file_.valid(switch_payload->condition_type.type)) {
                    error("switch condition type is invalid", block.terminator.loc);
                } else if (file_.inst(term_ops[0].inst).result_type !=
                           switch_payload->condition_type.type) {
                    error("switch condition type does not match condition value",
                          block.terminator.loc);
                }
                for (size_t case_index = 0;
                     case_index < switch_payload->cases.size();
                     ++case_index) {
                    const cir::SwitchCaseRange& case_range =
                        switch_payload->cases[case_index];
                    if (case_range.high < case_range.low) {
                        error("switch case range is empty", case_range.loc);
                    }
                    if (!file_.valid(case_range.target)) {
                        error("switch case target is invalid", case_range.loc);
                    } else if (!file_.block(case_range.target).parameters.empty()) {
                        error("switch case target parameters are not supported",
                              case_range.loc);
                    }
                    for (size_t prior_index = 0; prior_index < case_index; ++prior_index) {
                        const cir::SwitchCaseRange& prior =
                            switch_payload->cases[prior_index];
                        if (case_range.low <= prior.high && prior.low <= case_range.high) {
                            error("switch case ranges overlap", case_range.loc);
                            break;
                        }
                    }
                }
                break;
            }
            case cir::TerminatorKind::IndirectBranch:
            case cir::TerminatorKind::AsmGoto:
                break;
            case cir::TerminatorKind::Return:
            case cir::TerminatorKind::Unreachable:
            case cir::TerminatorKind::Invalid:
            case cir::TerminatorKind::Throw:
            case cir::TerminatorKind::Rethrow:
            case cir::TerminatorKind::Resume:
                break;
            case cir::TerminatorKind::CoroSuspend:
            case cir::TerminatorKind::CoroEnd:
                error("pre-split coroutine CIR reached the LLVM backend; "
                      "the coroutine split pass must run first",
                      block.terminator.loc);
                break;
        }
    }
}

bool Lowerer::check_type_ref(cir::TypeRef ref, SrcLoc loc, const std::string& context_text) {
    if (ref.memory_space != cir::MemorySpace::Default) {
        error("non-default memory space in " + context_text +
                  " is not supported yet",
              loc);
        return false;
    }
    return check_type(ref.type, loc, context_text);
}

bool Lowerer::check_type(cir::TypeId type_id, SrcLoc loc, const std::string& context_text) {
    if (!file_.valid(type_id)) {
        error("invalid type in " + context_text, loc);
        return false;
    }

    type_id = file_.resolved_type(type_id);
    const cir::Type& type = file_.type(type_id);
    const cir::TypePayload& payload = file_.type_payload(type_id);
    switch (type.kind) {
        case cir::TypeKind::Builtin: {
            const auto* builtin = std::get_if<cir::BuiltinTypePayload>(&payload);
            if (!builtin || builtin->kind == cir::BuiltinTypeKind::Other) {
                error("unsupported builtin type in " + context_text, loc);
                return false;
            }
            return true;
        }
        case cir::TypeKind::Pointer: {
            const auto* pointer = std::get_if<cir::PointerTypePayload>(&payload);
            if (!pointer) {
                error("malformed pointer type in " + context_text, loc);
                return false;
            }

            cir::TypeId pointee = file_.resolved_type(pointer->pointee.type);
            if (file_.valid(pointee) &&
                file_.type(pointee).kind == cir::TypeKind::Record) {
                return true;
            }
            return check_type_ref(pointer->pointee, loc, context_text);
        }
        case cir::TypeKind::BlockPointer:

            return true;
        case cir::TypeKind::MemberPointer: {
            cir::TypeRef class_ref = file_.member_pointer_class_ref(type_id);
            cir::TypeRef member_ref = file_.member_pointer_member_ref(type_id);
            cir::TypeId class_type = file_.resolved_type(class_ref.type);
            if (!file_.valid(class_type) ||
                file_.type(class_type).kind != cir::TypeKind::Record ||
                !member_ref.valid()) {
                error("malformed member pointer type in " + context_text, loc);
                return false;
            }
            return check_type_ref(member_ref, loc, context_text);
        }
        case cir::TypeKind::Array: {
            const auto* array = std::get_if<cir::ArrayTypePayload>(&payload);
            if (!array ||
                (array->size_kind == cir::ArraySizeKind::Constant &&
                 !array->size.has_value())) {
                error("malformed array type in " + context_text, loc);
                return false;
            }
            if (array->size_kind == cir::ArraySizeKind::Variable &&
                !array->size_expr.valid()) {
                error("variable-length array without a bound in " + context_text, loc);
                return false;
            }
            return check_type_ref(array->element_type, loc, context_text);
        }
        case cir::TypeKind::Function: {
            const auto* function = std::get_if<cir::FunctionTypePayload>(&payload);
            if (!function) {
                error("malformed function type in " + context_text, loc);
                return false;
            }
            bool ok = check_type_ref(function->return_type, loc, context_text);
            for (cir::TypeRef parameter : function->parameters) {
                ok = check_type_ref(parameter, loc, context_text) && ok;
            }
            for (uint8_t is_pack : function->parameter_pack_flags) {
                if (is_pack) {
                    error("function parameter packs are not supported yet in " + context_text,
                          loc);
                    ok = false;
                }
            }
            return ok;
        }
        case cir::TypeKind::Enum: {
            const auto* enum_payload = std::get_if<cir::EnumTypePayload>(&payload);
            if (enum_payload && enum_payload->underlying_type.valid()) {
                return check_type_ref(enum_payload->underlying_type, loc, context_text);
            }
            return true;
        }
        case cir::TypeKind::Vector: {
            const auto* vector = std::get_if<cir::VectorTypePayload>(&payload);
            if (!vector || vector->element_count == 0 || vector->size_bytes == 0) {
                error("malformed vector type in " + context_text, loc);
                return false;
            }
            return check_type_ref(vector->element_type, loc, context_text);
        }
        case cir::TypeKind::Complex: {
            const auto* complex = std::get_if<cir::ComplexTypePayload>(&payload);
            return complex && check_type_ref(complex->element_type, loc, context_text);
        }
        case cir::TypeKind::BitInt: {
            const auto* bit_int = std::get_if<cir::BitIntTypePayload>(&payload);
            if (!bit_int || bit_int->bits == 0 || bit_int->bits > 128) {
                error("unsupported _BitInt width in " + context_text, loc);
                return false;
            }
            return true;
        }
        case cir::TypeKind::Typedef: {
            const auto* typedef_payload = std::get_if<cir::TypedefTypePayload>(&payload);
            return typedef_payload &&
                   check_type_ref(typedef_payload->underlying_type, loc, context_text);
        }
        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference: {

            const auto* reference = std::get_if<cir::ReferenceTypePayload>(&payload);
            if (!reference) {
                error("malformed reference type in " + context_text, loc);
                return false;
            }

            cir::TypeId referred =
                file_.resolved_type(reference->referred_type.type);
            if (file_.valid(referred) &&
                file_.type(referred).kind == cir::TypeKind::Record) {
                return true;
            }
            return check_type_ref(reference->referred_type,
                                  loc,
                                  context_text);
        }
        case cir::TypeKind::Place: {
            const auto* place = std::get_if<cir::PlaceTypePayload>(&payload);
            if (!place) {
                error("malformed place type in " + context_text, loc);
                return false;
            }

            cir::TypeId object = file_.resolved_type(place->object_type.type);
            if (file_.valid(object) &&
                file_.type(object).kind == cir::TypeKind::Record) {
                return true;
            }
            return check_type_ref(place->object_type, loc, context_text);
        }
        case cir::TypeKind::Record:
            if (const cir::RecordFacts* facts = file_.record_facts_for_type(type_id);
                facts && !facts->is_incomplete) {
                return true;
            }
            error("incomplete record type is not supported yet in " + context_text, loc);
            return false;
        case cir::TypeKind::TypeParam:
        case cir::TypeKind::TemplateSpecialization:
        case cir::TypeKind::AliasSpecialization:
        case cir::TypeKind::DependentName:
        case cir::TypeKind::Dependent:
        case cir::TypeKind::Unknown:
        case cir::TypeKind::Error:
        case cir::TypeKind::Placeholder:
        case cir::TypeKind::Auto:
        case cir::TypeKind::TypeofExpr:
        case cir::TypeKind::DecltypeExpr:
        case cir::TypeKind::BuiltinTransform:
        case cir::TypeKind::BuiltinPackElement:
        case cir::TypeKind::PackIndex:
        case cir::TypeKind::Invalid:
            error("type '" + std::string(cir::type_kind_name(type.kind)) +
                      "' is not supported yet in " + context_text,
                  loc);
            return false;
    }
    return false;
}

void Lowerer::check_inst(cir::InstId inst_id) {
    const cir::Inst& inst = file_.inst(inst_id);
    if (inst.result_type.valid()) {
        check_type(inst.result_type, inst.loc, "instruction " + file_.format_inst(inst_id));
    }
    if (inst.place_fact.valid()) {
        const cir::PlaceFact& fact = file_.place_fact(inst.place_fact);

        cir::TypeId object = file_.resolved_type(fact.object_type.type);
        if (!(file_.valid(object) &&
              file_.type(object).kind == cir::TypeKind::Record)) {
            check_type_ref(fact.object_type, fact.loc, "place fact");
        }
    }

    const cir::InstPayload& payload = file_.payload(inst.payload_index);
    std::vector<cir::Operand> operands = file_.operands(inst.operands);
    std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
    for (const cir::Operand& operand : operands) {
        if (const auto* type_operand = std::get_if<cir::TypeRef>(&operand.data)) {
            check_type_ref(*type_operand, inst.loc, "instruction operand");
        }
    }
    switch (inst.kind) {
        case cir::InstKind::Invalid:
            error("invalid instructions cannot be lowered", inst.loc);
            return;
        case cir::InstKind::ReflectValue:
            error("'std::meta::info' values exist only during constant "
                  "evaluation and cannot be lowered to runtime code",
                  inst.loc);
            return;
        case cir::InstKind::NameRef:
        case cir::InstKind::DependentCall:
        case cir::InstKind::DependentRegion:
        case cir::InstKind::Error:
            error("instruction '" + std::string(cir::inst_mnemonic(inst.kind)) +
                      "' is not supported yet",
                  inst.loc);
            return;
        case cir::InstKind::ObjCMessageSend:
        case cir::InstKind::ObjCIvarAddr:
        case cir::InstKind::ObjCSelectorLiteral:
        case cir::InstKind::ObjCStringLiteral:
        case cir::InstKind::ObjCArcOp:
            error("Objective-C CIR reached the backend; the Objective-C "
                  "lowering pass must expand it first",
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
        case cir::InstKind::ConstructInPlace:
        case cir::InstKind::Destroy:
        case cir::InstKind::FieldAddr:
        case cir::InstKind::DataMemberPointerPlace:
        case cir::InstKind::MemberFunctionPointerCallee:
        case cir::InstKind::MemberFunctionPointerThis:
            return;
        case cir::InstKind::UnaryOp:
            if (const auto* descriptor =
                    std::get_if<cir::UnaryOpDescriptor>(&payload)) {
                check_type_ref(descriptor->computation_type,
                               inst.loc,
                               "unary computation type");
                cir::OperatorValueDomain domain =
                    file_.operator_value_domain(descriptor->computation_type);
                if (!is_supported_unary(descriptor->op, domain)) {
                    error("unary operator '" +
                              std::string(cir::unary_op_spelling(descriptor->op)) +
                              "' for " +
                              std::string(cir::operator_value_domain_name(domain)) +
                              " is not supported yet",
                          inst.loc);
                }
            } else {
                error("unary operator is missing a descriptor", inst.loc);
            }
            break;
        case cir::InstKind::BinaryOp:
            if (const auto* descriptor =
                    std::get_if<cir::BinaryOpDescriptor>(&payload)) {
                check_type_ref(descriptor->computation_type,
                               inst.loc,
                               "binary computation type");
                cir::OperatorValueDomain domain =
                    file_.operator_value_domain(descriptor->computation_type);
                if (!is_supported_binary(descriptor->op, domain)) {
                    error("binary operator '" +
                              std::string(cir::binary_op_spelling(descriptor->op)) +
                              "' for " +
                              std::string(cir::operator_value_domain_name(domain)) +
                              " is not supported yet",
                          inst.loc);
                }
            } else {
                error("binary operator is missing a descriptor", inst.loc);
            }
            break;
        case cir::InstKind::SizeofType:
        case cir::InstKind::AlignofType:
            break;
        case cir::InstKind::Call:
        case cir::InstKind::VaStart:
        case cir::InstKind::VaArg:
        case cir::InstKind::VaEnd:
        case cir::InstKind::VaCopy:
            break;
        case cir::InstKind::BuiltinCall:
            if (const auto* builtin =
                    std::get_if<cir::BuiltinCallPayload>(&payload)) {
                if (!is_supported_builtin_kind(builtin->kind)) {
                    error("builtin '" + builtin->name + "' is not supported yet", inst.loc);
                }
            } else {
                error("builtin call is missing builtin metadata", inst.loc);
            }
            break;
        case cir::InstKind::StackAlloc:
            if (values.size() != 1 || !file_.valid(values[0].inst)) {
                error("stack_alloc is missing its size operand", inst.loc);
            }
            break;
        case cir::InstKind::StackSave:
            break;
        case cir::InstKind::StackRestore:
            if (values.size() != 1 || !file_.valid(values[0].inst)) {
                error("stack_restore is missing its saved operand", inst.loc);
            }
            break;
        case cir::InstKind::LifetimeStart:
        case cir::InstKind::LifetimeEnd:

            if (values.size() > 1) {
                error("lifetime marker takes at most one place operand", inst.loc);
            }
            break;
        case cir::InstKind::AtomicLoad:
        case cir::InstKind::AtomicStore:
        case cir::InstKind::AtomicRmw:
        case cir::InstKind::AtomicCmpXchg:
        case cir::InstKind::AtomicFence:
        case cir::InstKind::ComplexMake:
        case cir::InstKind::ComplexReal:
        case cir::InstKind::ComplexImag:
        case cir::InstKind::ComplexRealPlace:
        case cir::InstKind::ComplexImagPlace:
            break;
        case cir::InstKind::ZeroObject:
            if (values.size() != 1 || !file_.valid(values[0].inst)) {
                error("zero_object is missing its destination place", inst.loc);
                break;
            }
            if (cir::TypeId place_type = file_.inst(values[0].inst).result_type;
                !file_.valid(place_type) ||
                file_.type(place_type).kind != cir::TypeKind::Place) {
                error("zero_object destination must be a place", inst.loc);
                break;
            } else if (!cir::size_align_of_type(file_, file_.place_object_type(place_type))) {
                error("zero_object requires a complete object type", inst.loc);
            }
            break;
        case cir::InstKind::InlineAsm:
            if (const auto* asm_ref =
                    std::get_if<cir::InlineAsmPayloadRef>(&payload)) {
                if (!file_.valid(asm_ref->payload)) {
                    error("inline asm is missing asm metadata", inst.loc);
                }
            } else {
                error("inline asm is missing asm metadata", inst.loc);
            }
            break;
        case cir::InstKind::Param:
        case cir::InstKind::IntegerLiteral:
        case cir::InstKind::BooleanLiteral:
        case cir::InstKind::NullptrLiteral:
        case cir::InstKind::FloatingLiteral:
        case cir::InstKind::CharacterLiteral:
        case cir::InstKind::StringLiteral:
        case cir::InstKind::LocalPlace:
        case cir::InstKind::GlobalPlace:
        case cir::InstKind::Load:
        case cir::InstKind::LValueToRValue:
        case cir::InstKind::FunctionToPointer:
        case cir::InstKind::MemberPointerValue:
        case cir::InstKind::LabelAddress:
        case cir::InstKind::Store:
        case cir::InstKind::AddrOf:
        case cir::InstKind::Deref:
        case cir::InstKind::ArrayElementPlace:
        case cir::InstKind::VectorElementPlace:
        case cir::InstKind::VectorExtract:
        case cir::InstKind::Cast:
            break;
        case cir::InstKind::EhAllocException:
        case cir::InstKind::EhSelector:
        case cir::InstKind::EhTypeId:
        case cir::InstKind::CatchBegin:
        case cir::InstKind::CatchEnd:
            break;
        case cir::InstKind::EhLandingPad:
            if (!std::holds_alternative<cir::EhLandingPadPayload>(payload)) {
                error("landing pad is missing clause metadata", inst.loc);
            }
            break;
    }
}

} // namespace aburi::cir2llvm
