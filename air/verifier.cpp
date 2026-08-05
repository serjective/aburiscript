#include "verifier.h"

#include "dominators.h"

#include <cassert>
#include <unordered_map>
#include <unordered_set>

namespace aburi::air {

std::string VerifyResult::to_string() const {
    std::string text;
    for (const VerifierDiag& diag : diags) {
        if (!text.empty()) {
            text += "\n";
        }
        text += diag.severity == VerifierDiag::Severity::Error ? "error: " : "note: ";
        text += diag.message;
    }
    return text;
}

namespace {

bool int_width_allowed(uint16_t width) {
    switch (width) {
        case 8:
        case 16:
        case 32:
        case 64:
        case 128:
            return true;
        default:
            return false;
    }
}

bool float_kind_allowed(FloatKind kind) {
    switch (kind) {
        case FloatKind::F32:
        case FloatKind::F64:
            return true;
        case FloatKind::F128:
        case FloatKind::F80:
            return true;
    }
    return false;
}

uint32_t float_bit_width(FloatKind kind) {
    switch (kind) {
        case FloatKind::F32: return 32;
        case FloatKind::F64: return 64;
        case FloatKind::F128: return 128;
        case FloatKind::F80: return 80;
    }
    return 0;
}

bool mem_order_valid(uint64_t code) {
    return code <= static_cast<uint64_t>(MemOrder::SeqCst);
}

class FunctionVerifier {
public:
    FunctionVerifier(const Module& mod, const Function& func, VerifyResult& result)
        : mod_(mod), func_(func), types_(mod.types()), result_(result) {}

    void run() {
        check_signature();
        if (func_.is_declaration()) {
            return;
        }
        number_blocks();
        check_entry_signature();
        for (BlockId b = func_.first_block(); b.is_valid(); b = func_.block(b).next) {
            check_block_layout(b);
        }
        for (BlockId b = func_.first_block(); b.is_valid(); b = func_.block(b).next) {
            for (InstId i = func_.block(b).first; i.is_valid(); i = func_.inst(i).next) {
                check_inst(b, i);
            }
        }
        domtree_.compute(func_);
        for (BlockId b = func_.first_block(); b.is_valid(); b = func_.block(b).next) {
            if (!domtree_.reachable(b)) {
                note(block_label(b) + " is unreachable");
                continue;
            }
            check_block_dominance(b);
        }
    }

private:
    void error(const std::string& message, SrcLoc loc = {}) {
        result_.diags.push_back(
            {VerifierDiag::Severity::Error, "func @" + func_.name() + ": " + message,
             loc});
    }

    void note(const std::string& message) {
        result_.diags.push_back(
            {VerifierDiag::Severity::Note, "func @" + func_.name() + ": " + message,
             SrcLoc{}});
    }

    std::string block_label(BlockId b) const {
        auto it = block_numbers_.find(b.index);
        if (it == block_numbers_.end()) {
            return "b?";
        }
        return "b" + std::to_string(it->second);
    }

    std::string inst_label(BlockId b, InstId i) const {
        return block_label(b) + ": " +
               std::string(opcode_mnemonic(func_.inst(i).op));
    }

    bool block_begins_with(BlockId b, Opcode op) const {
        if (!func_.is_valid(b)) {
            return false;
        }
        InstId first = func_.block(b).first;
        return first.is_valid() && func_.inst(first).op == op;
    }

    void number_blocks() {
        uint32_t next = 0;
        for (BlockId b = func_.first_block(); b.is_valid(); b = func_.block(b).next) {
            block_numbers_[b.index] = next++;
        }
    }

    const SigData& sig() const { return types_.signature(func_.sig()); }

    void check_signature() {
        const SigData& data = sig();
        for (uint32_t i = 0; i < data.params.size(); ++i) {
            const SigParam& param = data.params[i];
            if (param.role == ParamRole::Sret) {
                if (i != 0) {
                    error("sret parameter must be parameter 0");
                }
                if (!types_.is_ptr(param.type)) {
                    error("sret parameter must be a pointer");
                }
            }
            if (param.role == ParamRole::IndirectByval && !types_.is_ptr(param.type)) {
                error("byval parameter must be a pointer");
            }
            if (param.role == ParamRole::StackByval) {
                if (!types_.is_ptr(param.type)) {
                    error("stackbyval parameter must be a pointer");
                }
                if (param.byval_size == 0) {
                    error("stackbyval parameter must carry its byte size");
                }
            }
        }
        switch (data.ret_class) {
            case RetClass::Void:
                break;
            case RetClass::Scalar:
                if (!data.ret_type.is_valid() || !types_.is_scalar(data.ret_type)) {
                    error("scalar return requires a scalar return type");
                }
                break;
            case RetClass::IntPair:
                if (!data.ret_type.is_valid() || !types_.is_int(data.ret_type) ||
                    data.ret_count != 2) {
                    error("pair return requires an integer element type and count 2");
                }
                break;
            case RetClass::Hfa:
                if (!data.ret_type.is_valid() || !types_.is_float(data.ret_type) ||
                    data.ret_count == 0 || data.ret_count > 4) {
                    error("hfa return requires a float element type and count 1..4");
                }
                break;
            case RetClass::IndirectSret:
                if (data.params.empty() || data.params[0].role != ParamRole::Sret) {
                    error("sret return requires an sret-role parameter 0");
                }
                break;
        }
        if (data.is_variadic && data.fixed_param_count > data.params.size()) {
            error("variadic signature names more fixed parameters than it has");
        }
    }

    void check_entry_signature() {
        const SigData& data = sig();
        auto params = func_.block_params(func_.entry_block());
        if (params.size() != data.params.size()) {
            error("entry block has " + std::to_string(params.size()) +
                  " parameters but the signature has " +
                  std::to_string(data.params.size()));
            return;
        }
        for (uint32_t i = 0; i < params.size(); ++i) {
            if (func_.value_type(params[i]) != data.params[i].type) {
                error("entry block parameter " + std::to_string(i) + " has type " +
                      types_.spelling(func_.value_type(params[i])) +
                      " but the signature expects " +
                      types_.spelling(data.params[i].type));
            }
        }
    }

    void check_block_layout(BlockId b) {
        for (ValueId param : func_.block_params(b)) {
            check_value_type(func_.value_type(param),
                             block_label(b) + ": block parameter");
        }
        InstId last = func_.block(b).last;
        if (!last.is_valid()) {
            error(block_label(b) + " is empty");
            return;
        }
        uint32_t pos = 0;
        for (InstId i = func_.block(b).first; i.is_valid(); i = func_.inst(i).next) {
            inst_pos_[i.index] = pos++;
            if (func_.inst(i).block != b) {
                error(inst_label(b, i) + ": instruction is linked into " +
                      block_label(b) + " but records another owner block");
            }
            if (opcode_is_terminator(func_.inst(i).op) && i != last) {
                error(inst_label(b, i) + ": terminator in the middle of a block");
            }
            if (func_.inst(i).op == Opcode::EhLandingPad && pos != 1) {
                error(inst_label(b, i) +
                      ": eh_landing_pad must be the first instruction of its block");
            }
        }
        if (!opcode_is_terminator(func_.inst(last).op)) {
            error(block_label(b) + " does not end in a terminator");
        }
    }

    void check_value_type(TypeId type, const std::string& what) {
        if (!types_.is_valid(type)) {
            error(what + " has an invalid type");
            return;
        }
        if (types_.is_void(type)) {
            error(what + " has type void");
            return;
        }
        const TypeData& data = types_.type(type);
        if (data.kind == TypeKind::Int && !int_width_allowed(data.int_width)) {
            error(what + " has unsupported integer width i" +
                  std::to_string(data.int_width));
        }
        if (data.kind == TypeKind::Float && !float_kind_allowed(data.float_kind)) {
            error(what + " has reserved float type " + types_.spelling(type));
        }
    }

    bool check_operand_values(BlockId b, InstId i) {
        bool ok = true;
        for (ValueId op : func_.operands(i)) {
            if (!func_.is_valid(op)) {
                error(inst_label(b, i) + ": invalid operand value id");
                ok = false;
                continue;
            }
            const ValueData& value = func_.value(op);
            if (value.kind == ValueKind::ConstInt) {
                if (!types_.is_int(value.type)) {
                    error(inst_label(b, i) +
                          ": integer constant has a non-integer type");
                    ok = false;
                } else {
                    const uint16_t width = types_.int_width(value.type);
                    bool canonical = true;
                    if (width < 64) {
                        canonical = value.payload2 == 0 &&
                                    (value.payload >> width) == 0;
                    } else if (width == 64) {
                        canonical = value.payload2 == 0;
                    } else if (width < 128) {
                        canonical = (value.payload2 >> (width - 64)) == 0;
                    }
                    if (!canonical) {
                        error(inst_label(b, i) +
                              ": integer constant has non-canonical bits");
                        ok = false;
                    }
                }
            }
            if (value.kind == ValueKind::ConstFloat) {
                if (!types_.is_float(value.type)) {
                    error(inst_label(b, i) +
                          ": floating constant has a non-floating type");
                    ok = false;
                } else {
                    FloatKind kind = types_.type(value.type).float_kind;
                    bool canonical = true;
                    switch (kind) {
                        case FloatKind::F32:
                            canonical = value.payload2 == 0 &&
                                        (value.payload >> 32) == 0;
                            break;
                        case FloatKind::F64:
                            canonical = value.payload2 == 0;
                            break;
                        case FloatKind::F80:
                            canonical = (value.payload2 >> 16) == 0;
                            break;
                        case FloatKind::F128:
                            break;
                    }
                    if (!canonical) {
                        error(inst_label(b, i) +
                              ": floating constant has non-canonical bits");
                        ok = false;
                    }
                }
            }
            if (value.kind == ValueKind::LabelAddr) {
                BlockId target{static_cast<uint32_t>(value.payload)};
                if (!func_.is_valid(target)) {
                    error(inst_label(b, i) + ": label address of an invalid block");
                    ok = false;
                } else if (func_.block(target).param_count != 0) {
                    error(inst_label(b, i) +
                          ": label address of a block with parameters");
                }
            }
        }
        return ok;
    }

    TypeId op_type(InstId i, uint32_t index) const {
        return func_.value_type(func_.operands(i)[index]);
    }

    void require_type(BlockId b, InstId i, uint32_t index, TypeId expected) {
        TypeId got = op_type(i, index);
        if (got != expected) {
            error(inst_label(b, i) + ": operand " + std::to_string(index) +
                  " has type " + types_.spelling(got) + ", expected " +
                  types_.spelling(expected), func_.inst(i).loc);
        }
    }

    void require_int(BlockId b, InstId i, uint32_t index) {
        if (!types_.is_int(op_type(i, index))) {
            error(inst_label(b, i) + ": operand " + std::to_string(index) +
                  " must be an integer, got " + types_.spelling(op_type(i, index)),
                  func_.inst(i).loc);
        }
    }

    void require_ptr(BlockId b, InstId i, uint32_t index) {
        if (!types_.is_ptr(op_type(i, index))) {
            error(inst_label(b, i) + ": operand " + std::to_string(index) +
                  " must be a pointer, got " + types_.spelling(op_type(i, index)),
                  func_.inst(i).loc);
        }
    }

    TypeId size_int_type() const {
        return mod_.target().pointer_width == 64 ? types::I64 : types::I32;
    }

    void check_volatile_flag(BlockId b, InstId i) {
        const InstData& data = func_.inst(i);
        if ((data.flags & INST_FLAG_VOLATILE) == 0) {
            return;
        }
        switch (data.op) {
            case Opcode::Load:
            case Opcode::Store:
            case Opcode::AtomicLoad:
            case Opcode::AtomicStore:
                return;
            default:
                error(inst_label(b, i) + ": volatile flag on a non-memory operation");
        }
    }

    void check_block_call(BlockId b, InstId i, BlockCallId call_id,
                          bool allow_args = true,
                          bool allow_landing_pad = false) {
        if (!func_.is_valid(call_id)) {
            error(inst_label(b, i) + ": invalid block-call id");
            return;
        }
        const BlockCall& call = func_.block_call(call_id);
        if (!func_.is_valid(call.target)) {
            error(inst_label(b, i) + ": branch to an invalid block");
            return;
        }
        if (call.target == func_.entry_block()) {
            error(inst_label(b, i) + ": branch targets the entry block");
        }
        if (block_begins_with(call.target, Opcode::EhLandingPad) &&
            !allow_landing_pad) {
            error(inst_label(b, i) +
                  ": only an invoke unwind edge may target a landing pad");
        }
        auto args = func_.block_call_args(call_id);
        auto params = func_.block_params(call.target);
        if (!allow_args && !args.empty()) {
            error(inst_label(b, i) + ": edge must not carry arguments");
            return;
        }
        if (args.size() != params.size()) {
            error(inst_label(b, i) + ": branch to " + block_label(call.target) +
                  " passes " + std::to_string(args.size()) + " arguments, expected " +
                  std::to_string(params.size()), func_.inst(i).loc);
            return;
        }
        for (uint32_t a = 0; a < args.size(); ++a) {
            if (!func_.is_valid(args[a])) {
                error(inst_label(b, i) + ": invalid branch argument");
                continue;
            }
            if (func_.value_type(args[a]) != func_.value_type(params[a])) {
                error(inst_label(b, i) + ": branch argument " + std::to_string(a) +
                      " has type " + types_.spelling(func_.value_type(args[a])) +
                      " but " + block_label(call.target) + " expects " +
                      types_.spelling(func_.value_type(params[a])),
                      func_.inst(i).loc);
            }
        }
    }
    static bool has_trailing_dest(const SigData& sig) {
        return sig.ret_class == RetClass::IntPair || sig.ret_class == RetClass::Hfa;
    }

    void check_call_args(BlockId b, InstId i, const SigData& sig,
                         std::span<const ValueId> args) {
        size_t required = sig.params.size() + (has_trailing_dest(sig) ? 1 : 0);
        if (sig.is_variadic ? args.size() < required : args.size() != required) {
            error(inst_label(b, i) + ": call passes " + std::to_string(args.size()) +
                  " operands, signature expects " +
                  std::string(sig.is_variadic ? "at least " : "") +
                  std::to_string(required), func_.inst(i).loc);
            return;
        }
        for (uint32_t a = 0; a < sig.params.size(); ++a) {
            if (func_.value_type(args[a]) != sig.params[a].type) {
                error(inst_label(b, i) + ": call argument " + std::to_string(a) +
                      " has type " + types_.spelling(func_.value_type(args[a])) +
                      ", signature expects " + types_.spelling(sig.params[a].type),
                      func_.inst(i).loc);
            }
        }
        size_t variadic_end = args.size() - (has_trailing_dest(sig) ? 1 : 0);
        for (size_t a = sig.params.size(); a < variadic_end; ++a) {
            check_value_type(func_.value_type(args[a]),
                             inst_label(b, i) + ": variadic argument");
        }
        if (has_trailing_dest(sig) &&
            !types_.is_ptr(func_.value_type(args[args.size() - 1]))) {
            error(inst_label(b, i) +
                  ": multi-register return requires a trailing destination pointer");
        }
    }

    void check_call_result(BlockId b, InstId i, const SigData& sig) {
        const InstData& data = func_.inst(i);
        if (sig.ret_class == RetClass::Scalar) {
            if (!data.result.is_valid()) {
                error(inst_label(b, i) + ": scalar call must produce a result");
            } else if (data.type != sig.ret_type) {
                error(inst_label(b, i) + ": call result type " +
                      types_.spelling(data.type) + " does not match signature return " +
                      types_.spelling(sig.ret_type));
            }
        } else if (data.result.is_valid()) {
            error(inst_label(b, i) + ": non-scalar call must not produce a result");
        }
    }

    void check_inst(BlockId b, InstId i) {
        const InstData& data = func_.inst(i);
        int expected_ops = opcode_operand_count(data.op);
        auto ops = func_.operands(i);
        if (expected_ops >= 0 && ops.size() != static_cast<uint32_t>(expected_ops)) {
            error(inst_label(b, i) + ": expected " + std::to_string(expected_ops) +
                  " operands, got " + std::to_string(ops.size()));
            return;
        }
        if (!check_operand_values(b, i)) {
            return;
        }
        check_volatile_flag(b, i);
        if (data.result.is_valid()) {
            check_value_type(data.type, inst_label(b, i) + ": result");
        }
        for (uint32_t index = 0; index < ops.size(); ++index) {
            check_value_type(func_.value_type(ops[index]),
                             inst_label(b, i) + ": operand " + std::to_string(index));
        }

        switch (data.op) {
            case Opcode::StackAlloc:
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                if (stack_alloc_align_log2(data.aux) >= 32) {
                    error(inst_label(b, i) + ": unreasonable alignment");
                }
                break;
            case Opcode::StackAllocDyn:
                require_type(b, i, 0, size_int_type());
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                if (data.aux >= 32) {
                    error(inst_label(b, i) + ": unreasonable alignment");
                }
                break;
            case Opcode::StackSave:
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                break;
            case Opcode::StackRestore:
                require_ptr(b, i, 0);
                break;
            case Opcode::Load:
                require_ptr(b, i, 0);
                if (data.aux >= 32) {
                    error(inst_label(b, i) + ": unreasonable alignment");
                }
                break;
            case Opcode::Store:
                require_ptr(b, i, 1);
                if (data.aux >= 32) {
                    error(inst_label(b, i) + ": unreasonable alignment");
                }
                break;
            case Opcode::Memcpy:
            case Opcode::Memmove:
                require_ptr(b, i, 0);
                require_ptr(b, i, 1);
                require_type(b, i, 2, size_int_type());
                break;
            case Opcode::Memset:
                require_ptr(b, i, 0);
                require_type(b, i, 1, types::I8);
                require_type(b, i, 2, size_int_type());
                break;

            case Opcode::AtomicLoad: {
                require_ptr(b, i, 0);
                MemOrder order = atomic_access_order(data.aux);
                if (!mem_order_valid(static_cast<uint64_t>(order))) {
                    error(inst_label(b, i) + ": invalid memory order");
                } else if (order == MemOrder::Release || order == MemOrder::AcqRel) {
                    error(inst_label(b, i) + ": load order cannot be a release order");
                }
                if (atomic_access_align_log2(data.aux) >= 32) {
                    error(inst_label(b, i) + ": unreasonable alignment");
                }
                break;
            }
            case Opcode::AtomicStore: {
                require_ptr(b, i, 1);
                MemOrder order = atomic_access_order(data.aux);
                if (!mem_order_valid(static_cast<uint64_t>(order))) {
                    error(inst_label(b, i) + ": invalid memory order");
                } else if (order == MemOrder::Acquire || order == MemOrder::AcqRel) {
                    error(inst_label(b, i) + ": store order cannot be an acquire order");
                }
                if (atomic_access_align_log2(data.aux) >= 32) {
                    error(inst_label(b, i) + ": unreasonable alignment");
                }
                break;
            }
            case Opcode::AtomicRmw: {
                require_ptr(b, i, 0);
                if (rmw_op(data.aux) > RmwOp::UMin) {
                    error(inst_label(b, i) + ": invalid atomic operation");
                }
                if (!mem_order_valid(static_cast<uint64_t>(rmw_order(data.aux)))) {
                    error(inst_label(b, i) + ": invalid memory order");
                }
                if (!types_.is_int(op_type(i, 1))) {
                    error(inst_label(b, i) + ": operand must be an integer");
                } else if (data.type != op_type(i, 1)) {
                    error(inst_label(b, i) + ": result type must match the operand");
                }
                break;
            }
            case Opcode::AtomicCas: {
                require_ptr(b, i, 0);
                require_type(b, i, 2, op_type(i, 1));
                if (data.type != op_type(i, 1)) {
                    error(inst_label(b, i) + ": result type must match the operands");
                }
                if (!mem_order_valid(
                        static_cast<uint64_t>(cas_success_order(data.aux))) ||
                    !mem_order_valid(
                        static_cast<uint64_t>(cas_failure_order(data.aux)))) {
                    error(inst_label(b, i) + ": invalid memory order");
                } else {
                    MemOrder failure = cas_failure_order(data.aux);
                    if (failure == MemOrder::Release || failure == MemOrder::AcqRel) {
                        error(inst_label(b, i) +
                              ": failure order cannot be a release order");
                    }
                }
                break;
            }
            case Opcode::Fence:
                if (!mem_order_valid(data.aux)) {
                    error(inst_label(b, i) + ": invalid memory order");
                }
                break;

            case Opcode::Iadd:
            case Opcode::Isub:
            case Opcode::Imul:
            case Opcode::Iand:
            case Opcode::Ior:
            case Opcode::Ixor:
            case Opcode::Shl:
            case Opcode::Sdiv:
            case Opcode::Udiv:
            case Opcode::Srem:
            case Opcode::Urem:
            case Opcode::Ashr:
            case Opcode::Lshr:
                require_int(b, i, 0);
                require_type(b, i, 1, op_type(i, 0));
                if (data.type != op_type(i, 0)) {
                    error(inst_label(b, i) + ": result type must match operands");
                }
                break;

            case Opcode::Bswap:
            case Opcode::Clz:
            case Opcode::Ctz:
            case Opcode::Popcnt:
                require_int(b, i, 0);
                if (data.type != op_type(i, 0)) {
                    error(inst_label(b, i) + ": result type must match the operand");
                }
                if (data.op == Opcode::Bswap && types_.is_int(op_type(i, 0)) &&
                    types_.int_width(op_type(i, 0)) % 16 != 0) {
                    error(inst_label(b, i) + ": bswap requires a multi-byte integer");
                }
                break;

            case Opcode::Fadd:
            case Opcode::Fsub:
            case Opcode::Fmul:
            case Opcode::Fdiv:
            case Opcode::Frem:
                if (!types_.is_float(op_type(i, 0))) {
                    error(inst_label(b, i) + ": operands must be floating point");
                    break;
                }
                require_type(b, i, 1, op_type(i, 0));
                if (data.type != op_type(i, 0)) {
                    error(inst_label(b, i) + ": result type must match operands");
                }
                break;
            case Opcode::Fneg:
                if (!types_.is_float(op_type(i, 0))) {
                    error(inst_label(b, i) + ": operand must be floating point");
                } else if (data.type != op_type(i, 0)) {
                    error(inst_label(b, i) + ": result type must match operand");
                }
                break;

            case Opcode::Icmp: {
                TypeId lhs = op_type(i, 0);
                if (!types_.is_int(lhs) && !types_.is_ptr(lhs)) {
                    error(inst_label(b, i) + ": operands must be integers or pointers");
                }
                require_type(b, i, 1, lhs);
                if (data.type != types::I8) {
                    error(inst_label(b, i) + ": result must be i8");
                }
                if (data.aux > static_cast<uint64_t>(IntCond::Uge)) {
                    error(inst_label(b, i) + ": invalid condition code");
                }
                break;
            }
            case Opcode::Fcmp:
                if (!types_.is_float(op_type(i, 0))) {
                    error(inst_label(b, i) + ": operands must be floating point");
                }
                require_type(b, i, 1, op_type(i, 0));
                if (data.type != types::I8) {
                    error(inst_label(b, i) + ": result must be i8");
                }
                if (data.aux > static_cast<uint64_t>(FloatCond::Uge)) {
                    error(inst_label(b, i) + ": invalid condition code");
                }
                break;

            case Opcode::Trunc:
            case Opcode::Zext:
            case Opcode::Sext: {
                TypeId from = op_type(i, 0);
                if (!types_.is_int(from) || !types_.is_int(data.type)) {
                    error(inst_label(b, i) + ": int cast requires integer types");
                    break;
                }
                uint16_t from_width = types_.int_width(from);
                uint16_t to_width = types_.int_width(data.type);
                bool ok = data.op == Opcode::Trunc ? to_width < from_width
                                                   : to_width > from_width;
                if (!ok) {
                    error(inst_label(b, i) + ": invalid width change i" +
                          std::to_string(from_width) + " -> i" +
                          std::to_string(to_width));
                }
                break;
            }
            case Opcode::Fptrunc:
            case Opcode::Fpext: {
                TypeId from = op_type(i, 0);
                if (!types_.is_float(from) || !types_.is_float(data.type)) {
                    error(inst_label(b, i) + ": float cast requires float types");
                    break;
                }
                uint32_t from_width = float_bit_width(types_.type(from).float_kind);
                uint32_t to_width = float_bit_width(types_.type(data.type).float_kind);
                bool ok = data.op == Opcode::Fptrunc ? to_width < from_width
                                                     : to_width > from_width;
                if (!ok) {
                    error(inst_label(b, i) + ": invalid float width change");
                }
                break;
            }
            case Opcode::Fptosi:
            case Opcode::Fptoui:
                if (!types_.is_float(op_type(i, 0)) || !types_.is_int(data.type)) {
                    error(inst_label(b, i) + ": requires float operand, int result");
                }
                break;
            case Opcode::Sitofp:
            case Opcode::Uitofp:
                if (!types_.is_int(op_type(i, 0)) || !types_.is_float(data.type)) {
                    error(inst_label(b, i) + ": requires int operand, float result");
                }
                break;
            case Opcode::Ptrtoint:
                if (!types_.is_ptr(op_type(i, 0)) || !types_.is_int(data.type)) {
                    error(inst_label(b, i) + ": requires ptr operand, int result");
                }
                break;
            case Opcode::Inttoptr:
                if (!types_.is_int(op_type(i, 0)) || !types_.is_ptr(data.type)) {
                    error(inst_label(b, i) + ": requires int operand, ptr result");
                }
                break;
            case Opcode::Bitcast: {
                TypeId from = op_type(i, 0);
                if (types_.is_ptr(from) || types_.is_ptr(data.type)) {
                    error(inst_label(b, i) +
                          ": pointers are not bitcastable (use ptrtoint/inttoptr)");
                    break;
                }
                auto bits = [&](TypeId t) -> uint32_t {
                    const TypeData& td = types_.type(t);
                    return td.kind == TypeKind::Int
                               ? td.int_width
                               : float_bit_width(td.float_kind);
                };
                if (!types_.is_scalar(from) || !types_.is_scalar(data.type) ||
                    bits(from) != bits(data.type)) {
                    error(inst_label(b, i) + ": bitcast requires equal bit widths");
                }
                break;
            }

            case Opcode::PtrAdd:
                require_ptr(b, i, 0);
                require_type(b, i, 1, size_int_type());
                if (data.type != op_type(i, 0)) {
                    error(inst_label(b, i) + ": result type must match the pointer");
                }
                break;

            case Opcode::Select:
                require_type(b, i, 0, types::I8);
                require_type(b, i, 2, op_type(i, 1));
                if (data.type != op_type(i, 1)) {
                    error(inst_label(b, i) + ": result type must match the inputs");
                }
                break;

            case Opcode::VaStart:
                require_ptr(b, i, 0);
                if (!sig().is_variadic) {
                    error(inst_label(b, i) + ": va_start in a non-variadic function");
                }
                break;

            case Opcode::InlineAsm: {
                uint32_t payload = static_cast<uint32_t>(data.aux);
                if (payload >= mod_.asm_payload_count()) {
                    error(inst_label(b, i) + ": invalid asm payload index");
                    break;
                }
                const AsmPayload& asm_payload = mod_.asm_payload(payload);
                if (asm_payload.constraints.size() != ops.size()) {
                    error(inst_label(b, i) + ": asm has " +
                          std::to_string(asm_payload.constraints.size()) +
                          " constraints for " + std::to_string(ops.size()) +
                          " operands");
                }
                if (asm_payload.operand_types.size() != ops.size()) {
                    error(inst_label(b, i) + ": asm has " +
                          std::to_string(asm_payload.operand_types.size()) +
                          " operand types for " + std::to_string(ops.size()) +
                          " operands");
                }
                if (!asm_payload.register_bindings.empty() &&
                    asm_payload.register_bindings.size() != ops.size()) {
                    error(inst_label(b, i) + ": asm has " +
                          std::to_string(asm_payload.register_bindings.size()) +
                          " register bindings for " +
                          std::to_string(ops.size()) + " operands");
                }
                break;
            }

            case Opcode::EhAllocException:
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                break;
            case Opcode::EhLandingPad: {
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                uint32_t payload = static_cast<uint32_t>(data.aux);
                if (payload >= mod_.eh_landing_pad_payload_count()) {
                    error(inst_label(b, i) + ": invalid landing-pad payload index");
                    break;
                }
                const EhLandingPadPayload& clauses =
                    mod_.eh_landing_pad_payload(payload);
                if (!clauses.is_cleanup && !clauses.has_catch_all &&
                    clauses.clause_typeinfos.empty()) {
                    error(inst_label(b, i) + ": landing pad has no clauses");
                }
                for (GlobalId clause : clauses.clause_typeinfos) {
                    if (!mod_.is_valid(clause)) {
                        error(inst_label(b, i) +
                              ": landing-pad clause references an invalid global");
                    }
                }
                break;
            }
            case Opcode::EhSelector: {
                require_ptr(b, i, 0);
                if (data.type != types::I32) {
                    error(inst_label(b, i) + ": result must be i32");
                }
                const ValueData& pad_value = func_.value(ops[0]);
                if (pad_value.kind != ValueKind::InstResult ||
                    !func_.is_valid(InstId{
                        static_cast<uint32_t>(pad_value.payload)}) ||
                    func_.inst(InstId{static_cast<uint32_t>(pad_value.payload)}).op !=
                        Opcode::EhLandingPad) {
                    error(inst_label(b, i) +
                          ": operand must be an eh_landing_pad result");
                }
                break;
            }
            case Opcode::EhTypeId:
                require_ptr(b, i, 0);
                if (data.type != types::I32) {
                    error(inst_label(b, i) + ": result must be i32");
                }
                break;
            case Opcode::CatchBegin:
                require_ptr(b, i, 0);
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                break;
            case Opcode::CatchEnd:
                break;

            case Opcode::Trap:
                break;
            case Opcode::FrameAddr:
            case Opcode::ReturnAddr:
                if (data.type != types::PTR) {
                    error(inst_label(b, i) + ": result must be ptr");
                }
                break;

            case Opcode::Jump:
                check_block_call(b, i, BlockCallId{aux_low(data.aux)});
                break;
            case Opcode::BrIf:
                require_type(b, i, 0, types::I8);
                check_block_call(b, i, BlockCallId{aux_low(data.aux)});
                check_block_call(b, i, BlockCallId{aux_high(data.aux)});
                break;
            case Opcode::Switch: {
                require_int(b, i, 0);
                check_block_call(b, i, BlockCallId{aux_low(data.aux)});
                if (aux_high(data.aux) >= func_.jump_table_count()) {
                    error(inst_label(b, i) + ": invalid jump-table index");
                    break;
                }
                std::unordered_set<uint64_t> seen;
                for (const SwitchCase& c : func_.jump_table(aux_high(data.aux))) {
                    if (!seen.insert(c.value).second) {
                        error(inst_label(b, i) + ": duplicate case value " +
                              std::to_string(c.value));
                    }
                    check_block_call(b, i, c.target);
                }
                break;
            }
            case Opcode::AsmGoto: {
                uint32_t payload = static_cast<uint32_t>(data.aux);
                if (payload >= mod_.asm_payload_count()) {
                    error(inst_label(b, i) + ": invalid asm payload index");
                    break;
                }
                const AsmPayload& asm_payload = mod_.asm_payload(payload);
                if (asm_payload.constraints.size() != ops.size() ||
                    asm_payload.operand_types.size() != ops.size()) {
                    error(inst_label(b, i) +
                          ": asm goto metadata does not match its operands");
                }
                uint32_t list = static_cast<uint32_t>(data.aux2);
                if (list >= func_.block_call_list_count()) {
                    error(inst_label(b, i) + ": invalid label-list index");
                    break;
                }
                auto calls = func_.block_call_list(list);
                if (calls.empty()) {
                    error(inst_label(b, i) +
                          ": asm goto has no fallthrough edge");
                    break;
                }
                for (BlockCallId call : calls) {
                    check_block_call(b, i, call, /*allow_args=*/false);
                    if (func_.is_valid(call) &&
                        func_.is_valid(func_.block_call(call).target) &&
                        func_.block(func_.block_call(call).target)
                                .param_count != 0) {
                        error(inst_label(b, i) +
                              ": asm goto target has parameters");
                    }
                }
                break;
            }
            case Opcode::BrIndirect: {
                require_ptr(b, i, 0);
                if (aux_low(data.aux) >= func_.block_call_list_count()) {
                    error(inst_label(b, i) + ": invalid target-list index");
                    break;
                }
                auto calls = func_.block_call_list(aux_low(data.aux));
                if (calls.empty()) {
                    error(inst_label(b, i) + ": empty plausible-target list");
                }
                for (BlockCallId call : calls) {
                    check_block_call(b, i, call, /*allow_args=*/false);
                    if (func_.is_valid(call) &&
                        func_.is_valid(func_.block_call(call).target) &&
                        func_.block(func_.block_call(call).target).param_count != 0) {
                        error(inst_label(b, i) +
                              ": indirect-branch target has parameters");
                    }
                }
                break;
            }
            case Opcode::Ret: {
                const SigData& data_sig = sig();
                switch (data_sig.ret_class) {
                    case RetClass::Void:
                    case RetClass::IndirectSret:
                        if (!ops.empty()) {
                            error(inst_label(b, i) +
                                  ": this return class carries no operand");
                        }
                        break;
                    case RetClass::Scalar:
                        if (ops.size() != 1) {
                            error(inst_label(b, i) + ": must return exactly one value");
                        } else {
                            require_type(b, i, 0, data_sig.ret_type);
                        }
                        break;
                    case RetClass::IntPair:
                    case RetClass::Hfa:
                        if (ops.size() != 1) {
                            error(inst_label(b, i) +
                                  ": must return the buffer pointer");
                        } else {
                            require_ptr(b, i, 0);
                        }
                        break;
                }
                break;
            }
            case Opcode::Unreachable:
                break;
            case Opcode::Throw:
                if (ops.size() != 2 && ops.size() != 3) {
                    error(inst_label(b, i) +
                          ": throw expects exception, typeinfo, and optional destructor");
                    break;
                }
                require_ptr(b, i, 0);
                require_ptr(b, i, 1);
                if (ops.size() == 3) {
                    require_ptr(b, i, 2);
                }
                break;
            case Opcode::Rethrow:
                break;
            case Opcode::Resume:
                require_ptr(b, i, 0);
                require_type(b, i, 1, types::I32);
                break;

            case Opcode::Call: {
                FuncId callee{static_cast<uint32_t>(data.aux)};
                if (!mod_.is_valid(callee)) {
                    error(inst_label(b, i) + ": invalid callee");
                    break;
                }
                const SigData& callee_sig =
                    types_.signature(mod_.function(callee).sig());
                check_call_args(b, i, callee_sig, ops);
                check_call_result(b, i, callee_sig);
                break;
            }
            case Opcode::Invoke: {
                FuncId callee{static_cast<uint32_t>(data.aux)};
                if (!mod_.is_valid(callee)) {
                    error(inst_label(b, i) + ": invalid callee");
                    break;
                }
                const SigData& callee_sig =
                    types_.signature(mod_.function(callee).sig());
                check_call_args(b, i, callee_sig, ops);
                check_call_result(b, i, callee_sig);
                check_block_call(b, i, BlockCallId{aux_low(data.aux2)});
                BlockCallId unwind{aux_high(data.aux2)};
                check_block_call(b, i, unwind, true, true);
                if (func_.is_valid(unwind) &&
                    func_.is_valid(func_.block_call(unwind).target) &&
                    !block_begins_with(func_.block_call(unwind).target,
                                       Opcode::EhLandingPad)) {
                    error(inst_label(b, i) +
                          ": invoke unwind target must begin with eh_landing_pad");
                }
                break;
            }
            case Opcode::CallIndirect: {
                SigId sig_id{static_cast<uint32_t>(data.aux)};
                if (!types_.is_valid(sig_id)) {
                    error(inst_label(b, i) + ": invalid signature");
                    break;
                }
                if (ops.empty()) {
                    error(inst_label(b, i) + ": missing callee operand");
                    break;
                }
                require_ptr(b, i, 0);
                const SigData& callee_sig = types_.signature(sig_id);
                check_call_args(b, i, callee_sig, ops.subspan(1));
                check_call_result(b, i, callee_sig);
                break;
            }
            case Opcode::TailCallIndirect: {
                SigId sig_id{static_cast<uint32_t>(data.aux)};
                if (!types_.is_valid(sig_id)) {
                    error(inst_label(b, i) + ": invalid signature");
                    break;
                }
                if (ops.empty()) {
                    error(inst_label(b, i) + ": missing callee operand");
                    break;
                }
                require_ptr(b, i, 0);
                const SigData& callee_sig = types_.signature(sig_id);
                if (callee_sig.ret_class != RetClass::Void) {
                    error(inst_label(b, i) +
                          ": tail_call_indirect requires a void signature");
                }
                check_call_args(b, i, callee_sig, ops.subspan(1));
                break;
            }
            case Opcode::InvokeIndirect: {
                SigId sig_id{static_cast<uint32_t>(data.aux)};
                if (!types_.is_valid(sig_id)) {
                    error(inst_label(b, i) + ": invalid signature");
                    break;
                }
                if (ops.empty()) {
                    error(inst_label(b, i) + ": missing callee operand");
                    break;
                }
                require_ptr(b, i, 0);
                const SigData& callee_sig = types_.signature(sig_id);
                check_call_args(b, i, callee_sig, ops.subspan(1));
                check_call_result(b, i, callee_sig);
                check_block_call(b, i, BlockCallId{aux_low(data.aux2)});
                BlockCallId unwind{aux_high(data.aux2)};
                check_block_call(b, i, unwind, true, true);
                if (func_.is_valid(unwind) &&
                    func_.is_valid(func_.block_call(unwind).target) &&
                    !block_begins_with(func_.block_call(unwind).target,
                                       Opcode::EhLandingPad)) {
                    error(inst_label(b, i) +
                          ": invoke unwind target must begin with eh_landing_pad");
                }
                break;
            }
        }
    }

    void check_block_dominance(BlockId b) {
        std::vector<BlockCallId> succs;
        for (InstId i = func_.block(b).first; i.is_valid(); i = func_.inst(i).next) {
            uint32_t use_pos = inst_pos_.at(i.index);
            for (ValueId op : func_.operands(i)) {
                check_use(b, i, use_pos, op);
            }
            func_.successors(i, succs);
            for (BlockCallId call : succs) {
                for (ValueId arg : func_.block_call_args(call)) {
                    check_use(b, i, use_pos, arg);
                }
            }
        }
    }

    void check_use(BlockId use_block, InstId use_inst, uint32_t use_pos, ValueId v) {
        if (!func_.is_valid(v)) {
            return;
        }
        const ValueData& data = func_.value(v);
        if (data.kind == ValueKind::InstResult) {
            InstId def = func_.def_inst(v);
            BlockId def_block = func_.inst(def).block;
            if (!def_block.is_valid()) {
                error(inst_label(use_block, use_inst) +
                      ": use of a value whose defining instruction is not attached",
                      func_.inst(use_inst).loc);
                return;
            }
            if (def_block == use_block) {
                if (inst_pos_.at(def.index) >= use_pos) {
                    error(inst_label(use_block, use_inst) +
                          ": use of a value before its definition",
                          func_.inst(use_inst).loc);
                }
            } else if (!domtree_.dominates(def_block, use_block)) {
                error(inst_label(use_block, use_inst) + ": definition in " +
                      block_label(def_block) + " does not dominate use in " +
                      block_label(use_block), func_.inst(use_inst).loc);
            }
        } else if (data.kind == ValueKind::BlockParam) {
            BlockId def_block{static_cast<uint32_t>(data.payload)};
            if (def_block != use_block && !domtree_.dominates(def_block, use_block)) {
                error(inst_label(use_block, use_inst) + ": block parameter of " +
                      block_label(def_block) + " does not dominate use in " +
                      block_label(use_block), func_.inst(use_inst).loc);
            }
        }

    }

    const Module& mod_;
    const Function& func_;
    const TypeTable& types_;
    VerifyResult& result_;
    DominatorTree domtree_;
    std::unordered_map<uint32_t, uint32_t> block_numbers_;
    std::unordered_map<uint32_t, uint32_t> inst_pos_;
};

void check_global(const Module& mod, GlobalId id, VerifyResult& result) {
    const GlobalData& data = mod.global(id);
    auto error = [&](const std::string& message) {
        result.diags.push_back({VerifierDiag::Severity::Error,
                                "global @" + data.name + ": " + message, data.loc});
    };
    if (data.align_bytes == 0 || (data.align_bytes & (data.align_bytes - 1)) != 0) {
        error("alignment must be a power of two");
    }
    if (data.linkage == Linkage::Common && data.init.kind == GlobalInitKind::Bytes) {
        error("common linkage requires a zero initializer");
    }
    if (data.section == SectionKind::Cstring) {
        if (data.init.kind != GlobalInitKind::Bytes || data.init.bytes.empty()) {
            error("cstring global requires a byte initializer");
        } else {
            if (data.init.bytes.back() != 0) {
                error("cstring initializer must end with a NUL byte");
            }
            for (size_t i = 0; i + 1 < data.init.bytes.size(); ++i) {
                if (data.init.bytes[i] == 0) {
                    error("cstring initializer has an interior NUL byte");
                    break;
                }
            }
            if (!data.init.relocs.empty()) {
                error("cstring global cannot carry relocations");
            }
        }
    }
    if (data.init.kind != GlobalInitKind::Bytes) {
        if (!data.init.bytes.empty() || !data.init.relocs.empty()) {
            error("non-bytes initializer carries data");
        }
        return;
    }
    if (data.init.bytes.size() != data.size_bytes) {
        error("initializer has " + std::to_string(data.init.bytes.size()) +
              " bytes but the global is " + std::to_string(data.size_bytes) +
              " bytes");
    }
    uint32_t ptr_size = mod.ptr_size_bytes();
    for (const InitReloc& reloc : data.init.relocs) {
        bool target_ok = reloc.is_function
                             ? mod.is_valid(FuncId{reloc.target_index})
                             : mod.is_valid(GlobalId{reloc.target_index});
        if (!target_ok) {
            error("relocation references an invalid symbol");
        }
        if (reloc.offset + ptr_size > data.init.bytes.size()) {
            error("relocation at offset " + std::to_string(reloc.offset) +
                  " does not fit in the initializer");
        }
        if (reloc.offset % ptr_size != 0) {
            error("relocation at offset " + std::to_string(reloc.offset) +
                  " is not pointer-aligned");
        }
    }
}

} // namespace

void verify_function(const Module& mod, const Function& func, VerifyResult& result) {
    FunctionVerifier(mod, func, result).run();
}

VerifyResult verify_module(const Module& mod) {
    VerifyResult result;
    std::unordered_map<std::string, std::string> symbols;
    auto check_symbol = [&](const std::string& name, const std::string& what) {
        auto [it, inserted] = symbols.emplace(name, what);
        if (!inserted) {
            result.diags.push_back({VerifierDiag::Severity::Error,
                                    what + " @" + name + " collides with " +
                                        it->second + " of the same name",
                                    SrcLoc{}});
        }
    };
    for (uint32_t i = 1; i <= mod.function_count(); ++i) {
        check_symbol(mod.function(FuncId{i}).name(), "function");
    }
    for (uint32_t i = 1; i <= mod.global_count(); ++i) {
        check_symbol(mod.global(GlobalId{i}).name, "global");
        check_global(mod, GlobalId{i}, result);
    }
    for (const CtorEntry& ctor : mod.ctors()) {
        if (!mod.is_valid(ctor.func)) {
            result.diags.push_back({VerifierDiag::Severity::Error,
                                    "ctor entry references an invalid function",
                                    SrcLoc{}});
        } else if (mod.function(ctor.func).is_declaration()) {
            result.diags.push_back({VerifierDiag::Severity::Error,
                                    "ctor function @" +
                                        mod.function(ctor.func).name() +
                                        " is not defined",
                                    SrcLoc{}});
        }
    }
    for (uint32_t i = 1; i <= mod.function_count(); ++i) {
        verify_function(mod, mod.function(FuncId{i}), result);
    }
    return result;
}

} // namespace aburi::air
