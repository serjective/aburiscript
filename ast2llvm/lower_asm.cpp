#include "ast2llvm.h"
#include "../abi/mangle.h"
#include "../constexpr/consteval_compat.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <algorithm>
#include <array>
#include <cctype>
#include <limits>

void ASTToLLVM::convert_file_scope_asm(FileScopeAsmDecl *decl) {
    module->appendModuleInlineAsm(decl->asm_string);
}

// Translate GCC-style asm operand references to LLVM-style:
//   %% → %  (literal percent)
//   %N → $N  (operand reference)
//   %cN → ${N:c}  (operand with modifier, e.g. %w0 → ${0:w})
//   literal $ → $$  (escape for LLVM)
static std::string translate_gcc_to_llvm_asm(const std::string &tmpl) {
    std::string result;
    result.reserve(tmpl.size());
    for (size_t i = 0; i < tmpl.size(); i++) {
        if (tmpl[i] == '$') {
            result += "$$";
        } else if (tmpl[i] == '%') {
            if (i + 1 >= tmpl.size()) {
                result += '%';
                continue;
            }
            char next = tmpl[i + 1];
            if (next == '%') {
                // %% → literal %
                result += '%';
                i++;
            } else if (isdigit(next)) {
                // %N → $N (consume all digits for multi-digit operand numbers)
                result += '$';
                i++;
                while (i < tmpl.size() && isdigit(tmpl[i])) {
                    result += tmpl[i];
                    i++;
                }
                i--; // adjust for outer loop increment
            } else if (isalpha(next) && i + 2 < tmpl.size() && isdigit(tmpl[i + 2])) {
                // %cN → ${N:c} where c is a modifier letter (e.g. %w0 → ${0:w})
                char modifier = next;
                i += 2;
                std::string num;
                while (i < tmpl.size() && isdigit(tmpl[i])) {
                    num += tmpl[i];
                    i++;
                }
                i--; // adjust for outer loop increment
                result += "${" + num + ":" + modifier + "}";
            } else {
                // Unknown escape, pass through
                result += '%';
            }
        } else {
            result += tmpl[i];
        }
    }
    return result;
}

// LLVM on our targets rejects some GCC generic constraint classes.
// Lower them to register-compatible forms so extended asm remains representable.
static std::string normalize_gcc_constraint_for_llvm(std::string constraint) {
    for (char &ch : constraint) {
        if (ch == 'g' || ch == 'X') {
            ch = 'r';
        } else if (ch == 'Q') {
            // ARM memory operand class; representable as generic memory in LLVM.
            ch = 'm';
        }
    }
    return constraint;
}

static bool constraint_uses_memory_operand(const std::string& constraint) {
    return constraint.find('m') != std::string::npos;
}

static std::string add_llvm_indirect_memory_marker(std::string constraint) {
    size_t m_pos = constraint.find('m');
    if (m_pos != std::string::npos) {
        if (m_pos == 0 || constraint[m_pos - 1] != '*') {
            constraint.insert(m_pos, "*");
        }
    }
    return constraint;
}

static std::string strip_output_constraint_prefix(std::string constraint) {
    if (!constraint.empty() && (constraint[0] == '=' || constraint[0] == '+')) {
        constraint.erase(0, 1);
    }
    return constraint;
}

static bool constraint_prefers_immediate_operand(const std::string& constraint) {
    return constraint.find('i') != std::string::npos ||
           constraint.find('n') != std::string::npos;
}

static bool constraint_requires_immediate_operand(const std::string& constraint) {
    bool has_immediate = false;
    bool has_non_immediate_alternative = false;
    for (char ch : constraint) {
        if (ch == 'i' || ch == 'n') {
            has_immediate = true;
            continue;
        }
        if (ch == 'r' || ch == 'm' || ch == 'p' ||
            ch == 'o' || ch == 'V' ||
            std::isdigit(static_cast<unsigned char>(ch))) {
            has_non_immediate_alternative = true;
        }
    }
    return has_immediate && !has_non_immediate_alternative;
}

static std::string describe_consteval_failure(const ConstEvalResult& result) {
    if (!result.message.empty()) {
        return result.message;
    }
    if (!result.diagnostics.empty() && !result.diagnostics.front().message.empty()) {
        return result.diagnostics.front().message;
    }
    switch (result.status) {
        case ConstEvalStatus::NotEvaluated:
            return "expression could not be evaluated at compile time";
        case ConstEvalStatus::NotConstant:
            return "expression is not constant";
        case ConstEvalStatus::Error:
            return "constant-evaluation failed";
        case ConstEvalStatus::Constant:
            return "expression is not an integer constant expression";
    }
    return "expression is not constant";
}

static Expr* strip_noop_implicit_casts(Expr* expr) {
    while (auto* cast = dyn_cast<ImplicitCast>(expr)) {
        switch (cast->kind) {
            case ImplicitCastTypes::LVALUE_TO_RVALUE:
            case ImplicitCastTypes::ARRAY_TO_POINTER:
            case ImplicitCastTypes::RAW_CAST:
            case ImplicitCastTypes::ARITH_CAST:
                expr = cast->expr.get();
                continue;
            default:
                return expr;
        }
    }
    return expr;
}

struct AsmPointerIndexExpr {
    std::shared_ptr<Symbol> base_symbol;
    int64_t index = 0;
};

static std::optional<AsmPointerIndexExpr> try_extract_pointer_index_expr(Expr* expr) {
    expr = strip_noop_implicit_casts(expr);
    auto* unary = dyn_cast<UnaryOperation>(expr);
    if (!unary || unary->uop != UnaryOpTypes::ADDRESS_OF || !unary->exp) {
        return std::nullopt;
    }

    Expr* inner = strip_noop_implicit_casts(unary->exp.get());
    if (auto* subscript = dyn_cast<ArraySubscriptExpr>(inner)) {
        Expr* array_expr = strip_noop_implicit_casts(subscript->array.get());
        auto* base_var = dyn_cast<VarRef>(array_expr);
        if (!base_var || !base_var->symref || !subscript->index) {
            return std::nullopt;
        }
        auto idx = try_evaluate_with_consteval_compat(
            subscript->index.get(), ConstEvalMode::c_ice());
        if (!idx.has_value()) {
            return std::nullopt;
        }
        return AsmPointerIndexExpr{base_var->symref, idx.value()};
    }

    if (auto* base_var = dyn_cast<VarRef>(inner)) {
        if (!base_var->symref) {
            return std::nullopt;
        }
        return AsmPointerIndexExpr{base_var->symref, 0};
    }

    return std::nullopt;
}

struct AsmImmediateEvalResult {
    std::optional<int64_t> value;
    ConstEvalResult consteval_result = ConstEvalResult::not_evaluated(
        "expression could not be evaluated at compile time");
};

static AsmImmediateEvalResult evaluate_asm_immediate_expr(Expr* expr) {
    AsmImmediateEvalResult result;
    if (!expr) {
        result.consteval_result = ConstEvalResult::not_evaluated("null expression");
        return result;
    }

    result.consteval_result = evaluate_with_consteval_compat(
        expr, ConstEvalMode::c_ice());
    if (result.consteval_result.status == ConstEvalStatus::Constant &&
        result.consteval_result.int_value.has_value()) {
        result.value = result.consteval_result.int_value.value();
        return result;
    }

    Expr* core = strip_noop_implicit_casts(expr);
    auto* bin = dyn_cast<BinaryOperation>(core);
    if (!bin || bin->bop != BinOpTypes::SUB) {
        return result;
    }

    auto lhs = try_extract_pointer_index_expr(bin->left.get());
    auto rhs = try_extract_pointer_index_expr(bin->right.get());
    if (!lhs.has_value() || !rhs.has_value()) {
        return result;
    }
    if (!lhs->base_symbol || !rhs->base_symbol ||
        lhs->base_symbol.get() != rhs->base_symbol.get()) {
        return result;
    }
    result.value = lhs->index - rhs->index;
    return result;
}

void ASTToLLVM::convert_asm_statement(AsmStmt *stmt) {
    if (stmt->is_basic()) {
        // Basic asm: no operands, always has side effects
        std::string llvm_template = translate_gcc_to_llvm_asm(stmt->asm_template);
        auto *asm_func_ty = llvm::FunctionType::get(
            llvm::Type::getVoidTy(*context), false);
        auto *ia = llvm::InlineAsm::get(
            asm_func_ty,
            llvm_template,
            "",          // no constraints
            true,        // has side effects (basic asm is always volatile)
            false,       // not align stack
            llvm::InlineAsm::AD_ATT);
        builder.CreateCall(asm_func_ty, ia);
        return;
    }

    // Extended asm: translate %[name] symbolic references to %N positional references
    // Build name-to-index map: outputs are 0..N-1, inputs are N..N+M-1
    std::string asm_template = stmt->asm_template;
    {
        std::unordered_map<std::string, size_t> name_to_idx;
        size_t idx = 0;
        for (const auto &op : stmt->output_operands) {
            if (!op.symbolic_name.empty()) {
                name_to_idx[op.symbolic_name] = idx;
            }
            idx++;
        }
        for (const auto &op : stmt->input_operands) {
            if (!op.symbolic_name.empty()) {
                name_to_idx[op.symbolic_name] = idx;
            }
            idx++;
        }

        // Tied inputs from '+' constraints occupy implicit indices after inputs
        for (const auto &op : stmt->output_operands) {
            if (!op.constraint.empty() && op.constraint[0] == '+') {
                idx++; // skip tied input slot (no symbolic name for these)
            }
        }

        // Goto labels come after outputs + inputs + tied inputs
        // Track which indices are goto labels (for %l modifier stripping)
        std::unordered_set<size_t> goto_label_indices;
        for (const auto &label : stmt->goto_labels) {
            name_to_idx[label] = idx;
            goto_label_indices.insert(idx);
            idx++;
        }

        // Replace %[name] and %modifier[name] with %N / %modifierN in the template
        // %l[name] for goto labels keeps the 'l' modifier (LLVM uses ${N:l} for label printing)
        {
            std::string result;
            result.reserve(asm_template.size());
            for (size_t i = 0; i < asm_template.size(); i++) {
                if (asm_template[i] == '%' && i + 1 < asm_template.size()) {
                    // Check for %[name] (no modifier)
                    if (asm_template[i + 1] == '[') {
                        size_t close = asm_template.find(']', i + 2);
                        if (close != std::string::npos) {
                            std::string name = asm_template.substr(i + 2, close - (i + 2));
                            auto it = name_to_idx.find(name);
                            if (it != name_to_idx.end()) {
                                result += "%" + std::to_string(it->second);
                                i = close;
                                continue;
                            }
                        }
                    }
                    // Check for %c[name] (single-char modifier before [name])
                    if (isalpha(asm_template[i + 1]) && i + 2 < asm_template.size()
                        && asm_template[i + 2] == '[') {
                        char modifier = asm_template[i + 1];
                        size_t close = asm_template.find(']', i + 3);
                        if (close != std::string::npos) {
                            std::string name = asm_template.substr(i + 3, close - (i + 3));
                            auto it = name_to_idx.find(name);
                            if (it != name_to_idx.end()) {
                                result += "%";
                                result += modifier;
                                result += std::to_string(it->second);
                                i = close;
                                continue;
                            }
                        }
                    }
                }
                result += asm_template[i];
            }
            asm_template = std::move(result);
        }
    }

    // Now translate GCC % escapes to LLVM $ escapes
    asm_template = translate_gcc_to_llvm_asm(asm_template);

    std::string constraints_str;
    std::vector<llvm::Type*> output_types;
    std::vector<llvm::Value*> output_addrs;
    std::vector<llvm::Value*> input_values;
    std::vector<llvm::Type*> input_types;
    std::vector<llvm::Type*> input_element_types;
    std::vector<int> output_model_index(stmt->output_operands.size(), -1);
    std::vector<llvm::Value*> memory_output_addrs(stmt->output_operands.size(), nullptr);
    std::vector<llvm::Type*> memory_output_element_types(stmt->output_operands.size(), nullptr);
    std::vector<bool> memory_output_tied(stmt->output_operands.size(), false);
    bool needs_implicit_memory_clobber = false;
    bool has_memory_clobber = false;
    auto template_has_non_whitespace = [](const std::string& text) -> bool {
        return text.find_first_not_of(" \t\r\n") != std::string::npos;
    };
    bool has_template_text = template_has_non_whitespace(stmt->asm_template);

    // Process output operands
    for (size_t out_idx = 0; out_idx < stmt->output_operands.size(); ++out_idx) {
        auto &op = stmt->output_operands[out_idx];
        std::string normalized_constraint = normalize_gcc_constraint_for_llvm(op.constraint);
        bool memory_output = constraint_uses_memory_operand(normalized_constraint);
        // Empty-template memory outputs are frequently used as compiler barriers.
        // Model these as a memory clobber instead of an IR output value.
        if (!has_template_text && memory_output) {
            needs_implicit_memory_clobber = true;
            continue;
        }
        auto [addr, ctype] = get_lvalue(op.expr.get());
        if (!addr || !ctype) {
            return;
        }
        (void)ctype;
        if (!constraints_str.empty()) constraints_str += ",";
        if (memory_output) {
            std::string output_constraint = add_llvm_indirect_memory_marker(normalized_constraint);
            // LLVM IR doesn't support '+' directly: convert '+*m' to '=*m'
            // (the tied input is added separately below).
            if (!output_constraint.empty() && output_constraint[0] == '+') {
                output_constraint[0] = '=';
                memory_output_tied[out_idx] = true;
            }
            constraints_str += output_constraint;
            input_values.push_back(addr);
            input_types.push_back(addr->getType());
            input_element_types.push_back(convert_type(ctype));
            memory_output_addrs[out_idx] = addr;
            memory_output_element_types[out_idx] = convert_type(ctype);
            continue;
        }
        output_addrs.push_back(addr);
        llvm::Type *llvm_type = convert_type(op.expr->get_type());
        output_types.push_back(llvm_type);
        output_model_index[out_idx] = static_cast<int>(output_types.size()) - 1;
        std::string output_constraint = normalized_constraint;
        // LLVM IR doesn't support '+' directly: convert '+r' to '=r'
        // (the tied input is added separately below)
        if (!output_constraint.empty() && output_constraint[0] == '+') {
            output_constraint[0] = '=';
        }
        constraints_str += output_constraint;
    }

    // Process input operands
    for (auto &op : stmt->input_operands) {
        std::string constraint = normalize_gcc_constraint_for_llvm(op.constraint);
        if (constraint_uses_memory_operand(constraint)) {
            auto [addr, ctype] = get_lvalue(op.expr.get());
            if (!addr || !ctype) {
                return;
            }
            (void)ctype;
            input_values.push_back(addr);
            input_types.push_back(addr->getType());
            input_element_types.push_back(convert_type(ctype));
            constraint = add_llvm_indirect_memory_marker(constraint);
        } else {
            llvm::Value *val = nullptr;
            if (constraint_prefers_immediate_operand(constraint)) {
                AsmImmediateEvalResult const_eval = evaluate_asm_immediate_expr(op.expr.get());
                if (const_eval.value.has_value() && op.expr && op.expr->get_type()) {
                    llvm::Type *expr_ty = convert_type(op.expr->get_type());
                    if (auto *int_ty = llvm::dyn_cast<llvm::IntegerType>(expr_ty)) {
                        bool is_unsigned = op.expr->get_type()->isUnsigned();
                        llvm::APInt imm_bits(
                            int_ty->getBitWidth(),
                            static_cast<uint64_t>(const_eval.value.value()),
                            !is_unsigned);
                        val = llvm::ConstantInt::get(*context, imm_bits);
                    }
                }
                if (!val && constraint_requires_immediate_operand(constraint)) {
                    error(
                        "asm immediate input constraint requires compile-time integer constant expression: " +
                            describe_consteval_failure(const_eval.consteval_result),
                        op.loc);
                    return;
                }
            }
            if (!val) {
                val = convert_expression(op.expr.get());
            }
            input_values.push_back(val);
            input_types.push_back(val->getType());
            input_element_types.push_back(nullptr);
        }
        if (!constraints_str.empty()) constraints_str += ",";
        constraints_str += constraint;
    }

    // Handle '+' constraints: they add an implicit tied input
    for (size_t i = 0; i < stmt->output_operands.size(); i++) {
        if (!stmt->output_operands[i].constraint.empty() &&
            stmt->output_operands[i].constraint[0] == '+') {
            if (memory_output_tied[i]) {
                llvm::Value *addr = memory_output_addrs[i];
                if (!addr) {
                    return;
                }
                std::string tie_constraint = normalize_gcc_constraint_for_llvm(
                    stmt->output_operands[i].constraint);
                tie_constraint = add_llvm_indirect_memory_marker(
                    strip_output_constraint_prefix(tie_constraint));
                input_values.push_back(addr);
                input_types.push_back(addr->getType());
                input_element_types.push_back(memory_output_element_types[i]);
                constraints_str += "," + tie_constraint;
                continue;
            }
            if (output_model_index[i] < 0) {
                continue;
            }
            int modeled_idx = output_model_index[i];
            llvm::Value *loaded = builder.CreateLoad(
                output_types[modeled_idx], output_addrs[modeled_idx]);
            input_values.push_back(loaded);
            input_types.push_back(output_types[modeled_idx]);
            input_element_types.push_back(nullptr);
            constraints_str += "," + std::to_string(modeled_idx);
        }
    }

    // Resolve goto label BasicBlocks and add "!i" constraints BEFORE clobbers
    // (LLVM requires label constraints before clobber constraints in the constraint string)
    std::vector<llvm::BasicBlock*> indirect_dests;
    if (stmt->is_goto) {
        for (const auto &label : stmt->goto_labels) {
            std::string mangled = mangleCIdentifier(label);
            auto it = label_blocks.find(mangled);
            if (it == label_blocks.end()) {
                error("asm goto: undefined label '" + label + "'", stmt->location);
                return;
            }
            indirect_dests.push_back(it->second);
            if (!constraints_str.empty()) constraints_str += ",";
            constraints_str += "!i";
        }
    }

    // Process clobbers (must come after label constraints)
    for (auto &clob : stmt->clobbers) {
        if (clob == "memory") {
            has_memory_clobber = true;
        }
        if (!constraints_str.empty()) constraints_str += ",";
        constraints_str += "~{" + clob + "}";
    }
    if (needs_implicit_memory_clobber && !has_memory_clobber) {
        if (!constraints_str.empty()) constraints_str += ",";
        constraints_str += "~{memory}";
    }

    // Build return type
    llvm::Type *ret_type;
    if (output_types.empty()) {
        ret_type = llvm::Type::getVoidTy(*context);
    } else if (output_types.size() == 1) {
        ret_type = output_types[0];
    } else {
        ret_type = llvm::StructType::get(*context, output_types);
    }

    auto *func_ty = llvm::FunctionType::get(ret_type, input_types, false);
    bool has_side_effects = stmt->is_volatile
        || output_types.empty()
        || stmt->is_goto
        || needs_implicit_memory_clobber;

    auto *ia = llvm::InlineAsm::get(
        func_ty,
        asm_template,
        constraints_str,
        has_side_effects,
        false,  // alignStack
        llvm::InlineAsm::AD_ATT);

    llvm::Value *result;
    llvm::CallBase *asm_call_base = nullptr;
    if (stmt->is_goto) {
        // asm goto uses callbr instruction
        llvm::Function *function = builder.GetInsertBlock()->getParent();
        llvm::BasicBlock *fallthrough_bb = llvm::BasicBlock::Create(
            *context, "asm.fallthrough", function);

        auto *callbr = builder.CreateCallBr(
            func_ty, ia, fallthrough_bb, indirect_dests, input_values);
        result = callbr;
        asm_call_base = callbr;

        // Continue codegen in the fallthrough block
        builder.SetInsertPoint(fallthrough_bb);
    } else {
        auto *call = builder.CreateCall(func_ty, ia, input_values);
        result = call;
        asm_call_base = call;
    }

    // Opaque pointers need elementtype on indirect asm memory operands.
    for (size_t i = 0; i < input_element_types.size(); ++i) {
        if (!input_element_types[i]) {
            continue;
        }
        asm_call_base->addParamAttr(
            static_cast<unsigned>(i),
            llvm::Attribute::get(
                *context, llvm::Attribute::ElementType, input_element_types[i]));
    }

    // Store output values
    if (!output_types.empty()) {
        if (output_types.size() == 1) {
            builder.CreateStore(result, output_addrs[0]);
        } else {
            for (size_t i = 0; i < output_types.size(); i++) {
                llvm::Value *extracted = builder.CreateExtractValue(result, i);
                builder.CreateStore(extracted, output_addrs[i]);
            }
        }
    }
}
