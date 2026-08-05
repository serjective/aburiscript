#include "mir_verifier.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <utility>

namespace aburi::backend {

std::string_view mir_stage_name(MirStage stage) {
    switch (stage) {
        case MirStage::PostIsel:
            return "post-isel";
        case MirStage::PostRegAlloc:
            return "post-regalloc";
        case MirStage::PostFrame:
            return "post-frame";
    }
    return "unknown";
}

std::string MirVerifyResult::to_string() const {
    std::string text;
    for (const MirVerifierDiag& diag : diags) {
        if (!text.empty()) {
            text += '\n';
        }
        text += diag.severity == MirVerifierDiag::Severity::Error ? "error: "
                                                                  : "note: ";
        text += diag.message;
    }
    return text;
}

namespace {

RegClass scratch_class(RegClass cls) {
    return cls == RegClass::Gpr ? RegClass::Gpr : RegClass::Fpr;
}

uint8_t kind_bit(MOperandKind kind) {
    switch (kind) {
        case MOperandKind::Reg:
            return MK_Reg;
        case MOperandKind::Imm:
            return MK_Imm;
        case MOperandKind::FrameIndex:
            return MK_Frame;
        case MOperandKind::Symbol:
            return MK_Symbol;
        case MOperandKind::Label:
            return MK_Label;
    }
    return 0;
}

const char* kind_name(MOperandKind kind) {
    switch (kind) {
        case MOperandKind::Reg:
            return "a register";
        case MOperandKind::Imm:
            return "an immediate";
        case MOperandKind::FrameIndex:
            return "a frame index";
        case MOperandKind::Symbol:
            return "a symbol";
        case MOperandKind::Label:
            return "a label";
    }
    return "?";
}

std::string kind_mask_name(uint8_t mask) {
    static const std::pair<uint8_t, const char*> kNames[] = {
        {MK_Reg, "a register"},   {MK_Imm, "an immediate"},
        {MK_Frame, "a frame index"}, {MK_Symbol, "a symbol"},
        {MK_Label, "a label"},
    };
    std::string text;
    for (const auto& [bit, name] : kNames) {
        if ((mask & bit) == 0) {
            continue;
        }
        if (!text.empty()) {
            text += " or ";
        }
        text += name;
    }
    return text.empty() ? "nothing" : text;
}

const char* reg_class_name(RegClass cls) {
    switch (cls) {
        case RegClass::Gpr:
            return "general";
        case RegClass::Fpr:
            return "floating-point";
        case RegClass::Fpr128:
            return "128-bit floating-point";
    }
    return "?";
}

class MirVerifier {
public:
    MirVerifier(const MFunction& func, const TargetRegInfo& regs,
                const MirTargetInfo& target, MirStage stage, int opt_level,
                MirVerifyResult& result)
        : func_(func),
          regs_(regs),
          target_(target),
          stage_(stage),
          opt_level_(opt_level),
          result_(result) {}

    void run();

private:
    void error(const std::string& message) {
        MirVerifierDiag diag;
        diag.severity = MirVerifierDiag::Severity::Error;
        diag.message = prefix() + message;
        result_.diags.push_back(std::move(diag));
    }
    void error_at(size_t block, size_t index, const std::string& message) {
        error(inst_label(block, index) + ": " + message);
    }

    std::string prefix() const {
        return "func @" + func_.name + " (" +
               std::string(mir_stage_name(stage_)) + "): ";
    }
    static std::string block_label(size_t block) {
        return "b" + std::to_string(block);
    }
    std::string inst_label(size_t block, size_t index) const {
        std::string text = block_label(block) + " i" + std::to_string(index);
        const MInst& inst = func_.blocks[block].insts[index];
        if (target_.mnemonic != nullptr) {
            std::string_view mnemonic = target_.mnemonic(inst.opcode);
            text += " ";
            text.append(mnemonic.data(), mnemonic.size());
        }
        return text;
    }

    MirOpcodeFacts facts_of(const MInst& inst) const {
        return target_.facts != nullptr ? target_.facts(inst.opcode)
                                        : MirOpcodeFacts{};
    }
    bool valid_vreg(uint32_t vreg) const {
        return vreg < func_.vreg_classes.size();
    }
    bool operand_class(const MOperand& operand, RegClass& cls) const {
        if (operand.reg.is_virtual()) {
            if (!valid_vreg(operand.reg.index())) {
                return false;
            }
            cls = func_.vreg_classes[operand.reg.index()];
            return true;
        }
        if (regs_.reg_class == nullptr ||
            (target_.phys_reg_count != 0 &&
             operand.reg.index() >= target_.phys_reg_count)) {
            return false;
        }
        cls = regs_.reg_class(operand.reg.index());
        return true;
    }
    bool linear_scan_model() const { return opt_level_ >= 1; }
    void check_block_structure();
    void check_operands();
    void check_shape(size_t block, size_t index, const MInst& inst);
    void check_post_isel();
    void check_post_regalloc();
    void check_post_frame();
    void check_eh_metadata();

    void collect_pool_registers(std::unordered_set<uint32_t>& pool) const;

    const MFunction& func_;
    const TargetRegInfo& regs_;
    const MirTargetInfo& target_;
    MirStage stage_;
    int opt_level_;
    MirVerifyResult& result_;
};

void MirVerifier::run() {
    if (func_.blocks.empty()) {
        error("function has no blocks");
        return;
    }
    check_block_structure();
    check_operands();
    switch (stage_) {
        case MirStage::PostIsel:
            check_post_isel();
            check_eh_metadata();
            break;
        case MirStage::PostRegAlloc:
            check_post_regalloc();
            break;
        case MirStage::PostFrame:
            check_post_frame();
            break;
    }
}

void MirVerifier::check_block_structure() {
    for (size_t b = 0; b < func_.blocks.size(); ++b) {
        const MBlock& block = func_.blocks[b];
        if (block.insts.empty()) {
            error(block_label(b) + " is empty");
            continue;
        }
        for (size_t i = 0; i + 1 < block.insts.size(); ++i) {
            MirOpcodeFacts facts = facts_of(block.insts[i]);
            if (facts.is_terminator && !facts.is_conditional_branch) {
                error_at(b, i,
                         "unconditional terminator in the middle of a block (" +
                             std::to_string(block.insts.size() - i - 1) +
                             " instructions follow it and cannot execute)");
            }
        }
        const MirOpcodeFacts last = facts_of(block.insts.back());
        if (!last.is_terminator) {
            error_at(b, block.insts.size() - 1,
                     "block does not end in a terminator");
        } else if (last.is_conditional_branch) {
            error_at(b, block.insts.size() - 1,
                     "block ends in a conditional branch, so it falls through "
                     "to whichever block happens to be laid out next");
        }
        for (uint32_t succ : block.succs) {
            if (succ >= func_.blocks.size()) {
                error(block_label(b) + ": successor b" + std::to_string(succ) +
                      " is out of range (" +
                      std::to_string(func_.blocks.size()) + " blocks)");
            }
        }
    }
}

void MirVerifier::check_operands() {
    for (size_t b = 0; b < func_.blocks.size(); ++b) {
        const MBlock& block = func_.blocks[b];
        for (size_t i = 0; i < block.insts.size(); ++i) {
            const MInst& inst = block.insts[i];
            MirOpcodeFacts facts = facts_of(inst);
            check_shape(b, i, inst);
            if (facts.is_asm_block && inst.aux >= func_.asm_texts.size()) {
                error_at(b, i,
                         "asm text index " + std::to_string(inst.aux) +
                             " is out of range (" +
                             std::to_string(func_.asm_texts.size()) +
                             " entries)");
            }
            for (size_t o = 0; o < inst.operands.size(); ++o) {
                const MOperand& operand = inst.operands[o];
                const std::string where = "operand " + std::to_string(o) + " ";
                switch (operand.kind) {
                    case MOperandKind::Reg:
                        if (operand.reg.is_virtual()) {
                            if (!valid_vreg(operand.reg.index())) {
                                error_at(b, i,
                                         where + "names v" +
                                             std::to_string(
                                                 operand.reg.index()) +
                                             " but the function has " +
                                             std::to_string(
                                                 func_.vreg_classes.size()) +
                                             " virtual registers");
                            }
                        } else if (target_.phys_reg_count != 0 &&
                                   operand.reg.index() >=
                                       target_.phys_reg_count) {
                            error_at(b, i,
                                     where + "names physical register " +
                                         std::to_string(operand.reg.index()) +
                                         " but the register file holds " +
                                         std::to_string(
                                             target_.phys_reg_count));
                        }
                        break;
                    case MOperandKind::FrameIndex:
                        if (operand.frame_index >=
                            func_.frame_objects.size()) {
                            error_at(b, i,
                                     where + "names frame object " +
                                         std::to_string(operand.frame_index) +
                                         " but the function has " +
                                         std::to_string(
                                             func_.frame_objects.size()));
                        }
                        break;
                    case MOperandKind::Label:
                        if (operand.label >= func_.blocks.size()) {
                            error_at(b, i,
                                     where + "targets b" +
                                         std::to_string(operand.label) +
                                         " but the function has " +
                                         std::to_string(func_.blocks.size()) +
                                         " blocks");
                        }
                        break;
                    case MOperandKind::Imm:
                    case MOperandKind::Symbol:
                        break;
                }
            }
        }
    }
}

void MirVerifier::check_shape(size_t block, size_t index, const MInst& inst) {
    if (target_.shape == nullptr) {
        return;
    }
    const MirShape shape = target_.shape(inst.opcode);
    const size_t count = inst.operands.size();
    if (count < shape.min_operands) {
        error_at(block, index,
                 "expects at least " + std::to_string(shape.min_operands) +
                     " operands but carries " + std::to_string(count));
        return;
    }
    if (shape.max_operands != kMirUnbounded && count > shape.max_operands) {
        error_at(block, index,
                 "expects at most " + std::to_string(shape.max_operands) +
                     " operands but carries " + std::to_string(count));
    }
    const size_t positions =
        std::min<size_t>(count, kMirShapePositions);
    for (size_t o = 0; o < positions; ++o) {
        const MOperand& operand = inst.operands[o];
        const uint8_t allowed = shape.kinds[o];
        if (allowed != 0 && (allowed & kind_bit(operand.kind)) == 0) {
            error_at(block, index,
                     "operand " + std::to_string(o) + " is " +
                         kind_name(operand.kind) + " but the format wants " +
                         kind_mask_name(allowed));
            continue;
        }
        if ((shape.class_checked & (1u << o)) == 0 ||
            operand.kind != MOperandKind::Reg) {
            continue;
        }
        RegClass actual = RegClass::Gpr;
        if (!operand_class(operand, actual)) {
            continue;
        }

        const bool same_file =
            (actual == RegClass::Gpr) == (shape.classes[o] == RegClass::Gpr);
        if (!same_file) {
            error_at(block, index,
                     "operand " + std::to_string(o) + " is a " +
                         reg_class_name(actual) +
                         " register but the format wants a " +
                         reg_class_name(shape.classes[o]) + " one");
        }
    }
}

void MirVerifier::collect_pool_registers(
    std::unordered_set<uint32_t>& pool) const {
    for (const std::vector<uint32_t>* list :
         {&regs_.linear_gpr_caller, &regs_.linear_gpr_callee,
          &regs_.linear_fpr_caller, &regs_.linear_fpr_callee}) {
        pool.insert(list->begin(), list->end());
    }
}

void MirVerifier::check_post_isel() {

    std::unordered_set<uint32_t> defined;
    for (const MBlock& block : func_.blocks) {
        for (const MInst& inst : block.insts) {
            if (!facts_of(inst).defines_operand0 || inst.operands.empty()) {
                continue;
            }
            const MOperand& def = inst.operands[0];
            if (def.kind == MOperandKind::Reg && def.reg.is_virtual()) {
                defined.insert(def.reg.index());
            }
        }
    }

    std::unordered_set<uint32_t> pool;
    if (linear_scan_model()) {
        collect_pool_registers(pool);
    }
    const size_t gpr_scratch = regs_.linear_gpr_scratch.size();
    const size_t fpr_scratch = regs_.linear_fpr_scratch.size();

    for (size_t b = 0; b < func_.blocks.size(); ++b) {
        const MBlock& block = func_.blocks[b];

        std::unordered_set<uint32_t> block_defined;
        std::unordered_set<uint32_t> block_labels;

        for (size_t i = 0; i < block.insts.size(); ++i) {
            const MInst& inst = block.insts[i];
            MirOpcodeFacts facts = facts_of(inst);
            std::unordered_set<uint32_t> inst_gprs;
            std::unordered_set<uint32_t> inst_fprs;

            for (size_t o = 0; o < inst.operands.size(); ++o) {
                const MOperand& operand = inst.operands[o];
                if (operand.kind == MOperandKind::Label) {
                    block_labels.insert(operand.label);
                    continue;
                }
                if (operand.kind != MOperandKind::Reg) {
                    continue;
                }
                const bool is_def = o == 0 && facts.defines_operand0;
                const bool is_use = !is_def || facts.reads_operand0;

                if (!operand.reg.is_virtual()) {

                    if (linear_scan_model() &&
                        pool.count(operand.reg.index()) != 0) {
                        error_at(b, i,
                                 "explicit physical register " +
                                     std::to_string(operand.reg.index()) +
                                     " is in a linear-scan allocation pool; "
                                     "the allocator cannot see this use and "
                                     "may hand the register out");
                    }
                    continue;
                }
                const uint32_t vreg = operand.reg.index();
                if (!valid_vreg(vreg)) {
                    continue;
                }
                if (scratch_class(func_.vreg_classes[vreg]) == RegClass::Gpr) {
                    inst_gprs.insert(vreg);
                } else {
                    inst_fprs.insert(vreg);
                }
                if (is_use) {
                    if (defined.count(vreg) == 0) {
                        error_at(b, i,
                                 "v" + std::to_string(vreg) +
                                     " is used but never defined");
                    } else if (!linear_scan_model() &&
                               block_defined.count(vreg) == 0) {
                        error_at(b, i,
                                 "v" + std::to_string(vreg) +
                                     " is used before its definition in " +
                                     block_label(b) +
                                     "; the fast tier keeps no value live "
                                     "across a block boundary");
                    }
                }
                if (is_def) {
                    block_defined.insert(vreg);
                }
            }

            if (linear_scan_model()) {
                if (gpr_scratch != 0 && inst_gprs.size() > gpr_scratch) {
                    error_at(b, i,
                             "carries " + std::to_string(inst_gprs.size()) +
                                 " distinct virtual gpr operands but only " +
                                 std::to_string(gpr_scratch) +
                                 " scratch registers are reserved");
                }
                if (fpr_scratch != 0 && inst_fprs.size() > fpr_scratch) {
                    error_at(b, i,
                             "carries " + std::to_string(inst_fprs.size()) +
                                 " distinct virtual fpr operands but only " +
                                 std::to_string(fpr_scratch) +
                                 " scratch registers are reserved");
                }
            }
        }

        if (linear_scan_model()) {
            for (uint32_t label : block_labels) {
                if (std::find(block.succs.begin(), block.succs.end(), label) ==
                    block.succs.end()) {
                    error(block_label(b) + ": branches to " +
                          block_label(label) +
                          " but that block is not in its successor list");
                }
            }
        }
    }
}

void MirVerifier::check_eh_metadata() {
    if (func_.eh_call_sites.empty() && func_.eh_actions.empty() &&
        func_.eh_typeinfos.empty()) {
        return;
    }

    std::unordered_map<uint32_t, size_t> label_position;
    size_t position = 0;
    for (const MBlock& block : func_.blocks) {
        for (const MInst& inst : block.insts) {
            ++position;
            if (!facts_of(inst).is_eh_label) {
                continue;
            }
            if (!label_position.emplace(inst.aux, position).second) {
                error("eh label " + std::to_string(inst.aux) +
                      " is planted more than once in the block stream");
            }
        }
    }

    std::unordered_map<uint32_t, const MEhAction*> actions;
    for (const MEhAction& action : func_.eh_actions) {
        actions[action.label] = &action;
    }
    std::unordered_set<uint32_t> filters;
    for (const MEhTypeInfo& info : func_.eh_typeinfos) {
        filters.insert(info.filter);
    }

    size_t previous_end = 0;
    for (size_t i = 0; i < func_.eh_call_sites.size(); ++i) {
        const MEhCallSite& site = func_.eh_call_sites[i];
        const std::string where = "eh call site " + std::to_string(i) + ": ";

        auto begin = label_position.find(site.begin_label);
        auto end = label_position.find(site.end_label);
        if (begin == label_position.end()) {
            error(where + "begin label " + std::to_string(site.begin_label) +
                  " is never planted in the block stream");
        }
        if (end == label_position.end()) {
            error(where + "end label " + std::to_string(site.end_label) +
                  " is never planted in the block stream");
        }
        if (begin != label_position.end() && end != label_position.end()) {
            if (begin->second > end->second) {
                error(where + "begin label follows its end label");
            }

            if (begin->second < previous_end) {
                error(where +
                      "starts before the previous site ends; the call-site "
                      "table encodes distances as unsigned deltas");
            }
            previous_end = end->second;
        }

        if (site.landing_pad_block >= func_.blocks.size()) {
            error(where + "landing pad b" +
                  std::to_string(site.landing_pad_block) +
                  " is out of range");
        } else if (site.landing_pad_block == 0) {

            error(where +
                  "names the entry block as its landing pad, which the "
                  "exception table cannot distinguish from having none");
        }

        if (site.action_label != 0 &&
            actions.find(site.action_label) == actions.end()) {
            error(where + "action label " + std::to_string(site.action_label) +
                  " matches no action row");
        }
    }

    for (const MEhAction& action : func_.eh_actions) {
        if (action.filter != 0 &&
            filters.find(static_cast<uint32_t>(action.filter)) ==
                filters.end()) {
            error("eh action " + std::to_string(action.label) + " selects type "
                  "filter " + std::to_string(action.filter) +
                  ", which matches no typeinfo row");
        }
        std::unordered_set<uint32_t> seen{action.label};
        uint32_t next = action.next_label;
        while (next != 0) {
            auto found = actions.find(next);
            if (found == actions.end()) {
                error("eh action chain from " + std::to_string(action.label) +
                      " reaches label " + std::to_string(next) +
                      ", which matches no action row");
                break;
            }
            if (!seen.insert(next).second) {
                error("eh action chain from " + std::to_string(action.label) +
                      " revisits label " + std::to_string(next));
                break;
            }
            next = found->second->next_label;
        }
    }
}

void MirVerifier::check_post_regalloc() {
    for (size_t b = 0; b < func_.blocks.size(); ++b) {
        const MBlock& block = func_.blocks[b];
        for (size_t i = 0; i < block.insts.size(); ++i) {
            for (size_t o = 0; o < block.insts[i].operands.size(); ++o) {
                const MOperand& operand = block.insts[i].operands[o];
                if (operand.kind == MOperandKind::Reg &&
                    operand.reg.is_virtual()) {
                    error_at(b, i,
                             "operand " + std::to_string(o) + " is still v" +
                                 std::to_string(operand.reg.index()) +
                                 " after register allocation");
                }
            }
        }
    }
    for (uint32_t csr : func_.used_csrs) {
        if (target_.phys_reg_count != 0 && csr >= target_.phys_reg_count) {
            error("used callee-saved register " + std::to_string(csr) +
                  " is out of range");
            continue;
        }
        if (regs_.is_callee_saved != nullptr && !regs_.is_callee_saved(csr)) {
            error("register " + std::to_string(csr) +
                  " is listed in used_csrs but is not callee-saved");
        }
    }
}

void MirVerifier::check_post_frame() {
    for (size_t b = 0; b < func_.blocks.size(); ++b) {
        const MBlock& block = func_.blocks[b];
        for (size_t i = 0; i < block.insts.size(); ++i) {
            const MInst& inst = block.insts[i];
            if (facts_of(inst).is_frame_pseudo) {
                error_at(b, i,
                         "frame pseudo-instruction survived frame lowering");
            }
            for (size_t o = 0; o < inst.operands.size(); ++o) {
                if (inst.operands[o].kind == MOperandKind::FrameIndex) {
                    error_at(b, i,
                             "operand " + std::to_string(o) +
                                 " is still a frame index after frame "
                                 "lowering");
                }
            }
        }
    }

    for (uint32_t csr : func_.used_csrs) {
        bool described = false;
        for (const auto& [reg, offset] : func_.csr_cfa_offsets) {
            if (reg == csr) {
                described = true;
                break;
            }
        }
        if (!described) {
            error("callee-saved register " + std::to_string(csr) +
                  " has no recorded CFA offset");
        }
    }
}

} // namespace

void verify_mfunction_into(const MFunction& func, const TargetRegInfo& regs,
                           const MirTargetInfo& target, MirStage stage,
                           int opt_level, MirVerifyResult& result) {
    MirVerifier verifier(func, regs, target, stage, opt_level, result);
    verifier.run();
}

MirVerifyResult verify_mfunction(const MFunction& func,
                                 const TargetRegInfo& regs,
                                 const MirTargetInfo& target, MirStage stage,
                                 int opt_level) {
    MirVerifyResult result;
    verify_mfunction_into(func, regs, target, stage, opt_level, result);
    return result;
}

} // namespace aburi::backend
