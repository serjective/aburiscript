#include "backend.h"

#include <cstdio>
#include <cstdlib>
#include <string_view>

#include "../air/legalize.h"
#include "../air/passes.h"
#include "or1k/asm_emit.h"
#include "or1k/frame.h"
#include "or1k/insts.h"
#include "or1k/isel.h"
#include "or1k/target.h"

#include "aarch64/asm_emit.h"
#include "aarch64/elf_emit.h"
#include "aarch64/frame.h"
#include "aarch64/insts.h"
#include "aarch64/isel.h"
#include "aarch64/macho_emit.h"
#include "aarch64/target.h"
#include "common/emitter.h"
#include "common/mir_verifier.h"
#include "common/regalloc.h"
#include "x86/asm_emit.h"
#include "x86/frame.h"
#include "x86/insts.h"
#include "x86/isel.h"
#include "x86/elf_emit.h"
#include "x86/macho_emit.h"
#include "x86/target.h"

namespace aburi::backend {

namespace {

struct TargetPipeline {
    uint16_t store_gpr, load_gpr;
    uint16_t store_fpr, load_fpr;
    uint16_t store_fpr128, load_fpr128;

    bool (*select_function)(const air::Module&, const air::Function&,
                            uint32_t, MFunction&, std::vector<Diagnostic>&,
                            int);
    const TargetRegInfo& (*reg_info)();
    OpcodeInfoFn opcode_info;
    void (*lower_frame)(MFunction&);
    const MirTargetInfo& (*mir_info)();
    bool force_fast_regalloc = false;
    const air::LegalizeConfig* legalize = nullptr;
};

const TargetPipeline& aarch64_pipeline() {
    static const TargetPipeline pipeline = {
        static_cast<uint16_t>(aarch64::A64Op::StrX),
        static_cast<uint16_t>(aarch64::A64Op::LdrX),
        static_cast<uint16_t>(aarch64::A64Op::StrD),
        static_cast<uint16_t>(aarch64::A64Op::LdrD),
        static_cast<uint16_t>(aarch64::A64Op::StrQ),
        static_cast<uint16_t>(aarch64::A64Op::LdrQ),
        aarch64::select_function,
        aarch64::reg_info,
        aarch64::a64_regalloc_info,
        aarch64::lower_frame,
        aarch64::a64_mir_target,
    };
    return pipeline;
}

const TargetPipeline& x86_64_pipeline() {
    static const TargetPipeline pipeline = {
        static_cast<uint16_t>(x86::X86Op::Store64),
        static_cast<uint16_t>(x86::X86Op::Load64),
        static_cast<uint16_t>(x86::X86Op::StoreSD),
        static_cast<uint16_t>(x86::X86Op::LoadSD),
        static_cast<uint16_t>(x86::X86Op::StoreX128),
        static_cast<uint16_t>(x86::X86Op::LoadX128),
        x86::select_function,
        x86::reg_info,
        x86::x86_regalloc_info,
        x86::lower_frame,
        x86::x86_mir_target,
    };
    return pipeline;
}

const TargetPipeline& x86_32_pipeline() {
    static const TargetPipeline pipeline = {
        static_cast<uint16_t>(x86::X86Op::Store32),
        static_cast<uint16_t>(x86::X86Op::Load32),
        static_cast<uint16_t>(x86::X86Op::StoreSD),
        static_cast<uint16_t>(x86::X86Op::LoadSD),
        static_cast<uint16_t>(x86::X86Op::StoreX128),
        static_cast<uint16_t>(x86::X86Op::LoadX128),
        x86::select_function,
        x86::reg_info_32,
        x86::x86_regalloc_info,
        x86::lower_frame,
        x86::x86_mir_target,
        /*force_fast_regalloc=*/true,
    };
    return pipeline;
}

const TargetPipeline& x86_pipeline_for(const TargetInfo& target) {
    return target.arch == TargetArch::X86 ? x86_32_pipeline()
                                          : x86_64_pipeline();
}

const air::LegalizeConfig& or1k_legalize_config() {
    static const air::LegalizeConfig config = [] {
        air::LegalizeConfig c;
        c.word_bytes = 4;
        c.endianness = EndiannessKind::Big;
        c.split_i64 = true;
        c.soft_float = true;
        return c;
    }();
    return config;
}

const TargetPipeline& or1k_pipeline() {
    static const TargetPipeline pipeline = {

        static_cast<uint16_t>(or1k::Or1kOp::Sw),
        static_cast<uint16_t>(or1k::Or1kOp::Lwz),
        static_cast<uint16_t>(or1k::Or1kOp::Sw),
        static_cast<uint16_t>(or1k::Or1kOp::Lwz),
        static_cast<uint16_t>(or1k::Or1kOp::Sw),
        static_cast<uint16_t>(or1k::Or1kOp::Lwz),
        or1k::select_function,
        or1k::reg_info,
        or1k::or1k_regalloc_info,
        or1k::lower_frame,
        or1k::or1k_mir_target,
        /*force_fast_regalloc=*/true,
        &or1k_legalize_config(),
    };
    return pipeline;
}

void dump_prera_mir(const MFunction& mfunc, const TargetPipeline& target) {
    std::fprintf(stderr, "%s:\n", mfunc.name.c_str());
    for (size_t bi = 0; bi < mfunc.blocks.size(); ++bi) {
        std::fprintf(stderr, "b%zu:\n", bi);
        for (const MInst& mi : mfunc.blocks[bi].insts) {
            std::string_view mnemonic = target.mir_info().mnemonic(mi.opcode);
            std::fprintf(stderr, "  %-12.*s aux=%llu [",
                         static_cast<int>(mnemonic.size()), mnemonic.data(),
                         static_cast<unsigned long long>(mi.aux));
            for (const MOperand& operand : mi.operands) {
                switch (operand.kind) {
                    case MOperandKind::Reg:
                        std::fprintf(stderr, " %s%u",
                                     operand.reg.is_virtual() ? "v" : "p",
                                     operand.reg.index());
                        break;
                    case MOperandKind::Imm:
                        std::fprintf(stderr, " #%lld",
                                     static_cast<long long>(operand.imm));
                        break;
                    case MOperandKind::FrameIndex:
                        std::fprintf(stderr, " fi%u", operand.frame_index);
                        break;
                    case MOperandKind::Symbol:
                        std::fprintf(stderr, " @%s", operand.symbol.c_str());
                        break;
                    case MOperandKind::Label:
                        std::fprintf(stderr, " b%u", operand.label);
                        break;
                }
            }
            std::fprintf(stderr, " ]\n");
        }
    }
}

void diagnose(EmitResult& result, const std::string& message) {
    Diagnostic diag;
    diag.level = DiagnosticLevel::Error;
    diag.message = "air backend: " + message;
    result.diagnostics.push_back(std::move(diag));
}

EmitResult run_pipeline(air::Module& module, ModuleEmitter& emitter,
                        const BackendOptions& options,
                        const TargetPipeline& target) {
    EmitResult result;

    if (target.legalize != nullptr) {
        air::LegalizeResult legalized =
            air::run_legalize(module, *target.legalize);
        if (!legalized.ok) {
            diagnose(result, legalized.error);
            return result;
        }
        if (legalized.changed && options.opt_level >= 1) {

            for (uint32_t index = 1; index <= module.function_count();
                 ++index) {
                air::Function& function = module.function(air::FuncId{index});
                if (!function.is_declaration()) {
                    air::run_instsimplify(function, module);
                    air::run_dce(function, module);
                }
            }
        }
    }

    set_fast_regalloc_spill_opcodes(target.store_gpr, target.load_gpr,
                                    target.store_fpr, target.load_fpr,
                                    target.store_fpr128, target.load_fpr128);

    emitter.begin_module(module);
    for (const std::string& text : module.module_asm()) {
        emitter.emit_module_asm(text);
    }

    const bool use_linear_scan =
        options.opt_level >= 1 && !target.force_fast_regalloc;
    const int isel_opt_level = use_linear_scan ? options.opt_level : 0;

    const bool verify_mir =
        options.verify_mir || std::getenv("ABURI_VERIFY_MIR") != nullptr;
    auto verify_stage = [&](const MFunction& mfunc, MirStage stage) {
        if (!verify_mir) {
            return true;
        }
        MirVerifyResult verified =
            verify_mfunction(mfunc, target.reg_info(), target.mir_info(),
                             stage, isel_opt_level);
        if (verified.ok()) {
            return true;
        }
        diagnose(result, "mir verifier rejected the function:\n" +
                             verified.to_string());
        return false;
    };
    FastRegAllocator fast_allocator;
    LinearScanAllocator linear_allocator;
    RegAllocator& allocator =
        use_linear_scan
            ? static_cast<RegAllocator&>(linear_allocator)
            : static_cast<RegAllocator&>(fast_allocator);
    for (uint32_t index = 1; index <= module.function_count(); ++index) {
        const air::Function& function = module.function(air::FuncId{index});
        if (function.is_declaration()) {
            continue;
        }
        MFunction mfunc;
        if (!target.select_function(module, function, index, mfunc,
                                    result.diagnostics, isel_opt_level)) {
            continue;
        }

        if (std::getenv("ABURI_AIR_DEBUG_PRERA")) {
            dump_prera_mir(mfunc, target);
        }
        if (!verify_stage(mfunc, MirStage::PostIsel)) {
            continue;
        }
        allocator.run(mfunc, target.reg_info(), target.opcode_info);
        if (!verify_stage(mfunc, MirStage::PostRegAlloc)) {
            continue;
        }
        target.lower_frame(mfunc);
        if (!verify_stage(mfunc, MirStage::PostFrame)) {
            continue;
        }

        emitter.begin_function(mfunc);
        for (uint32_t block = 0; block < mfunc.blocks.size(); ++block) {
            emitter.emit_block_label(mfunc, block);
            for (const MInst& inst : mfunc.blocks[block].insts) {
                emitter.emit_inst(mfunc, inst);
            }
        }
        emitter.end_function(mfunc);
    }

    for (uint32_t index = 1; index <= module.global_count(); ++index) {
        emitter.emit_global(module, module.global(air::GlobalId{index}));
    }
    emitter.emit_ctor_list(module);
    emitter.end_module(module);
    return result;
}

bool check_target(const TargetInfo& target, EmitResult& result) {
    bool arch_ok = target.arch == TargetArch::AARCH64 ||
                   target.arch == TargetArch::X86_64 ||
                   target.arch == TargetArch::X86 ||
                   target.arch == TargetArch::OR1K;
    // 32-bit x86 targets Linux (no 32-bit Mach-O: modern Darwin cannot link
    // or run it) or bare metal (16-bit real mode for DOS/kernel boot code).
    bool os_ok = target.os == TargetOS::MACOS || target.os == TargetOS::LINUX ||
                 (target.arch == TargetArch::X86 &&
                  target.os == TargetOS::NONE);
    if (target.arch == TargetArch::X86 && target.os != TargetOS::LINUX &&
        target.os != TargetOS::NONE) {
        diagnose(result, "32-bit x86 is only supported on Linux or bare metal");
        return false;
    }
    if (!arch_ok || !os_ok) {
        diagnose(result,
                 "only the AArch64, x86-64, and 32-bit x86 Linux targets are "
                 "supported by the native backend today");
        return false;
    }
    return true;
}

} // namespace

EmitResult emit_assembly(air::Module& module, const TargetInfo& target,
                         std::ostream& out, BackendOptions options) {
    EmitResult result;
    if (!check_target(target, result)) {
        return result;
    }
    std::vector<Diagnostic> emit_diags;
    if (target.arch == TargetArch::OR1K) {
        or1k::AsmTextEmitter emitter(out, options.emit_unwind_tables,
                                     &emit_diags);
        result = run_pipeline(module, emitter, options, or1k_pipeline());
        result.diagnostics.insert(result.diagnostics.end(), emit_diags.begin(),
                                  emit_diags.end());
        return result;
    }
    if (target.arch == TargetArch::X86_64 || target.arch == TargetArch::X86) {
        x86::AsmTextEmitter emitter(out, options.emit_unwind_tables,
                                    object_format_for(target), &emit_diags,
                                    x86::is_legacy32(target),
                                    target.real_mode_16);
        result = run_pipeline(module, emitter, options,
                              x86_pipeline_for(target));
        result.diagnostics.insert(result.diagnostics.end(), emit_diags.begin(),
                                  emit_diags.end());
        return result;
    }
    aarch64::AsmTextEmitter emitter(out, options.emit_unwind_tables,
                                    object_format_for(target), &emit_diags);
    result = run_pipeline(module, emitter, options, aarch64_pipeline());
    result.diagnostics.insert(result.diagnostics.end(), emit_diags.begin(),
                              emit_diags.end());
    return result;
}

EmitResult emit_object(air::Module& module, const TargetInfo& target,
                       std::ostream& out, BackendOptions options) {
    EmitResult result;
    if (!check_target(target, result)) {
        return result;
    }
    if (target.arch == TargetArch::OR1K) {

        diagnose(result,
                 "or1k native object emission is not yet implemented; use "
                 "--air-object=as once instruction selection lands");
        return result;
    }
    std::vector<Diagnostic> emit_diags;
    if (target.arch == TargetArch::X86) {

        diagnose(result,
                 "the direct object writer does not cover 32-bit x86; use "
                 "--air-object=as");
        return result;
    }
    if (target.arch == TargetArch::X86_64) {
        if (target.os == TargetOS::LINUX) {
            x86::ElfEmitter emitter(emit_diags, options.emit_unwind_tables);
            result = run_pipeline(module, emitter, options, x86_64_pipeline());
            result.diagnostics.insert(result.diagnostics.end(),
                                      emit_diags.begin(), emit_diags.end());
            if (result.ok()) {
                emitter.write(out);
            }
            return result;
        }
        x86::MachOEmitter emitter(emit_diags, options.emit_unwind_tables);
        result = run_pipeline(module, emitter, options, x86_64_pipeline());
        result.diagnostics.insert(result.diagnostics.end(), emit_diags.begin(),
                                  emit_diags.end());
        if (result.ok()) {
            emitter.write(out);
        }
        return result;
    }
    if (target.os == TargetOS::LINUX) {
        aarch64::ElfEmitter emitter(emit_diags, options.emit_unwind_tables);
        result = run_pipeline(module, emitter, options, aarch64_pipeline());
        result.diagnostics.insert(result.diagnostics.end(), emit_diags.begin(),
                                  emit_diags.end());
        if (result.ok()) {
            emitter.write(out);
        }
        return result;
    }
    aarch64::MachOEmitter emitter(emit_diags, options.emit_unwind_tables);
    result = run_pipeline(module, emitter, options, aarch64_pipeline());
    result.diagnostics.insert(result.diagnostics.end(), emit_diags.begin(),
                              emit_diags.end());
    if (result.ok()) {
        emitter.write(out);
    }
    return result;
}

} // namespace aburi::backend
