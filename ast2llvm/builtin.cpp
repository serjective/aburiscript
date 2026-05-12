#include "ast2llvm.h"
#include "const_lowering.h"
#include "../helpers/casting.h"
#include "../constexpr/consteval_compat.h"
#include "../numeric_utils.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <algorithm>
#include <cstdlib>
#include <functional>
#include <unordered_set>
namespace {
    std::optional<int64_t> eval_constexpr_i64(
    Expr* expr, ConstEvalMode mode = ConstEvalMode::c_ice()) {
        return try_evaluate_with_consteval_compat(expr, mode);
    }

    llvm::Value* lower_builtin_const_integer(
        ASTToLLVM& lower,
        BuiltinCallExpr* expr,
        int64_t value) {
        auto& ctx = *lower.context;
        llvm::Type* result_type = lower.convert_type(expr->result_type);
        if (auto* int_type = llvm::dyn_cast<llvm::IntegerType>(result_type)) {
            return llvm::ConstantInt::get(int_type, value, true);
        }
        return llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), value, true);
    }

}
// Helper: get or declare an external libc function
static llvm::FunctionCallee get_or_declare_libc_func(
    llvm::Module* module, llvm::LLVMContext& ctx,
    const std::string& name, llvm::FunctionType* ft) {
    if (auto* existing = module->getFunction(name)) {
        return existing;
    }
    return module->getOrInsertFunction(name, ft);
}

// Helper: map memory order integer to LLVM AtomicOrdering
static llvm::AtomicOrdering map_memory_order(int order) {
    switch (order) {
        case 0: return llvm::AtomicOrdering::Monotonic;       // __ATOMIC_RELAXED
        case 1: return llvm::AtomicOrdering::Monotonic;       // __ATOMIC_CONSUME (treat as relaxed per C++ standard recommendation)
        case 2: return llvm::AtomicOrdering::Acquire;         // __ATOMIC_ACQUIRE
        case 3: return llvm::AtomicOrdering::Release;         // __ATOMIC_RELEASE
        case 4: return llvm::AtomicOrdering::AcquireRelease;  // __ATOMIC_ACQ_REL
        case 5: return llvm::AtomicOrdering::SequentiallyConsistent; // __ATOMIC_SEQ_CST
        default: return llvm::AtomicOrdering::SequentiallyConsistent;
    }
}

static bool is_valid_atomic_store_order(int order) {
    switch (order) {
        case 0: // __ATOMIC_RELAXED
        case 3: // __ATOMIC_RELEASE
        case 5: // __ATOMIC_SEQ_CST
            return true;
        default:
            return false;
    }
}

struct BuiltinLoweringResult {
    bool handled = false;
    llvm::Value* value = nullptr;
};

// Grouped lowerers keep convert_builtin_call_expr readable while preserving a
// single external builtin entrypoint.
static BuiltinLoweringResult lower_builtin_memory_and_stack_group(
    ASTToLLVM& lower, BuiltinCallExpr* expr) {
    auto& builder = lower.builder;
    auto& module = lower.module;
    auto& ctx = *lower.context;
    auto convert_expression = [&](Expr* expression) {
        return lower.convert_expression(expression);
    };
    auto cast_llvm_type =
        [&](llvm::Value* value, llvm::Type* dest_type, bool is_unsigned) {
        return lower.cast_llvm_type(value, dest_type, is_unsigned);
    };

    switch (expr->kind) {
    case BuiltinKind::MEMCPY: {
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        builder.CreateMemCpy(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
        return {true, dst};
    }
    case BuiltinKind::MEMMOVE: {
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        builder.CreateMemMove(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
        return {true, dst};
    }
    case BuiltinKind::BCOPY: {
        // bcopy(src, dst, n) — same as memmove(dst, src, n)
        auto src = convert_expression(expr->args[0].get());
        auto dst = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        builder.CreateMemMove(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
        return {true, nullptr}; // returns void
    }
    case BuiltinKind::BZERO: {
        // bzero(s, n) — same as memset(s, 0, n)
        auto dst = convert_expression(expr->args[0].get());
        auto size = convert_expression(expr->args[1].get());
        auto zero = llvm::ConstantInt::get(llvm::Type::getInt8Ty(ctx), 0);
        builder.CreateMemSet(dst, zero, size, llvm::MaybeAlign(1));
        return {true, nullptr}; // returns void
    }
    case BuiltinKind::MEMSET: {
        auto dst = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        val = builder.CreateTrunc(val, llvm::Type::getInt8Ty(ctx), "memset_val");
        builder.CreateMemSet(dst, val, size, llvm::MaybeAlign(1));
        return {true, dst};
    }
    // Fortified _chk variants — same as non-_chk, ignore the object-size arg
    case BuiltinKind::MEMCPY_CHK: {
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        // arg[3] is object_size — ignored
        builder.CreateMemCpy(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
        return {true, dst};
    }
    case BuiltinKind::MEMMOVE_CHK: {
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        builder.CreateMemMove(dst, llvm::MaybeAlign(1), src, llvm::MaybeAlign(1), size);
        return {true, dst};
    }
    case BuiltinKind::MEMSET_CHK: {
        auto dst = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        val = builder.CreateTrunc(val, llvm::Type::getInt8Ty(ctx), "memset_val");
        builder.CreateMemSet(dst, val, size, llvm::MaybeAlign(1));
        return {true, dst};
    }
    case BuiltinKind::STRCPY_CHK: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strcpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {dst, src}, "strcpy")};
    }
    case BuiltinKind::STPCPY_CHK: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "stpcpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {dst, src}, "stpcpy")};
    }
    case BuiltinKind::STRNCPY_CHK: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strncpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        return {true, builder.CreateCall(callee, {dst, src, n}, "strncpy")};
    }
    case BuiltinKind::STRCAT_CHK: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strcat", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {dst, src}, "strcat")};
    }
    case BuiltinKind::STRNCAT_CHK: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strncat", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        return {true, builder.CreateCall(callee, {dst, src, n}, "strncat")};
    }
    // Fortified stdio _chk variants — call through to real libc functions
    case BuiltinKind::SPRINTF_CHK: {
        // __builtin___sprintf_chk(str, flag, os, fmt, ...) → sprintf(str, fmt, ...)
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i8_ptr_ty}, /*isVarArg=*/true);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "sprintf", ft);
        std::vector<llvm::Value*> args;
        args.push_back(convert_expression(expr->args[0].get())); // str
        // skip args[1] (flag) and args[2] (object_size)
        for (size_t i = 3; i < expr->args.size(); i++) {
            args.push_back(convert_expression(expr->args[i].get()));
        }
        return {true, builder.CreateCall(callee, args, "sprintf")};
    }
    case BuiltinKind::SNPRINTF_CHK: {
        // __builtin___snprintf_chk(str, maxlen, flag, os, fmt, ...) → snprintf(str, maxlen, fmt, ...)
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i64_ty, i8_ptr_ty}, /*isVarArg=*/true);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "snprintf", ft);
        std::vector<llvm::Value*> args;
        args.push_back(convert_expression(expr->args[0].get())); // str
        args.push_back(convert_expression(expr->args[1].get())); // maxlen
        // skip args[2] (flag) and args[3] (object_size)
        for (size_t i = 4; i < expr->args.size(); i++) {
            args.push_back(convert_expression(expr->args[i].get()));
        }
        return {true, builder.CreateCall(callee, args, "snprintf")};
    }
    case BuiltinKind::VSPRINTF_CHK: {
        // __builtin___vsprintf_chk(str, flag, os, fmt, ap) → vsprintf(str, fmt, ap)
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i8_ptr_ty, i8_ptr_ty}, /*isVarArg=*/false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "vsprintf", ft);
        auto str = convert_expression(expr->args[0].get());
        // skip args[1] (flag) and args[2] (object_size)
        auto fmt = convert_expression(expr->args[3].get());
        auto ap = convert_expression(expr->args[4].get());
        return {true, builder.CreateCall(callee, {str, fmt, ap}, "vsprintf")};
    }
    case BuiltinKind::VSNPRINTF_CHK: {
        // __builtin___vsnprintf_chk(str, maxlen, flag, os, fmt, ap) → vsnprintf(str, maxlen, fmt, ap)
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i64_ty, i8_ptr_ty, i8_ptr_ty}, /*isVarArg=*/false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "vsnprintf", ft);
        auto str = convert_expression(expr->args[0].get());
        auto maxlen = convert_expression(expr->args[1].get());
        // skip args[2] (flag) and args[3] (object_size)
        auto fmt = convert_expression(expr->args[4].get());
        auto ap = convert_expression(expr->args[5].get());
        return {true, builder.CreateCall(callee, {str, maxlen, fmt, ap}, "vsnprintf")};
    }
    case BuiltinKind::MEMCMP: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "memcmp", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        if (size->getType() != i64_ty) size = builder.CreateIntCast(size, i64_ty, false);
        return {true, builder.CreateCall(callee, {dst, src, size}, "memcmp")};
    }
    case BuiltinKind::MEMCMP_EQ: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "memcmp", ft);
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto size = convert_expression(expr->args[2].get());
        if (size->getType() != i64_ty) {
            size = builder.CreateIntCast(size, i64_ty, false);
        }
        auto cmp = builder.CreateCall(callee, {lhs, rhs, size}, "memcmp_eq_cmp");
        auto is_eq = builder.CreateICmpEQ(cmp, llvm::ConstantInt::get(i32_ty, 0), "memcmp_eq");
        return {true, builder.CreateZExt(is_eq, i32_ty, "memcmp_eq_i32")};
    }
    case BuiltinKind::STRCMP: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {ptr_ty, ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strcmp", ft);
        auto s1 = convert_expression(expr->args[0].get());
        auto s2 = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {s1, s2}, "strcmp")};
    }
    case BuiltinKind::STRNCMP: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {ptr_ty, ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strncmp", ft);
        auto s1 = convert_expression(expr->args[0].get());
        auto s2 = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != i64_ty) n = builder.CreateIntCast(n, i64_ty, false);
        return {true, builder.CreateCall(callee, {s1, s2, n}, "strncmp")};
    }
    case BuiltinKind::MEMCHR: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i32_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "memchr", ft);
        auto s = convert_expression(expr->args[0].get());
        auto c = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != i64_ty) n = builder.CreateIntCast(n, i64_ty, false);
        return {true, builder.CreateCall(callee, {s, c, n}, "memchr")};
    }
    case BuiltinKind::STRLEN: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i64_ty, {i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strlen", ft);
        auto s = convert_expression(expr->args[0].get());
        return {true, builder.CreateCall(callee, {s}, "strlen")};
    }
    case BuiltinKind::STRCSPN:
    case BuiltinKind::STRSPN: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i64_ty, {ptr_ty, ptr_ty}, false);
        const char* name = expr->kind == BuiltinKind::STRCSPN ? "strcspn" : "strspn";
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        auto s1 = convert_expression(expr->args[0].get());
        auto s2 = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {s1, s2}, name)};
    }
    case BuiltinKind::STRCHR:
    case BuiltinKind::STRRCHR: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i32_ty}, false);
        const char* name = expr->kind == BuiltinKind::STRCHR ? "strchr" : "strrchr";
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        auto s = convert_expression(expr->args[0].get());
        auto c = convert_expression(expr->args[1].get());
        if (c->getType() != i32_ty) c = builder.CreateIntCast(c, i32_ty, true);
        return {true, builder.CreateCall(callee, {s, c}, name)};
    }
    case BuiltinKind::STRSTR: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strstr", ft);
        auto s1 = convert_expression(expr->args[0].get());
        auto s2 = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {s1, s2}, "strstr")};
    }
    case BuiltinKind::STRDUP: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strdup", ft);
        auto s = convert_expression(expr->args[0].get());
        return {true, builder.CreateCall(callee, {s}, "strdup")};
    }
    case BuiltinKind::STPNCPY: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* size_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, size_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "stpncpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != size_ty) n = builder.CreateIntCast(n, size_ty, false);
        return {true, builder.CreateCall(callee, {dst, src, n}, "stpncpy")};
    }
    case BuiltinKind::STRNDUP: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* size_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, size_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strndup", ft);
        auto s = convert_expression(expr->args[0].get());
        auto n = convert_expression(expr->args[1].get());
        if (n->getType() != size_ty) n = builder.CreateIntCast(n, size_ty, false);
        return {true, builder.CreateCall(callee, {s, n}, "strndup")};
    }
    case BuiltinKind::STRNCASECMP: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* size_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {ptr_ty, ptr_ty, size_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strncasecmp", ft);
        auto s1 = convert_expression(expr->args[0].get());
        auto s2 = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != size_ty) n = builder.CreateIntCast(n, size_ty, false);
        return {true, builder.CreateCall(callee, {s1, s2, n}, "strncasecmp")};
    }
    case BuiltinKind::STRCPY: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strcpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {dst, src}, "strcpy")};
    }
    case BuiltinKind::STPCPY: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "stpcpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {dst, src}, "stpcpy")};
    }
    case BuiltinKind::MEMPCPY: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != i64_ty) n = builder.CreateIntCast(n, i64_ty, false);
        auto* memcpy_ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto memcpy_callee = get_or_declare_libc_func(module.get(), ctx, "memcpy", memcpy_ft);
        auto dst_i8 = cast_llvm_type(dst, i8_ptr_ty, true);
        auto src_i8 = cast_llvm_type(src, i8_ptr_ty, true);
        builder.CreateCall(memcpy_callee, {dst_i8, src_i8, n}, "mempcpy.memcpy");
        auto end_i8 = builder.CreateInBoundsGEP(llvm::Type::getInt8Ty(ctx), dst_i8, n, "mempcpy.end");
        if (end_i8->getType() != dst->getType()) {
            return {true, cast_llvm_type(end_i8, dst->getType(), true)};
        }
        return {true, end_i8};
    }
    case BuiltinKind::STRNCPY: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strncpy", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != i64_ty) n = builder.CreateIntCast(n, i64_ty, false);
        return {true, builder.CreateCall(callee, {dst, src, n}, "strncpy")};
    }
    case BuiltinKind::STRCAT: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strcat", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        return {true, builder.CreateCall(callee, {dst, src}, "strcat")};
    }
    case BuiltinKind::STRNCAT: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "strncat", ft);
        auto dst = convert_expression(expr->args[0].get());
        auto src = convert_expression(expr->args[1].get());
        auto n = convert_expression(expr->args[2].get());
        if (n->getType() != i64_ty) n = builder.CreateIntCast(n, i64_ty, false);
        return {true, builder.CreateCall(callee, {dst, src, n}, "strncat")};
    }

    // ========== Tier 2: Stack/cache builtins ==========
    case BuiltinKind::CLEAR_CACHE: {
        // __builtin___clear_cache(begin, end) — evaluate args for side effects, then no-op
        convert_expression(expr->args[0].get());
        convert_expression(expr->args[1].get());
        return {true, nullptr};
    }
    case BuiltinKind::CLEAR_PADDING: {
        // __builtin_clear_padding(ptr) is used for object representation hygiene.
        // Preserve evaluation of the pointer expression and lower as a no-op.
        convert_expression(expr->args[0].get());
        return {true, nullptr};
    }
    case BuiltinKind::PREFETCH: {
        // __builtin_prefetch is a performance hint only. Preserve side effects of
        // all arguments but lower to no-op to avoid target-specific relocation issues.
        for (auto& arg : expr->args) {
            convert_expression(arg.get());
        }
        return {true, nullptr};
    }
    case BuiltinKind::RETURN_ADDRESS: {
        auto level = convert_expression(expr->args[0].get());
        level = builder.CreateIntCast(level, llvm::Type::getInt32Ty(ctx), false);
        llvm::Function* ret_addr_fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::returnaddress);
        return {true, builder.CreateCall(ret_addr_fn, {level}, "return_addr")};
    }
    case BuiltinKind::FRAME_ADDRESS: {
        auto level = convert_expression(expr->args[0].get());
        level = builder.CreateIntCast(level, llvm::Type::getInt32Ty(ctx), false);
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        llvm::Function* frame_addr_fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::frameaddress, {ptr_ty});
        return {true, builder.CreateCall(frame_addr_fn, {level}, "frame_addr")};
    }
    case BuiltinKind::EXTRACT_RETURN_ADDR: {
        // Identity on most platforms
        return {true, convert_expression(expr->args[0].get())};
    }
    case BuiltinKind::ALLOCA: {
        auto size = convert_expression(expr->args[0].get());
        auto* i8_ty = llvm::Type::getInt8Ty(ctx);
        return {true, builder.CreateAlloca(i8_ty, size, "builtin_alloca")};
    }
    case BuiltinKind::STACK_SAVE: {
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        llvm::Function* fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::stacksave, {ptr_ty});
        return {true, builder.CreateCall(fn, {}, "stack_save")};
    }
    case BuiltinKind::STACK_RESTORE: {
        auto ptr = convert_expression(expr->args[0].get());
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        llvm::Function* fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::stackrestore, {ptr_ty});
        builder.CreateCall(fn, {ptr});
        return {true, llvm::Constant::getNullValue(ptr_ty)};
    }
    default:
        return {};
    }
}

static BuiltinLoweringResult lower_builtin_atomic_and_sync_group(
    ASTToLLVM& lower, BuiltinCallExpr* expr) {
    auto& builder = lower.builder;
    auto& module = lower.module;
    auto& ctx = *lower.context;
    auto convert_expression = [&](Expr* expression) {
        return lower.convert_expression(expression);
    };
    auto convert_type = [&](const auto& ctype) {
        return lower.convert_type(ctype);
    };
    auto cast_llvm_type =
        [&](llvm::Value* value, llvm::Type* dest_type, bool is_unsigned) {
        return lower.cast_llvm_type(value, dest_type, is_unsigned);
    };
    auto get_atomic_semantic_type =
        [&](Expr* ptr_expr) -> std::pair<std::shared_ptr<PointerType>, llvm::Type*> {
        auto ptr_ctype = ptr_expr->get_type().as_shared<PointerType>();
        llvm::Type* semantic_type = ptr_ctype ? convert_type(ptr_ctype->pointed_type) : nullptr;
        return {ptr_ctype, semantic_type};
    };
    auto get_atomic_storage_type =
        [&](const std::shared_ptr<PointerType>& ptr_ctype,
            llvm::Type* semantic_type) -> llvm::Type* {
        if (!ptr_ctype || !ptr_ctype->pointed_type) {
            return semantic_type;
        }
        auto canonical_pointee = desugar_type(ptr_ctype->pointed_type, lower.ast_ctx.get());
        if (auto builtin = canonical_pointee.as_shared<BuiltinType>()) {
            if (builtin->builtin_kind == BuiltinTypes::Bool) {
                return llvm::Type::getInt8Ty(ctx);
            }
        }
        return semantic_type;
    };
    auto cast_to_atomic_semantic_type = [&](Expr* source_expr, llvm::Value* value,
                                            llvm::Type* semantic_type) {
        if (!semantic_type || value->getType() == semantic_type) {
            return value;
        }
        bool src_unsigned = source_expr && source_expr->get_type() &&
            source_expr->get_type()->isUnsigned();
        return cast_llvm_type(value, semantic_type, src_unsigned);
    };
    auto cast_to_atomic_storage_type = [&](llvm::Value* value, llvm::Type* semantic_type,
                                           llvm::Type* storage_type) {
        if (!storage_type || value->getType() == storage_type) {
            return value;
        }
        llvm::Type* source_type = semantic_type ? semantic_type : value->getType();
        bool source_is_unsigned = source_type->isIntegerTy();
        return cast_llvm_type(value, storage_type, source_is_unsigned);
    };
    auto cast_from_atomic_storage_type = [&](llvm::Value* value, llvm::Type* semantic_type) {
        if (!semantic_type || value->getType() == semantic_type) {
            return value;
        }
        bool semantic_is_unsigned = semantic_type->isIntegerTy();
        return cast_llvm_type(value, semantic_type, semantic_is_unsigned);
    };

    switch (expr->kind) {
    case BuiltinKind::ATOMIC_LOAD_N: {
        auto ptr = convert_expression(expr->args[0].get());
        auto [ptr_ctype, value_type] = get_atomic_semantic_type(expr->args[0].get());
        if (!value_type) {
            value_type = convert_type(expr->result_type);
        }
        llvm::Type* storage_type = get_atomic_storage_type(ptr_ctype, value_type);

        if (expr->args.size() == 3) {
            // Generic __atomic_load(ptr, out_ptr, order): load then store through out_ptr.
            auto out_ptr = convert_expression(expr->args[1].get());
            auto order_val = eval_constexpr_i64(
                expr->args[2].get(), ConstEvalMode::builtin_query()).value_or(5);
            auto ordering = map_memory_order(order_val);
            auto* load = builder.CreateLoad(storage_type, ptr, "atomic_load");
            load->setAtomic(ordering);
            builder.CreateStore(cast_from_atomic_storage_type(load, value_type), out_ptr);
            return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
        }

        auto order_val = eval_constexpr_i64(
            expr->args[1].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto ordering = map_memory_order(order_val);
        auto* load = builder.CreateLoad(storage_type, ptr, "atomic_load");
        load->setAtomic(ordering);
        return {true, cast_from_atomic_storage_type(load, value_type)};
    }
    case BuiltinKind::ATOMIC_STORE_N: {
        auto ptr = convert_expression(expr->args[0].get());
        auto [ptr_ctype, value_type] = get_atomic_semantic_type(expr->args[0].get());
        llvm::Type* storage_type = get_atomic_storage_type(ptr_ctype, value_type);

        auto val = convert_expression(expr->args[1].get());
        auto val_ptr_ctype = expr->args[1]->get_type().as_shared<PointerType>();
        bool val_is_pointer_to_value =
            ptr_ctype && val_ptr_ctype &&
            val_ptr_ctype->pointed_type.equals_qualified(ptr_ctype->pointed_type);
        if (val_is_pointer_to_value && value_type) {
            val = builder.CreateLoad(value_type, val, "atomic_store_val");
        }
        val = cast_to_atomic_semantic_type(expr->args[1].get(), val, value_type);
        val = cast_to_atomic_storage_type(val, value_type, storage_type);

        auto order_val = eval_constexpr_i64(
            expr->args[2].get(), ConstEvalMode::builtin_query()).value_or(5);
        if (!is_valid_atomic_store_order(order_val)) {
            // GCC/Clang keep compiling these invalid store-order forms and leave
            // the target object unchanged in this test environment.
            return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
        }
        auto ordering = map_memory_order(order_val);
        auto* store = builder.CreateStore(val, ptr);
        store->setAtomic(ordering);
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    case BuiltinKind::ATOMIC_EXCHANGE_N: {
        auto ptr = convert_expression(expr->args[0].get());
        auto [ptr_ctype, value_type] = get_atomic_semantic_type(expr->args[0].get());
        llvm::Type* storage_type = get_atomic_storage_type(ptr_ctype, value_type);

        if (expr->args.size() == 4) {
            // Generic __atomic_exchange(ptr, value_ptr, out_ptr, order)
            auto value_ptr = convert_expression(expr->args[1].get());
            auto out_ptr = convert_expression(expr->args[2].get());
            auto order_val = eval_constexpr_i64(
                expr->args[3].get(), ConstEvalMode::builtin_query()).value_or(5);
            auto ordering = map_memory_order(order_val);
            llvm::Value* desired = value_ptr;
            if (value_type) {
                desired = builder.CreateLoad(value_type, value_ptr, "atomic_exchange_val");
            }
            desired = cast_to_atomic_storage_type(desired, value_type, storage_type);
            auto* old = builder.CreateAtomicRMW(
                llvm::AtomicRMWInst::Xchg, ptr, desired, llvm::MaybeAlign(0), ordering);
            builder.CreateStore(cast_from_atomic_storage_type(old, value_type), out_ptr);
            return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
        }

        auto val = convert_expression(expr->args[1].get());
        val = cast_to_atomic_semantic_type(expr->args[1].get(), val, value_type);
        val = cast_to_atomic_storage_type(val, value_type, storage_type);
        auto order_val = eval_constexpr_i64(
            expr->args[2].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto ordering = map_memory_order(order_val);
        auto* old = builder.CreateAtomicRMW(
            llvm::AtomicRMWInst::Xchg, ptr, val, llvm::MaybeAlign(0), ordering);
        return {true, cast_from_atomic_storage_type(old, value_type)};
    }
    case BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N: {
        auto ptr = convert_expression(expr->args[0].get());
        auto expected_ptr = convert_expression(expr->args[1].get());
        auto [ptr_ctype, value_type] = get_atomic_semantic_type(expr->args[0].get());
        llvm::Type* storage_type = get_atomic_storage_type(ptr_ctype, value_type);

        auto desired = convert_expression(expr->args[2].get());
        auto desired_ptr_ctype = expr->args[2]->get_type().as_shared<PointerType>();
        bool desired_is_pointer_to_value =
            ptr_ctype && desired_ptr_ctype &&
            desired_ptr_ctype->pointed_type.equals_qualified(ptr_ctype->pointed_type);
        if (desired_is_pointer_to_value && value_type) {
            desired = builder.CreateLoad(value_type, desired, "cmpxchg_desired");
        }
        desired = cast_to_atomic_semantic_type(expr->args[2].get(), desired, value_type);
        desired = cast_to_atomic_storage_type(desired, value_type, storage_type);

        // _n and generic __atomic_compare_exchange take 6 args with weak flag.
        // __c11_atomic_compare_exchange_{strong,weak} take 5 args.
        size_t success_idx = expr->args.size() == 6 ? 4 : 3;
        size_t failure_idx = expr->args.size() == 6 ? 5 : 4;
        auto success_order = eval_constexpr_i64(
            expr->args[success_idx].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto failure_order = eval_constexpr_i64(
            expr->args[failure_idx].get(), ConstEvalMode::builtin_query()).value_or(5);

        if (!value_type) {
            value_type = desired->getType();
        }
        if (!storage_type) {
            storage_type = value_type;
        }
        llvm::Value* expected = builder.CreateLoad(value_type, expected_ptr, "cmpxchg_expected");
        expected = cast_to_atomic_storage_type(expected, value_type, storage_type);
        auto* cmpxchg = builder.CreateAtomicCmpXchg(ptr, expected, desired,
            llvm::MaybeAlign(0),
            map_memory_order(success_order),
            map_memory_order(failure_order));
        auto* old_val = builder.CreateExtractValue(cmpxchg, {0}, "cmpxchg_old");
        auto* success = builder.CreateExtractValue(cmpxchg, {1}, "cmpxchg_success");
        auto* func = builder.GetInsertBlock()->getParent();
        auto* fail_bb = llvm::BasicBlock::Create(ctx, "cmpxchg_fail", func);
        auto* end_bb = llvm::BasicBlock::Create(ctx, "cmpxchg_end", func);
        builder.CreateCondBr(success, end_bb, fail_bb);
        builder.SetInsertPoint(fail_bb);
        // GCC/Clang contract: on failure write observed memory value back to
        // expected pointer so caller can retry with the new compare value.
        builder.CreateStore(cast_from_atomic_storage_type(old_val, value_type), expected_ptr);
        builder.CreateBr(end_bb);
        builder.SetInsertPoint(end_bb);
        return {true, builder.CreateZExt(success, llvm::Type::getInt8Ty(ctx), "cmpxchg_bool")};
    }
    case BuiltinKind::ATOMIC_IS_LOCK_FREE: {
        int64_t size = expr->args.empty()
            ? static_cast<int64_t>(module->getDataLayout().getPointerSize())
            : eval_constexpr_i64(expr->args[0].get(), ConstEvalMode::builtin_query()).value_or(
                static_cast<int64_t>(module->getDataLayout().getPointerSize()));
        bool lock_free = size > 0 && size <= 16;
        return {true, llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), lock_free ? 1 : 0)};
    }
    case BuiltinKind::C11_ATOMIC_INIT: {
        auto ptr = convert_expression(expr->args[0].get());
        auto ptr_ctype = expr->args[0]->get_type().as_shared<PointerType>();
        llvm::Type* value_type = ptr_ctype ? convert_type(ptr_ctype->pointed_type) : nullptr;
        auto init_val = convert_expression(expr->args[1].get());
        if (value_type && init_val->getType() != value_type) {
            bool src_unsigned = expr->args[1]->get_type() && expr->args[1]->get_type()->isUnsigned();
            init_val = cast_llvm_type(init_val, value_type, src_unsigned);
        }
        builder.CreateStore(init_val, ptr);
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    case BuiltinKind::ATOMIC_FETCH_ADD:
    case BuiltinKind::ATOMIC_FETCH_SUB:
    case BuiltinKind::ATOMIC_FETCH_AND:
    case BuiltinKind::ATOMIC_FETCH_OR:
    case BuiltinKind::ATOMIC_FETCH_XOR:
    case BuiltinKind::ATOMIC_FETCH_NAND: {
        auto ptr = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        if (auto ptr_type = expr->args[0]->get_type().as_shared<PointerType>()) {
            llvm::Type* pointee_type = convert_type(ptr_type->pointed_type);
            if (pointee_type && val->getType() != pointee_type) {
                bool src_unsigned = expr->args[1]->get_type() && expr->args[1]->get_type()->isUnsigned();
                val = cast_llvm_type(val, pointee_type, src_unsigned);
            }
        }
        auto order_val = eval_constexpr_i64(
            expr->args[2].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto ordering = map_memory_order(order_val);
        llvm::AtomicRMWInst::BinOp op;
        switch (expr->kind) {
            case BuiltinKind::ATOMIC_FETCH_ADD: op = llvm::AtomicRMWInst::Add; break;
            case BuiltinKind::ATOMIC_FETCH_SUB: op = llvm::AtomicRMWInst::Sub; break;
            case BuiltinKind::ATOMIC_FETCH_AND: op = llvm::AtomicRMWInst::And; break;
            case BuiltinKind::ATOMIC_FETCH_OR:  op = llvm::AtomicRMWInst::Or;  break;
            case BuiltinKind::ATOMIC_FETCH_XOR: op = llvm::AtomicRMWInst::Xor; break;
            case BuiltinKind::ATOMIC_FETCH_NAND: op = llvm::AtomicRMWInst::Nand; break;
            default: op = llvm::AtomicRMWInst::Add; break;
        }
        return {true, builder.CreateAtomicRMW(op, ptr, val, llvm::MaybeAlign(0), ordering)};
    }
    case BuiltinKind::ATOMIC_ADD_FETCH:
    case BuiltinKind::ATOMIC_SUB_FETCH:
    case BuiltinKind::ATOMIC_AND_FETCH:
    case BuiltinKind::ATOMIC_OR_FETCH:
    case BuiltinKind::ATOMIC_XOR_FETCH:
    case BuiltinKind::ATOMIC_NAND_FETCH: {
        auto ptr = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        if (auto ptr_type = expr->args[0]->get_type().as_shared<PointerType>()) {
            llvm::Type* pointee_type = convert_type(ptr_type->pointed_type);
            if (pointee_type && val->getType() != pointee_type) {
                bool src_unsigned = expr->args[1]->get_type() && expr->args[1]->get_type()->isUnsigned();
                val = cast_llvm_type(val, pointee_type, src_unsigned);
            }
        }
        auto order_val = eval_constexpr_i64(
            expr->args[2].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto ordering = map_memory_order(order_val);
        llvm::AtomicRMWInst::BinOp op;
        switch (expr->kind) {
            case BuiltinKind::ATOMIC_ADD_FETCH: op = llvm::AtomicRMWInst::Add; break;
            case BuiltinKind::ATOMIC_SUB_FETCH: op = llvm::AtomicRMWInst::Sub; break;
            case BuiltinKind::ATOMIC_AND_FETCH: op = llvm::AtomicRMWInst::And; break;
            case BuiltinKind::ATOMIC_OR_FETCH:  op = llvm::AtomicRMWInst::Or;  break;
            case BuiltinKind::ATOMIC_XOR_FETCH: op = llvm::AtomicRMWInst::Xor; break;
            case BuiltinKind::ATOMIC_NAND_FETCH: op = llvm::AtomicRMWInst::Nand; break;
            default: op = llvm::AtomicRMWInst::Add; break;
        }
        auto* old = builder.CreateAtomicRMW(op, ptr, val, llvm::MaybeAlign(0), ordering);
        // Compute new value: old OP val
        switch (expr->kind) {
            case BuiltinKind::ATOMIC_ADD_FETCH: return {true, builder.CreateAdd(old, val, "add_fetch")};
            case BuiltinKind::ATOMIC_SUB_FETCH: return {true, builder.CreateSub(old, val, "sub_fetch")};
            case BuiltinKind::ATOMIC_AND_FETCH: return {true, builder.CreateAnd(old, val, "and_fetch")};
            case BuiltinKind::ATOMIC_OR_FETCH:  return {true, builder.CreateOr(old, val, "or_fetch")};
            case BuiltinKind::ATOMIC_XOR_FETCH: return {true, builder.CreateXor(old, val, "xor_fetch")};
            case BuiltinKind::ATOMIC_NAND_FETCH: {
                auto* and_val = builder.CreateAnd(old, val);
                return {true, builder.CreateNot(and_val, "nand_fetch")};
            }
            default: return {true, old};
        }
    }
    case BuiltinKind::ATOMIC_THREAD_FENCE: {
        auto order_val = eval_constexpr_i64(
            expr->args[0].get(), ConstEvalMode::builtin_query()).value_or(5);
        builder.CreateFence(map_memory_order(order_val));
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    case BuiltinKind::ATOMIC_SIGNAL_FENCE: {
        auto order_val = eval_constexpr_i64(
            expr->args[0].get(), ConstEvalMode::builtin_query()).value_or(5);
        builder.CreateFence(map_memory_order(order_val), llvm::SyncScope::SingleThread);
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    case BuiltinKind::ATOMIC_TEST_AND_SET: {
        auto ptr = convert_expression(expr->args[0].get());
        auto order_val = eval_constexpr_i64(
            expr->args[1].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto* one = llvm::ConstantInt::get(llvm::Type::getInt8Ty(ctx), 1);
        auto* old = builder.CreateAtomicRMW(llvm::AtomicRMWInst::Xchg, ptr, one,
            llvm::MaybeAlign(1), map_memory_order(order_val));
        return {true, builder.CreateICmpNE(old, llvm::ConstantInt::get(llvm::Type::getInt8Ty(ctx), 0), "test_and_set")};
    }
    case BuiltinKind::ATOMIC_CLEAR: {
        auto ptr = convert_expression(expr->args[0].get());
        auto order_val = eval_constexpr_i64(
            expr->args[1].get(), ConstEvalMode::builtin_query()).value_or(5);
        auto* store = builder.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt8Ty(ctx), 0), ptr);
        store->setAtomic(map_memory_order(order_val));
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    // ========== Legacy __sync_* builtins ==========
    case BuiltinKind::SYNC_FETCH_AND_ADD:
    case BuiltinKind::SYNC_FETCH_AND_SUB:
    case BuiltinKind::SYNC_FETCH_AND_OR:
    case BuiltinKind::SYNC_FETCH_AND_AND:
    case BuiltinKind::SYNC_FETCH_AND_XOR:
    case BuiltinKind::SYNC_FETCH_AND_NAND: {
        auto ptr = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        llvm::AtomicRMWInst::BinOp op;
        switch (expr->kind) {
            case BuiltinKind::SYNC_FETCH_AND_ADD: op = llvm::AtomicRMWInst::Add; break;
            case BuiltinKind::SYNC_FETCH_AND_SUB: op = llvm::AtomicRMWInst::Sub; break;
            case BuiltinKind::SYNC_FETCH_AND_OR:  op = llvm::AtomicRMWInst::Or;  break;
            case BuiltinKind::SYNC_FETCH_AND_AND: op = llvm::AtomicRMWInst::And; break;
            case BuiltinKind::SYNC_FETCH_AND_XOR: op = llvm::AtomicRMWInst::Xor; break;
            case BuiltinKind::SYNC_FETCH_AND_NAND: op = llvm::AtomicRMWInst::Nand; break;
            default: op = llvm::AtomicRMWInst::Add; break;
        }
        return {true, builder.CreateAtomicRMW(op, ptr, val, llvm::MaybeAlign(0),
            llvm::AtomicOrdering::SequentiallyConsistent)};
    }
    case BuiltinKind::SYNC_ADD_AND_FETCH:
    case BuiltinKind::SYNC_SUB_AND_FETCH:
    case BuiltinKind::SYNC_OR_AND_FETCH:
    case BuiltinKind::SYNC_AND_AND_FETCH:
    case BuiltinKind::SYNC_XOR_AND_FETCH:
    case BuiltinKind::SYNC_NAND_AND_FETCH: {
        auto ptr = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        llvm::AtomicRMWInst::BinOp op;
        switch (expr->kind) {
            case BuiltinKind::SYNC_ADD_AND_FETCH: op = llvm::AtomicRMWInst::Add; break;
            case BuiltinKind::SYNC_SUB_AND_FETCH: op = llvm::AtomicRMWInst::Sub; break;
            case BuiltinKind::SYNC_OR_AND_FETCH:  op = llvm::AtomicRMWInst::Or;  break;
            case BuiltinKind::SYNC_AND_AND_FETCH: op = llvm::AtomicRMWInst::And; break;
            case BuiltinKind::SYNC_XOR_AND_FETCH: op = llvm::AtomicRMWInst::Xor; break;
            case BuiltinKind::SYNC_NAND_AND_FETCH: op = llvm::AtomicRMWInst::Nand; break;
            default: op = llvm::AtomicRMWInst::Add; break;
        }
        auto* old = builder.CreateAtomicRMW(op, ptr, val, llvm::MaybeAlign(0),
            llvm::AtomicOrdering::SequentiallyConsistent);
        switch (expr->kind) {
            case BuiltinKind::SYNC_ADD_AND_FETCH: return {true, builder.CreateAdd(old, val)};
            case BuiltinKind::SYNC_SUB_AND_FETCH: return {true, builder.CreateSub(old, val)};
            case BuiltinKind::SYNC_OR_AND_FETCH:  return {true, builder.CreateOr(old, val)};
            case BuiltinKind::SYNC_AND_AND_FETCH: return {true, builder.CreateAnd(old, val)};
            case BuiltinKind::SYNC_XOR_AND_FETCH: return {true, builder.CreateXor(old, val)};
            case BuiltinKind::SYNC_NAND_AND_FETCH: {
                auto* and_val = builder.CreateAnd(old, val);
                return {true, builder.CreateNot(and_val)};
            }
            default: return {true, old};
        }
    }
    case BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP: {
        auto ptr = convert_expression(expr->args[0].get());
        auto oldval = convert_expression(expr->args[1].get());
        auto newval = convert_expression(expr->args[2].get());
        auto* cmpxchg = builder.CreateAtomicCmpXchg(ptr, oldval, newval,
            llvm::MaybeAlign(0),
            llvm::AtomicOrdering::SequentiallyConsistent,
            llvm::AtomicOrdering::SequentiallyConsistent);
        auto* success = builder.CreateExtractValue(cmpxchg, {1}, "sync_cas_success");
        return {true, builder.CreateZExt(success, llvm::Type::getInt8Ty(ctx), "sync_cas_bool")};
    }
    case BuiltinKind::SYNC_VAL_COMPARE_AND_SWAP: {
        auto ptr = convert_expression(expr->args[0].get());
        auto oldval = convert_expression(expr->args[1].get());
        auto newval = convert_expression(expr->args[2].get());
        auto* cmpxchg = builder.CreateAtomicCmpXchg(ptr, oldval, newval,
            llvm::MaybeAlign(0),
            llvm::AtomicOrdering::SequentiallyConsistent,
            llvm::AtomicOrdering::SequentiallyConsistent);
        return {true, builder.CreateExtractValue(cmpxchg, {0}, "sync_cas_val")};
    }
    case BuiltinKind::SYNC_SYNCHRONIZE: {
        builder.CreateFence(llvm::AtomicOrdering::SequentiallyConsistent);
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    case BuiltinKind::SYNC_LOCK_TEST_AND_SET: {
        auto ptr = convert_expression(expr->args[0].get());
        auto val = convert_expression(expr->args[1].get());
        return {true, builder.CreateAtomicRMW(llvm::AtomicRMWInst::Xchg, ptr, val,
            llvm::MaybeAlign(0), llvm::AtomicOrdering::Acquire)};
    }
    case BuiltinKind::SYNC_LOCK_RELEASE: {
        auto ptr = convert_expression(expr->args[0].get());
        // Determine the type from what the pointer points to
        auto ptr_type = expr->args[0]->get_type();
        auto* pointed = dyn_cast<PointerType>(ptr_type.get());
        auto* val_type = pointed ? convert_type(pointed->pointed_type) : llvm::Type::getInt32Ty(ctx);
        auto* zero = llvm::Constant::getNullValue(val_type);
        auto* store = builder.CreateStore(zero, ptr);
        store->setAtomic(llvm::AtomicOrdering::Release);
        return {true, llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx))};
    }
    default:
        return {};
    }
}

// Helper: cast integer argument to the canonical type for a builtin family
// (e.g., __builtin_clz operates on unsigned int, __builtin_clzl on unsigned long).
static llvm::Value* cast_builtin_integer_arg(
    ASTToLLVM& lower, llvm::Value* val, BuiltinTypes bt, bool src_unsigned) {
    if (!lower.type_ctx) return val;
    auto ctype = lower.type_ctx->get_builtin(bt);
    if (!ctype) return val;
    llvm::Type* target_ty = lower.convert_type(ctype);
    if (!target_ty || !target_ty->isIntegerTy() || val->getType() == target_ty) return val;
    return lower.cast_llvm_type(val, target_ty, src_unsigned);
}

// ── IO builtins: printf, fprintf, sprintf, snprintf, puts, putchar ──────────
static BuiltinLoweringResult lower_builtin_io_group(
    ASTToLLVM& lower, BuiltinCallExpr* expr) {
    auto& builder = lower.builder;
    auto& module = lower.module;
    auto& ctx = *lower.context;
    auto convert_expression = [&](Expr* e) { return lower.convert_expression(e); };

    switch (expr->kind) {
    case BuiltinKind::PRINTF: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty}, true);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "printf", ft);
        std::vector<llvm::Value*> args;
        for (auto& arg : expr->args) args.push_back(convert_expression(arg.get()));
        return {true, builder.CreateCall(callee, args, "printf")};
    }
    case BuiltinKind::FPRINTF: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i8_ptr_ty}, true);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "fprintf", ft);
        std::vector<llvm::Value*> args;
        for (auto& arg : expr->args) args.push_back(convert_expression(arg.get()));
        return {true, builder.CreateCall(callee, args, "fprintf")};
    }
    case BuiltinKind::SPRINTF: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i8_ptr_ty}, true);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "sprintf", ft);
        std::vector<llvm::Value*> args;
        for (auto& arg : expr->args) args.push_back(convert_expression(arg.get()));
        return {true, builder.CreateCall(callee, args, "sprintf")};
    }
    case BuiltinKind::SNPRINTF: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty, i64_ty, i8_ptr_ty}, true);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "snprintf", ft);
        std::vector<llvm::Value*> args;
        for (auto& arg : expr->args) args.push_back(convert_expression(arg.get()));
        if (args.size() > 1 && args[1]->getType() != i64_ty)
            args[1] = builder.CreateIntCast(args[1], i64_ty, false);
        return {true, builder.CreateCall(callee, args, "snprintf")};
    }
    case BuiltinKind::PUTS: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "puts", ft);
        auto s = convert_expression(expr->args[0].get());
        return {true, builder.CreateCall(callee, {s}, "puts")};
    }
    case BuiltinKind::PUTCHAR: {
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "putchar", ft);
        auto c = convert_expression(expr->args[0].get());
        return {true, builder.CreateCall(callee, {c}, "putchar")};
    }
    default:
        return {};
    }
}

// ── Bit manipulation: clz, ctz, ffs, popcount, bswap, bzhi, clrsb, parity ──
static BuiltinLoweringResult lower_builtin_bit_group(
    ASTToLLVM& lower, BuiltinCallExpr* expr) {
    auto& builder = lower.builder;
    auto& module = lower.module;
    auto& ctx = *lower.context;
    auto convert_expression = [&](Expr* e) { return lower.convert_expression(e); };
    auto cast_int_arg = [&](llvm::Value* val, BuiltinTypes bt, bool src_unsigned) {
        return cast_builtin_integer_arg(lower, val, bt, src_unsigned);
    };

    switch (expr->kind) {
    case BuiltinKind::CLZ:
    case BuiltinKind::CLZL:
    case BuiltinKind::CLZLL: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        BuiltinTypes arg_ty = BuiltinTypes::UInt;
        if (expr->kind == BuiltinKind::CLZL) arg_ty = BuiltinTypes::ULong;
        else if (expr->kind == BuiltinKind::CLZLL) arg_ty = BuiltinTypes::ULongLong;
        val = cast_int_arg(val, arg_ty, src_unsigned);
        llvm::Function* ctlz = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::ctlz, {val->getType()});
        auto* is_zero_undef = llvm::ConstantInt::getTrue(ctx);
        auto* result = builder.CreateCall(ctlz, {val, is_zero_undef}, "clz");
        return {true, builder.CreateIntCast(result, llvm::Type::getInt32Ty(ctx), false, "clz_int")};
    }
    case BuiltinKind::CTZ:
    case BuiltinKind::CTZL:
    case BuiltinKind::CTZLL: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        BuiltinTypes arg_ty = BuiltinTypes::UInt;
        if (expr->kind == BuiltinKind::CTZL) arg_ty = BuiltinTypes::ULong;
        else if (expr->kind == BuiltinKind::CTZLL) arg_ty = BuiltinTypes::ULongLong;
        val = cast_int_arg(val, arg_ty, src_unsigned);
        llvm::Function* cttz = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::cttz, {val->getType()});
        auto* is_zero_undef = llvm::ConstantInt::getTrue(ctx);
        auto* result = builder.CreateCall(cttz, {val, is_zero_undef}, "ctz");
        return {true, builder.CreateIntCast(result, llvm::Type::getInt32Ty(ctx), false, "ctz_int")};
    }
    case BuiltinKind::FFS:
    case BuiltinKind::FFSL:
    case BuiltinKind::FFSLL: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        BuiltinTypes arg_ty = BuiltinTypes::UInt;
        if (expr->kind == BuiltinKind::FFSL) arg_ty = BuiltinTypes::ULong;
        else if (expr->kind == BuiltinKind::FFSLL) arg_ty = BuiltinTypes::ULongLong;
        val = cast_int_arg(val, arg_ty, src_unsigned);
        auto* zero = llvm::ConstantInt::get(val->getType(), 0);
        auto* is_zero = builder.CreateICmpEQ(val, zero, "ffs_is_zero");
        llvm::Function* cttz = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::cttz, {val->getType()});
        auto* ctz_val = builder.CreateCall(cttz, {val, llvm::ConstantInt::getFalse(ctx)}, "ffs_ctz");
        auto* ctz_plus1 = builder.CreateAdd(ctz_val, llvm::ConstantInt::get(val->getType(), 1), "ffs_ctz_p1");
        auto* result = builder.CreateSelect(is_zero, zero, ctz_plus1, "ffs_result");
        return {true, builder.CreateIntCast(result, llvm::Type::getInt32Ty(ctx), true, "ffs_int")};
    }
    case BuiltinKind::POPCOUNT:
    case BuiltinKind::POPCOUNTL:
    case BuiltinKind::POPCOUNTLL: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        BuiltinTypes arg_ty = BuiltinTypes::UInt;
        if (expr->kind == BuiltinKind::POPCOUNTL) arg_ty = BuiltinTypes::ULong;
        else if (expr->kind == BuiltinKind::POPCOUNTLL) arg_ty = BuiltinTypes::ULongLong;
        val = cast_int_arg(val, arg_ty, src_unsigned);
        llvm::Function* ctpop = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::ctpop, {val->getType()});
        auto* result = builder.CreateCall(ctpop, {val}, "popcount");
        return {true, builder.CreateIntCast(result, llvm::Type::getInt32Ty(ctx), false, "popcount_int")};
    }
    case BuiltinKind::BSWAP16:
    case BuiltinKind::BSWAP32:
    case BuiltinKind::BSWAP64: {
        auto val = convert_expression(expr->args[0].get());
        llvm::Type* target_type;
        if (expr->kind == BuiltinKind::BSWAP16) target_type = llvm::Type::getInt16Ty(ctx);
        else if (expr->kind == BuiltinKind::BSWAP32) target_type = llvm::Type::getInt32Ty(ctx);
        else target_type = llvm::Type::getInt64Ty(ctx);
        val = builder.CreateIntCast(val, target_type, false, "bswap_cast");
        llvm::Function* bswap = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::bswap, {target_type});
        return {true, builder.CreateCall(bswap, {val}, "bswap")};
    }
    case BuiltinKind::IA32_BZHI_SI: {
        auto a = convert_expression(expr->args[0].get());
        auto p = convert_expression(expr->args[1].get());
        bool a_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        bool p_unsigned = expr->args[1]->get_type() && expr->args[1]->get_type()->isUnsigned();
        a = cast_int_arg(a, BuiltinTypes::UInt, a_unsigned);
        p = cast_int_arg(p, BuiltinTypes::UInt, p_unsigned);
        auto* int_ty = llvm::dyn_cast<llvm::IntegerType>(a->getType());
        if (!int_ty || p->getType() != a->getType()) {
            lower.error("__builtin_ia32_bzhi_si requires integer operands", expr->location);
            return {true, nullptr};
        }
        unsigned bits = int_ty->getBitWidth();
        auto* bitwidth = llvm::ConstantInt::get(int_ty, bits);
        auto* ge_width = builder.CreateICmpUGE(p, bitwidth, "bzhi_ge_width");
        auto* clamped_p = builder.CreateSelect(
            ge_width, llvm::ConstantInt::get(int_ty, bits - 1), p, "bzhi_clamped_p");
        auto* one = llvm::ConstantInt::get(int_ty, 1);
        auto* shifted = builder.CreateShl(one, clamped_p, "bzhi_shifted");
        auto* partial_mask = builder.CreateSub(shifted, one, "bzhi_partial_mask");
        auto* full_mask = llvm::ConstantInt::get(int_ty, llvm::APInt::getAllOnes(bits));
        auto* mask = builder.CreateSelect(ge_width, full_mask, partial_mask, "bzhi_mask");
        return {true, builder.CreateAnd(a, mask, "bzhi")};
    }
    case BuiltinKind::CLRSB:
    case BuiltinKind::CLRSBL:
    case BuiltinKind::CLRSBLL: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        BuiltinTypes arg_ty = BuiltinTypes::Int;
        if (expr->kind == BuiltinKind::CLRSBL) arg_ty = BuiltinTypes::Long;
        else if (expr->kind == BuiltinKind::CLRSBLL) arg_ty = BuiltinTypes::LongLong;
        val = cast_int_arg(val, arg_ty, src_unsigned);
        unsigned bits = val->getType()->getIntegerBitWidth();
        auto* shift_amt = llvm::ConstantInt::get(val->getType(), bits - 1);
        auto* sign_ext = builder.CreateAShr(val, shift_amt, "clrsb_signext");
        auto* xored = builder.CreateXor(val, sign_ext, "clrsb_xor");
        llvm::Function* ctlz = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::ctlz, {val->getType()});
        auto* clz_val = builder.CreateCall(ctlz, {xored, llvm::ConstantInt::getFalse(ctx)}, "clrsb_clz");
        auto* one = llvm::ConstantInt::get(val->getType(), 1);
        auto* result = builder.CreateSub(clz_val, one, "clrsb");
        return {true, builder.CreateIntCast(result, llvm::Type::getInt32Ty(ctx), true, "clrsb_int")};
    }
    case BuiltinKind::PARITY:
    case BuiltinKind::PARITYL:
    case BuiltinKind::PARITYLL: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        BuiltinTypes arg_ty = BuiltinTypes::UInt;
        if (expr->kind == BuiltinKind::PARITYL) arg_ty = BuiltinTypes::ULong;
        else if (expr->kind == BuiltinKind::PARITYLL) arg_ty = BuiltinTypes::ULongLong;
        val = cast_int_arg(val, arg_ty, src_unsigned);
        llvm::Function* ctpop = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::ctpop, {val->getType()});
        auto* pop = builder.CreateCall(ctpop, {val}, "parity_pop");
        auto* one = llvm::ConstantInt::get(val->getType(), 1);
        auto* result = builder.CreateAnd(pop, one, "parity");
        return {true, builder.CreateIntCast(result, llvm::Type::getInt32Ty(ctx), false, "parity_int")};
    }
    default:
        return {};
    }
}

// ── Math builtins: classification, constants, abs, transcendental, etc. ──────
static BuiltinLoweringResult lower_builtin_math_group(
    ASTToLLVM& lower, BuiltinCallExpr* expr) {
    auto& builder = lower.builder;
    auto& module = lower.module;
    auto& ctx = *lower.context;
    auto convert_expression = [&](Expr* e) { return lower.convert_expression(e); };
    auto convert_type = [&](auto t) { return lower.convert_type(t); };
    auto cast_int_arg = [&](llvm::Value* val, BuiltinTypes bt, bool src_unsigned) {
        return cast_builtin_integer_arg(lower, val, bt, src_unsigned);
    };
    auto builtin_llvm_type = [&](BuiltinTypes bt) -> llvm::Type* {
        if (!lower.type_ctx) {
            if (bt == BuiltinTypes::Float) return llvm::Type::getFloatTy(ctx);
            if (bt == BuiltinTypes::Double || bt == BuiltinTypes::LongDouble) {
                return llvm::Type::getDoubleTy(ctx);
            }
            if (bt == BuiltinTypes::Long || bt == BuiltinTypes::LongLong) {
                return llvm::Type::getInt64Ty(ctx);
            }
            return llvm::Type::getInt32Ty(ctx);
        }
        return convert_type(QualType(lower.type_ctx->get_builtin(bt)));
    };
    auto coerce_builtin_fp_arg =
        [&](llvm::Value* value, llvm::Type* target_ty, bool src_unsigned = false) -> llvm::Value* {
        if (!value || !target_ty || value->getType() == target_ty) {
            return value;
        }
        if (value->getType()->isFloatingPointTy()) {
            return builder.CreateFPCast(value, target_ty);
        }
        if (value->getType()->isIntegerTy()) {
            return src_unsigned ? builder.CreateUIToFP(value, target_ty) : builder.CreateSIToFP(value, target_ty);
        }
        return value;
    };
    auto coerce_builtin_fp_expr_arg =
        [&](Expr* arg, llvm::Type* target_ty) -> llvm::Value* {
        auto* value = convert_expression(arg);
        bool src_unsigned = arg && arg->get_type() && arg->get_type()->isUnsigned();
        return coerce_builtin_fp_arg(value, target_ty, src_unsigned);
    };
    auto result_fp_type = [&]() -> llvm::Type* {
        llvm::Type* fp_ty = convert_type(expr->result_type);
        if (fp_ty && fp_ty->isFloatingPointTy()) {
            return fp_ty;
        }
        return llvm::Type::getDoubleTy(ctx);
    };
    auto suffix_fp_type = [&](BuiltinKind kind) -> llvm::Type* {
        switch (kind) {
            case BuiltinKind::ILOGBF:
            case BuiltinKind::LRINTF:
            case BuiltinKind::LROUNDF:
            case BuiltinKind::LLRINTF:
            case BuiltinKind::LLROUNDF:
                return llvm::Type::getFloatTy(ctx);
            case BuiltinKind::ILOGBL:
            case BuiltinKind::LRINTL:
            case BuiltinKind::LROUNDL:
            case BuiltinKind::LLRINTL:
            case BuiltinKind::LLROUNDL:
                return builtin_llvm_type(BuiltinTypes::LongDouble);
            default:
                return llvm::Type::getDoubleTy(ctx);
        }
    };
    auto lower_unary_fp_intrinsic =
        [&](llvm::Intrinsic::ID id, const char* call_name) -> BuiltinLoweringResult {
        llvm::Type* fp_ty = result_fp_type();
        auto* val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* fn = llvm::Intrinsic::getDeclaration(module.get(), id, {fp_ty});
        return {true, builder.CreateCall(fn, {val}, call_name)};
    };
    auto lower_binary_fp_intrinsic =
        [&](llvm::Intrinsic::ID id, const char* call_name) -> BuiltinLoweringResult {
        llvm::Type* fp_ty = result_fp_type();
        auto* lhs = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* rhs = coerce_builtin_fp_expr_arg(expr->args[1].get(), fp_ty);
        auto* fn = llvm::Intrinsic::getDeclaration(module.get(), id, {fp_ty});
        return {true, builder.CreateCall(fn, {lhs, rhs}, call_name)};
    };
    auto lower_ternary_fp_intrinsic =
        [&](llvm::Intrinsic::ID id, const char* call_name) -> BuiltinLoweringResult {
        llvm::Type* fp_ty = result_fp_type();
        auto* a = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* b = coerce_builtin_fp_expr_arg(expr->args[1].get(), fp_ty);
        auto* c = coerce_builtin_fp_expr_arg(expr->args[2].get(), fp_ty);
        auto* fn = llvm::Intrinsic::getDeclaration(module.get(), id, {fp_ty});
        return {true, builder.CreateCall(fn, {a, b, c}, call_name)};
    };
    auto lower_unary_libm =
        [&](const char* name, const char* call_name) -> BuiltinLoweringResult {
        llvm::Type* fp_ty = result_fp_type();
        auto* val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* ft = llvm::FunctionType::get(fp_ty, {fp_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {val}, call_name)};
    };
    auto lower_binary_libm =
        [&](const char* name, const char* call_name) -> BuiltinLoweringResult {
        llvm::Type* fp_ty = result_fp_type();
        auto* lhs = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* rhs = coerce_builtin_fp_expr_arg(expr->args[1].get(), fp_ty);
        auto* ft = llvm::FunctionType::get(fp_ty, {fp_ty, fp_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {lhs, rhs}, call_name)};
    };

    switch (expr->kind) {
    // --- Float classification ---
    case BuiltinKind::ISNAN: {
        auto val = convert_expression(expr->args[0].get());
        auto* result = builder.CreateFCmpUNO(val, val, "isnan");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isnan_int")};
    }
    case BuiltinKind::ISINF: {
        auto val = convert_expression(expr->args[0].get());
        llvm::Function* fabs_fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::fabs, {val->getType()});
        auto* abs_val = builder.CreateCall(fabs_fn, {val}, "fabs");
        auto* inf = llvm::ConstantFP::getInfinity(val->getType());
        auto* result = builder.CreateFCmpOEQ(abs_val, inf, "isinf");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isinf_int")};
    }
    case BuiltinKind::ISINF_SIGN: {
        auto val = convert_expression(expr->args[0].get());
        auto* ty = val->getType();
        auto* pos_inf = llvm::ConstantFP::getInfinity(ty, false);
        auto* neg_inf = llvm::ConstantFP::getInfinity(ty, true);
        auto* is_pos = builder.CreateFCmpOEQ(val, pos_inf, "isinf_pos");
        auto* is_neg = builder.CreateFCmpOEQ(val, neg_inf, "isinf_neg");
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* pos_one = llvm::ConstantInt::get(i32_ty, 1);
        auto* neg_one = llvm::ConstantInt::getSigned(i32_ty, -1);
        auto* zero = llvm::ConstantInt::get(i32_ty, 0);
        return {true, builder.CreateSelect(is_pos, pos_one, builder.CreateSelect(is_neg, neg_one, zero))};
    }
    case BuiltinKind::ISFINITE: {
        auto val = convert_expression(expr->args[0].get());
        auto* zero = llvm::ConstantFP::get(val->getType(), 0.0);
        auto* is_ord = builder.CreateFCmpORD(val, zero, "is_ordered");
        llvm::Function* fabs_fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::fabs, {val->getType()});
        auto* abs_val = builder.CreateCall(fabs_fn, {val}, "fabs");
        auto* inf = llvm::ConstantFP::getInfinity(val->getType());
        auto* is_not_inf = builder.CreateFCmpONE(abs_val, inf, "is_not_inf");
        auto* result = builder.CreateAnd(is_ord, is_not_inf, "isfinite");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isfinite_int")};
    }
    case BuiltinKind::ISNORMAL: {
        auto val = convert_expression(expr->args[0].get());
        auto* ty = val->getType();
        auto* zero = llvm::ConstantFP::get(ty, 0.0);
        auto* is_ord = builder.CreateFCmpORD(val, zero, "isnormal_ord");
        llvm::Function* fabs_fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::fabs, {ty});
        auto* abs_val = builder.CreateCall(fabs_fn, {val}, "fabs");
        auto* inf = llvm::ConstantFP::getInfinity(ty);
        auto* is_not_inf = builder.CreateFCmpONE(abs_val, inf, "isnormal_not_inf");
        llvm::APFloat min_normal = [&]() -> llvm::APFloat {
            if (ty->isHalfTy()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::IEEEhalf());
            if (ty->isBFloatTy()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::BFloat());
            if (ty->isFloatTy()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::IEEEsingle());
            if (ty->isDoubleTy()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::IEEEdouble());
            if (ty->isX86_FP80Ty()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::x87DoubleExtended());
            if (ty->isFP128Ty()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::IEEEquad());
            if (ty->isPPC_FP128Ty()) return llvm::APFloat::getSmallestNormalized(llvm::APFloat::PPCDoubleDouble());
            return llvm::APFloat::getSmallestNormalized(llvm::APFloat::IEEEdouble());
        }();
        auto* min_norm = llvm::ConstantFP::get(ctx, min_normal);
        auto* is_ge_min_norm = builder.CreateFCmpOGE(abs_val, min_norm, "isnormal_ge_min");
        auto* is_normal = builder.CreateAnd(builder.CreateAnd(is_ord, is_not_inf), is_ge_min_norm, "isnormal");
        return {true, builder.CreateZExt(is_normal, llvm::Type::getInt32Ty(ctx), "isnormal_int")};
    }
    case BuiltinKind::ISEQSIG: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        if (lhs->getType()->isFloatingPointTy() || rhs->getType()->isFloatingPointTy()) {
            llvm::Type* fp_ty = lhs->getType()->isFloatingPointTy() ? lhs->getType() : rhs->getType();
            if (lhs->getType() != fp_ty) {
                lhs = lhs->getType()->isIntegerTy() ? builder.CreateSIToFP(lhs, fp_ty) : builder.CreateFPCast(lhs, fp_ty);
            }
            if (rhs->getType() != fp_ty) {
                rhs = rhs->getType()->isIntegerTy() ? builder.CreateSIToFP(rhs, fp_ty) : builder.CreateFPCast(rhs, fp_ty);
            }
            auto* eq = builder.CreateFCmpOEQ(lhs, rhs, "iseqsig_fp");
            return {true, builder.CreateZExt(eq, llvm::Type::getInt32Ty(ctx), "iseqsig_i32")};
        }
        if (lhs->getType() != rhs->getType()) {
            if (lhs->getType()->getIntegerBitWidth() < rhs->getType()->getIntegerBitWidth())
                lhs = builder.CreateSExt(lhs, rhs->getType());
            else
                rhs = builder.CreateSExt(rhs, lhs->getType());
        }
        auto* eq = builder.CreateICmpEQ(lhs, rhs, "iseqsig_int");
        return {true, builder.CreateZExt(eq, llvm::Type::getInt32Ty(ctx), "iseqsig_i32")};
    }
    case BuiltinKind::ISUNORDERED: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* result = builder.CreateFCmpUNO(lhs, rhs, "isunordered");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isunordered_int")};
    }
    case BuiltinKind::ISLESS: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* result = builder.CreateFCmpOLT(lhs, rhs, "isless");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isless_int")};
    }
    case BuiltinKind::ISLESSEQUAL: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* result = builder.CreateFCmpOLE(lhs, rhs, "islessequal");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "islessequal_int")};
    }
    case BuiltinKind::ISGREATER: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* result = builder.CreateFCmpOGT(lhs, rhs, "isgreater");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isgreater_int")};
    }
    case BuiltinKind::ISGREATEREQUAL: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* result = builder.CreateFCmpOGE(lhs, rhs, "isgreaterequal");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "isgreaterequal_int")};
    }
    case BuiltinKind::ISLESSGREATER: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* result = builder.CreateFCmpONE(lhs, rhs, "islessgreater");
        return {true, builder.CreateZExt(result, llvm::Type::getInt32Ty(ctx), "islessgreater_int")};
    }
    case BuiltinKind::SIGNBIT:
    case BuiltinKind::SIGNBITF:
    case BuiltinKind::SIGNBITL: {
        auto val = convert_expression(expr->args[0].get());
        llvm::Type* int_ty;
        if (val->getType()->isFloatTy()) int_ty = llvm::Type::getInt32Ty(ctx);
        else int_ty = llvm::Type::getInt64Ty(ctx);
        auto* as_int = builder.CreateBitCast(val, int_ty, "signbit_int");
        auto* zero = llvm::ConstantInt::get(int_ty, 0);
        auto* is_neg = builder.CreateICmpSLT(as_int, zero, "signbit");
        return {true, builder.CreateZExt(is_neg, llvm::Type::getInt32Ty(ctx), "signbit_result")};
    }
    // --- Float constants ---
    case BuiltinKind::BUILTIN_HUGE_VAL:
    case BuiltinKind::INF:
        return {true, llvm::ConstantFP::getInfinity(llvm::Type::getDoubleTy(ctx))};
    case BuiltinKind::BUILTIN_HUGE_VALF:
    case BuiltinKind::INFF:
        return {true, llvm::ConstantFP::getInfinity(llvm::Type::getFloatTy(ctx))};
    case BuiltinKind::BUILTIN_HUGE_VALL:
    case BuiltinKind::INFL:
        return {true, llvm::ConstantFP::getInfinity(convert_type(expr->result_type))};
    case BuiltinKind::NAN_BUILTIN:
        return {true, llvm::ConstantFP::getNaN(llvm::Type::getDoubleTy(ctx))};
    case BuiltinKind::NANF:
        return {true, llvm::ConstantFP::getNaN(llvm::Type::getFloatTy(ctx))};
    case BuiltinKind::NANL:
        return {true, llvm::ConstantFP::getNaN(convert_type(expr->result_type))};
    case BuiltinKind::NANS:
        return {true, llvm::ConstantFP::getSNaN(llvm::Type::getDoubleTy(ctx))};
    case BuiltinKind::NANSF:
        return {true, llvm::ConstantFP::getSNaN(llvm::Type::getFloatTy(ctx))};
    case BuiltinKind::NANSL:
        return {true, llvm::ConstantFP::getSNaN(convert_type(expr->result_type))};
    // --- Integer absolute value ---
    case BuiltinKind::ABS: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        val = cast_int_arg(val, BuiltinTypes::Int, src_unsigned);
        auto* zero = llvm::ConstantInt::get(val->getType(), 0);
        auto* is_neg = builder.CreateICmpSLT(val, zero, "is_neg");
        auto* neg_val = builder.CreateNeg(val, "neg");
        return {true, builder.CreateSelect(is_neg, neg_val, val, "abs")};
    }
    case BuiltinKind::LABS: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        val = cast_int_arg(val, BuiltinTypes::Long, src_unsigned);
        auto* zero = llvm::ConstantInt::get(val->getType(), 0);
        auto* is_neg = builder.CreateICmpSLT(val, zero, "is_neg");
        auto* neg_val = builder.CreateNeg(val, "neg");
        return {true, builder.CreateSelect(is_neg, neg_val, val, "labs")};
    }
    case BuiltinKind::LLABS: {
        auto val = convert_expression(expr->args[0].get());
        bool src_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        val = cast_int_arg(val, BuiltinTypes::LongLong, src_unsigned);
        auto* zero = llvm::ConstantInt::get(val->getType(), 0);
        auto* is_neg = builder.CreateICmpSLT(val, zero, "is_neg");
        auto* neg_val = builder.CreateNeg(val, "neg");
        return {true, builder.CreateSelect(is_neg, neg_val, val, "llabs")};
    }
    // --- Float math ---
    case BuiltinKind::FABS:
    case BuiltinKind::FABSF:
    case BuiltinKind::FABSL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::fabs, "fabs");
    case BuiltinKind::SQRT:
    case BuiltinKind::SQRTF:
    case BuiltinKind::SQRTL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::sqrt, "sqrt");
    case BuiltinKind::SIN:
    case BuiltinKind::SINF:
    case BuiltinKind::SINL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::sin, "sin");
    case BuiltinKind::COS:
    case BuiltinKind::COSF:
    case BuiltinKind::COSL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::cos, "cos");
    case BuiltinKind::LOG:
    case BuiltinKind::LOGF:
    case BuiltinKind::LOGL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::log, "log");
    case BuiltinKind::LOG2:
    case BuiltinKind::LOG2F:
    case BuiltinKind::LOG2L:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::log2, "log2");
    case BuiltinKind::LOG10:
    case BuiltinKind::LOG10F:
    case BuiltinKind::LOG10L:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::log10, "log10");
    case BuiltinKind::EXP:
    case BuiltinKind::EXPF:
    case BuiltinKind::EXPL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::exp, "exp");
    case BuiltinKind::EXP2:
    case BuiltinKind::EXP2F:
    case BuiltinKind::EXP2L:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::exp2, "exp2");
    case BuiltinKind::CEIL:
    case BuiltinKind::CEILF:
    case BuiltinKind::CEILL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::ceil, "ceil");
    case BuiltinKind::FLOOR:
    case BuiltinKind::FLOORF:
    case BuiltinKind::FLOORL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::floor, "floor");
    case BuiltinKind::ROUND:
    case BuiltinKind::ROUNDF:
    case BuiltinKind::ROUNDL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::round, "round");
    case BuiltinKind::TRUNC:
    case BuiltinKind::TRUNCF:
    case BuiltinKind::TRUNCL:
        return lower_unary_fp_intrinsic(llvm::Intrinsic::trunc, "trunc");
    case BuiltinKind::POW:
    case BuiltinKind::POWF:
    case BuiltinKind::POWL:
        return lower_binary_fp_intrinsic(llvm::Intrinsic::pow, "pow");
    case BuiltinKind::COPYSIGN:
    case BuiltinKind::COPYSIGNF:
    case BuiltinKind::COPYSIGNL:
        return lower_binary_fp_intrinsic(llvm::Intrinsic::copysign, "copysign");
    case BuiltinKind::FMIN:
    case BuiltinKind::FMINF:
    case BuiltinKind::FMINL:
        return lower_binary_fp_intrinsic(llvm::Intrinsic::minnum, "fmin");
    case BuiltinKind::FMAX:
    case BuiltinKind::FMAXF:
    case BuiltinKind::FMAXL:
        return lower_binary_fp_intrinsic(llvm::Intrinsic::maxnum, "fmax");
    case BuiltinKind::FMA:
    case BuiltinKind::FMAF:
    case BuiltinKind::FMAL:
        return lower_ternary_fp_intrinsic(llvm::Intrinsic::fma, "fma");
    case BuiltinKind::CBRT:
        return lower_unary_libm("cbrt", "cbrt");
    case BuiltinKind::CBRTF:
        return lower_unary_libm("cbrtf", "cbrt");
    case BuiltinKind::CBRTL:
        return lower_unary_libm("cbrtl", "cbrt");
    case BuiltinKind::TAN:
        return lower_unary_libm("tan", "tan");
    case BuiltinKind::TANF:
        return lower_unary_libm("tanf", "tan");
    case BuiltinKind::TANL:
        return lower_unary_libm("tanl", "tan");
    case BuiltinKind::ASIN:
        return lower_unary_libm("asin", "asin");
    case BuiltinKind::ASINF:
        return lower_unary_libm("asinf", "asin");
    case BuiltinKind::ASINL:
        return lower_unary_libm("asinl", "asin");
    case BuiltinKind::ACOS:
        return lower_unary_libm("acos", "acos");
    case BuiltinKind::ACOSF:
        return lower_unary_libm("acosf", "acos");
    case BuiltinKind::ACOSL:
        return lower_unary_libm("acosl", "acos");
    case BuiltinKind::ATAN:
        return lower_unary_libm("atan", "atan");
    case BuiltinKind::ATANF:
        return lower_unary_libm("atanf", "atan");
    case BuiltinKind::ATANL:
        return lower_unary_libm("atanl", "atan");
    case BuiltinKind::SINH:
        return lower_unary_libm("sinh", "sinh");
    case BuiltinKind::SINHF:
        return lower_unary_libm("sinhf", "sinh");
    case BuiltinKind::SINHL:
        return lower_unary_libm("sinhl", "sinh");
    case BuiltinKind::COSH:
        return lower_unary_libm("cosh", "cosh");
    case BuiltinKind::COSHF:
        return lower_unary_libm("coshf", "cosh");
    case BuiltinKind::COSHL:
        return lower_unary_libm("coshl", "cosh");
    case BuiltinKind::TANH:
        return lower_unary_libm("tanh", "tanh");
    case BuiltinKind::TANHF:
        return lower_unary_libm("tanhf", "tanh");
    case BuiltinKind::TANHL:
        return lower_unary_libm("tanhl", "tanh");
    case BuiltinKind::ASINH:
        return lower_unary_libm("asinh", "asinh");
    case BuiltinKind::ASINHF:
        return lower_unary_libm("asinhf", "asinh");
    case BuiltinKind::ASINHL:
        return lower_unary_libm("asinhl", "asinh");
    case BuiltinKind::ACOSH:
        return lower_unary_libm("acosh", "acosh");
    case BuiltinKind::ACOSHF:
        return lower_unary_libm("acoshf", "acosh");
    case BuiltinKind::ACOSHL:
        return lower_unary_libm("acoshl", "acosh");
    case BuiltinKind::ATANH:
        return lower_unary_libm("atanh", "atanh");
    case BuiltinKind::ATANHF:
        return lower_unary_libm("atanhf", "atanh");
    case BuiltinKind::ATANHL:
        return lower_unary_libm("atanhl", "atanh");
    case BuiltinKind::EXPM1:
        return lower_unary_libm("expm1", "expm1");
    case BuiltinKind::EXPM1F:
        return lower_unary_libm("expm1f", "expm1");
    case BuiltinKind::EXPM1L:
        return lower_unary_libm("expm1l", "expm1");
    case BuiltinKind::LOG1P:
        return lower_unary_libm("log1p", "log1p");
    case BuiltinKind::LOG1PF:
        return lower_unary_libm("log1pf", "log1p");
    case BuiltinKind::LOG1PL:
        return lower_unary_libm("log1pl", "log1p");
    case BuiltinKind::LOGB:
        return lower_unary_libm("logb", "logb");
    case BuiltinKind::LOGBF:
        return lower_unary_libm("logbf", "logb");
    case BuiltinKind::LOGBL:
        return lower_unary_libm("logbl", "logb");
    case BuiltinKind::RINT:
        return lower_unary_libm("rint", "rint");
    case BuiltinKind::RINTF:
        return lower_unary_libm("rintf", "rint");
    case BuiltinKind::RINTL:
        return lower_unary_libm("rintl", "rint");
    case BuiltinKind::NEARBYINT:
        return lower_unary_libm("nearbyint", "nearbyint");
    case BuiltinKind::NEARBYINTF:
        return lower_unary_libm("nearbyintf", "nearbyint");
    case BuiltinKind::NEARBYINTL:
        return lower_unary_libm("nearbyintl", "nearbyint");
    case BuiltinKind::ERF:
        return lower_unary_libm("erf", "erf");
    case BuiltinKind::ERFF:
        return lower_unary_libm("erff", "erf");
    case BuiltinKind::ERFL:
        return lower_unary_libm("erfl", "erf");
    case BuiltinKind::ERFC:
        return lower_unary_libm("erfc", "erfc");
    case BuiltinKind::ERFCF:
        return lower_unary_libm("erfcf", "erfc");
    case BuiltinKind::ERFCL:
        return lower_unary_libm("erfcl", "erfc");
    case BuiltinKind::LGAMMA:
        return lower_unary_libm("lgamma", "lgamma");
    case BuiltinKind::LGAMMAF:
        return lower_unary_libm("lgammaf", "lgamma");
    case BuiltinKind::LGAMMAL:
        return lower_unary_libm("lgammal", "lgamma");
    case BuiltinKind::TGAMMA:
        return lower_unary_libm("tgamma", "tgamma");
    case BuiltinKind::TGAMMAF:
        return lower_unary_libm("tgammaf", "tgamma");
    case BuiltinKind::TGAMMAL:
        return lower_unary_libm("tgammal", "tgamma");
    case BuiltinKind::ATAN2:
        return lower_binary_libm("atan2", "atan2");
    case BuiltinKind::ATAN2F:
        return lower_binary_libm("atan2f", "atan2");
    case BuiltinKind::ATAN2L:
        return lower_binary_libm("atan2l", "atan2");
    case BuiltinKind::HYPOT:
        return lower_binary_libm("hypot", "hypot");
    case BuiltinKind::HYPOTF:
        return lower_binary_libm("hypotf", "hypot");
    case BuiltinKind::HYPOTL:
        return lower_binary_libm("hypotl", "hypot");
    case BuiltinKind::FDIM:
        return lower_binary_libm("fdim", "fdim");
    case BuiltinKind::FDIMF:
        return lower_binary_libm("fdimf", "fdim");
    case BuiltinKind::FDIML:
        return lower_binary_libm("fdiml", "fdim");
    case BuiltinKind::FMOD:
        return lower_binary_libm("fmod", "fmod");
    case BuiltinKind::FMODF:
        return lower_binary_libm("fmodf", "fmod");
    case BuiltinKind::FMODL:
        return lower_binary_libm("fmodl", "fmod");
    case BuiltinKind::REMAINDER:
        return lower_binary_libm("remainder", "remainder");
    case BuiltinKind::REMAINDERF:
        return lower_binary_libm("remainderf", "remainder");
    case BuiltinKind::REMAINDERL:
        return lower_binary_libm("remainderl", "remainder");
    case BuiltinKind::NEXTAFTER:
        return lower_binary_libm("nextafter", "nextafter");
    case BuiltinKind::NEXTAFTERF:
        return lower_binary_libm("nextafterf", "nextafter");
    case BuiltinKind::NEXTAFTERL:
        return lower_binary_libm("nextafterl", "nextafter");
    case BuiltinKind::ILOGB:
    case BuiltinKind::ILOGBF:
    case BuiltinKind::ILOGBL: {
        llvm::Type* fp_ty = suffix_fp_type(expr->kind);
        auto* val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* i32_ty = llvm::Type::getInt32Ty(ctx);
        auto* ft = llvm::FunctionType::get(i32_ty, {fp_ty}, false);
        const char* name = expr->kind == BuiltinKind::ILOGBF
            ? "ilogbf"
            : (expr->kind == BuiltinKind::ILOGBL ? "ilogbl" : "ilogb");
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {val}, "ilogb")};
    }
    case BuiltinKind::LRINT:
    case BuiltinKind::LRINTF:
    case BuiltinKind::LRINTL:
    case BuiltinKind::LROUND:
    case BuiltinKind::LROUNDF:
    case BuiltinKind::LROUNDL:
    case BuiltinKind::LLRINT:
    case BuiltinKind::LLRINTF:
    case BuiltinKind::LLRINTL:
    case BuiltinKind::LLROUND:
    case BuiltinKind::LLROUNDF:
    case BuiltinKind::LLROUNDL: {
        llvm::Type* fp_ty = suffix_fp_type(expr->kind);
        auto* val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        llvm::Type* result_ty = convert_type(expr->result_type);
        auto* ft = llvm::FunctionType::get(result_ty, {fp_ty}, false);
        const char* name = nullptr;
        switch (expr->kind) {
            case BuiltinKind::LRINT: name = "lrint"; break;
            case BuiltinKind::LRINTF: name = "lrintf"; break;
            case BuiltinKind::LRINTL: name = "lrintl"; break;
            case BuiltinKind::LROUND: name = "lround"; break;
            case BuiltinKind::LROUNDF: name = "lroundf"; break;
            case BuiltinKind::LROUNDL: name = "lroundl"; break;
            case BuiltinKind::LLRINT: name = "llrint"; break;
            case BuiltinKind::LLRINTF: name = "llrintf"; break;
            case BuiltinKind::LLRINTL: name = "llrintl"; break;
            case BuiltinKind::LLROUND: name = "llround"; break;
            case BuiltinKind::LLROUNDF: name = "llroundf"; break;
            case BuiltinKind::LLROUNDL: name = "llroundl"; break;
            default: name = "lrint"; break;
        }
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {val}, name)};
    }
    case BuiltinKind::MODF: case BuiltinKind::MODFF: case BuiltinKind::MODFL: {
        llvm::Type* fp_ty = result_fp_type();
        auto* val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto iptr = convert_expression(expr->args[1].get());
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(fp_ty, {fp_ty, ptr_ty}, false);
        const char* name = expr->kind == BuiltinKind::MODFF
            ? "modff"
            : (expr->kind == BuiltinKind::MODFL ? "modfl" : "modf");
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {val, iptr}, name)};
    }
    case BuiltinKind::REMQUO:
    case BuiltinKind::REMQUOF:
    case BuiltinKind::REMQUOL: {
        llvm::Type* fp_ty = result_fp_type();
        auto* lhs = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* rhs = coerce_builtin_fp_expr_arg(expr->args[1].get(), fp_ty);
        auto* quo_ptr = convert_expression(expr->args[2].get());
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(fp_ty, {fp_ty, fp_ty, ptr_ty}, false);
        const char* name = expr->kind == BuiltinKind::REMQUOF
            ? "remquof"
            : (expr->kind == BuiltinKind::REMQUOL ? "remquol" : "remquo");
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {lhs, rhs, quo_ptr}, "remquo")};
    }
    case BuiltinKind::NEXTTOWARD:
    case BuiltinKind::NEXTTOWARDF:
    case BuiltinKind::NEXTTOWARDL: {
        llvm::Type* fp_ty = result_fp_type();
        llvm::Type* long_double_ty = builtin_llvm_type(BuiltinTypes::LongDouble);
        auto* from = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto* to = coerce_builtin_fp_expr_arg(expr->args[1].get(), long_double_ty);
        auto* ft = llvm::FunctionType::get(fp_ty, {fp_ty, long_double_ty}, false);
        const char* name = expr->kind == BuiltinKind::NEXTTOWARDF
            ? "nexttowardf"
            : (expr->kind == BuiltinKind::NEXTTOWARDL ? "nexttowardl" : "nexttoward");
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {from, to}, "nexttoward")};
    }
    case BuiltinKind::FREXP:
    case BuiltinKind::FREXPF:
    case BuiltinKind::FREXPL: {
        llvm::Type* fp_ty = result_fp_type();
        auto* val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto exp_ptr = convert_expression(expr->args[1].get());
        auto* ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* ft = llvm::FunctionType::get(fp_ty, {fp_ty, ptr_ty}, false);
        const char* name = expr->kind == BuiltinKind::FREXPF
            ? "frexpf"
            : (expr->kind == BuiltinKind::FREXPL ? "frexpl" : "frexp");
        auto callee = get_or_declare_libc_func(module.get(), ctx, name, ft);
        return {true, builder.CreateCall(callee, {val, exp_ptr}, name)};
    }
    case BuiltinKind::LDEXP:
    case BuiltinKind::LDEXPF:
    case BuiltinKind::LDEXPL:
    case BuiltinKind::SCALBN:
    case BuiltinKind::SCALBNF:
    case BuiltinKind::SCALBNL:
    case BuiltinKind::SCALBLN:
    case BuiltinKind::SCALBLNF:
    case BuiltinKind::SCALBLNL: {
        llvm::Type* fp_ty = result_fp_type();
        auto val = coerce_builtin_fp_expr_arg(expr->args[0].get(), fp_ty);
        auto exp = convert_expression(expr->args[1].get());

        bool exponent_is_long =
            expr->kind == BuiltinKind::SCALBLN ||
            expr->kind == BuiltinKind::SCALBLNF ||
            expr->kind == BuiltinKind::SCALBLNL;
        exp = cast_int_arg(
            exp,
            exponent_is_long ? BuiltinTypes::Long : BuiltinTypes::Int,
            /*src_unsigned=*/false);

        llvm::Intrinsic::ID intrinsic_id = llvm::Intrinsic::ldexp;
        auto* fn = llvm::Intrinsic::getDeclaration(
            module.get(),
            intrinsic_id,
            {fp_ty, exp->getType()});
        return {true, builder.CreateCall(fn, {val, exp}, "ldexp")};
    }
    default:
        return {};
    }
}

// ── Complex builtins: conjf, __builtin_complex, cpow, cexpi ─────────────────
static BuiltinLoweringResult lower_builtin_complex_group(
    ASTToLLVM& lower, BuiltinCallExpr* expr) {
    auto& builder = lower.builder;
    auto& module = lower.module;
    auto& ctx = *lower.context;
    auto convert_expression = [&](Expr* e) { return lower.convert_expression(e); };
    auto convert_type = [&](auto t) { return lower.convert_type(t); };

    switch (expr->kind) {
    case BuiltinKind::CONJF: {
        auto val = convert_expression(expr->args[0].get());
        auto* agg_ty = llvm::dyn_cast<llvm::StructType>(val->getType());
        if (!agg_ty || agg_ty->getNumElements() != 2) {
            lower.error("__builtin_conjf expects complex aggregate argument", expr->location);
            return {true, nullptr};
        }
        auto* real = builder.CreateExtractValue(val, {0}, "conjf.real");
        auto* imag = builder.CreateExtractValue(val, {1}, "conjf.imag");
        auto* neg_imag = imag->getType()->isFloatingPointTy()
            ? static_cast<llvm::Value*>(builder.CreateFNeg(imag, "conjf.imag.neg"))
            : static_cast<llvm::Value*>(builder.CreateNeg(imag, "conjf.imag.neg"));
        llvm::Value* result = llvm::UndefValue::get(agg_ty);
        result = builder.CreateInsertValue(result, real, {0}, "conjf.set.real");
        result = builder.CreateInsertValue(result, neg_imag, {1}, "conjf.set.imag");
        return {true, result};
    }
    case BuiltinKind::COMPLEX: {
        auto* ret_ty = llvm::dyn_cast<llvm::StructType>(convert_type(expr->result_type));
        auto complex_ty =
            desugar_type(expr->result_type, lower.ast_ctx.get()).as_shared<ComplexType>();
        if (!ret_ty || ret_ty->getNumElements() != 2 || !complex_ty) {
            lower.error("__builtin_complex expects complex return type", expr->location);
            return {true, nullptr};
        }
        llvm::Type* elem_ty = ret_ty->getElementType(0);
        bool target_unsigned = false;
        if (auto elem_builtin = complex_ty->element_type) {
            target_unsigned = elem_builtin->isUnsigned();
        }
        auto coerce_component = [&](llvm::Value* val, const QualType& src_type) -> llvm::Value* {
            if (val->getType() == elem_ty) return val;
            if (elem_ty->isFloatingPointTy()) {
                if (val->getType()->isFloatingPointTy()) return builder.CreateFPCast(val, elem_ty);
                if (val->getType()->isIntegerTy()) {
                    bool src_unsigned = false;
                    if (auto src_builtin = src_type.as_shared<BuiltinType>()) src_unsigned = src_builtin->isUnsigned();
                    return src_unsigned ? builder.CreateUIToFP(val, elem_ty) : builder.CreateSIToFP(val, elem_ty);
                }
            } else if (elem_ty->isIntegerTy()) {
                if (val->getType()->isFloatingPointTy())
                    return target_unsigned ? builder.CreateFPToUI(val, elem_ty) : builder.CreateFPToSI(val, elem_ty);
                if (val->getType()->isIntegerTy()) {
                    bool src_unsigned = false;
                    if (auto src_builtin = src_type.as_shared<BuiltinType>()) src_unsigned = src_builtin->isUnsigned();
                    return builder.CreateIntCast(val, elem_ty, !src_unsigned);
                }
            }
            return val;
        };
        auto real_val = convert_expression(expr->args[0].get());
        auto imag_val = convert_expression(expr->args[1].get());
        real_val = coerce_component(real_val, expr->args[0]->get_type());
        imag_val = coerce_component(imag_val, expr->args[1]->get_type());
        llvm::Value* result = llvm::UndefValue::get(ret_ty);
        result = builder.CreateInsertValue(result, real_val, {0}, "complex.set.real");
        result = builder.CreateInsertValue(result, imag_val, {1}, "complex.set.imag");
        return {true, result};
    }
    case BuiltinKind::CPOW: {
        auto lhs = convert_expression(expr->args[0].get());
        auto rhs = convert_expression(expr->args[1].get());
        auto* ret_ty = llvm::dyn_cast<llvm::StructType>(convert_type(expr->result_type));
        auto complex_ty =
            desugar_type(expr->result_type, lower.ast_ctx.get()).as_shared<ComplexType>();
        if (!ret_ty || ret_ty->getNumElements() != 2 || !complex_ty) {
            lower.error("__builtin_cpow expects complex return type", expr->location);
            return {true, nullptr};
        }
        llvm::Type* elem_ty = ret_ty->getElementType(0);
        auto build_complex_from_scalar = [&](llvm::Value* scalar, const QualType& scalar_qt) -> llvm::Value* {
            llvm::Value* real = scalar;
            if (real->getType() != elem_ty) {
                if (real->getType()->isFloatingPointTy()) {
                    real = builder.CreateFPCast(real, elem_ty, "cpow.real.cast");
                } else if (real->getType()->isIntegerTy()) {
                    bool src_unsigned = scalar_qt && scalar_qt->isUnsigned();
                    real = src_unsigned
                        ? static_cast<llvm::Value*>(builder.CreateUIToFP(real, elem_ty, "cpow.real.ui2fp"))
                        : static_cast<llvm::Value*>(builder.CreateSIToFP(real, elem_ty, "cpow.real.si2fp"));
                }
            }
            llvm::Value* imag = llvm::ConstantFP::get(elem_ty, 0.0);
            llvm::Value* z = llvm::UndefValue::get(ret_ty);
            z = builder.CreateInsertValue(z, real, {0}, "cpow.scalar.real");
            z = builder.CreateInsertValue(z, imag, {1}, "cpow.scalar.imag");
            return z;
        };
        auto cast_complex = [&](llvm::Value* value, const QualType& value_qt) -> llvm::Value* {
            if (value->getType() == ret_ty) return value;
            auto value_complex = desugar_type(value_qt, lower.ast_ctx.get()).as_shared<ComplexType>();
            if (!value_complex) return build_complex_from_scalar(value, value_qt);
            auto* src_struct = llvm::dyn_cast<llvm::StructType>(value->getType());
            if (!src_struct || src_struct->getNumElements() != 2) return build_complex_from_scalar(value, value_qt);
            auto* src_real = builder.CreateExtractValue(value, {0}, "cpow.src.real");
            auto* src_imag = builder.CreateExtractValue(value, {1}, "cpow.src.imag");
            if (src_real->getType() != elem_ty) src_real = builder.CreateFPCast(src_real, elem_ty, "cpow.src.real.cast");
            if (src_imag->getType() != elem_ty) src_imag = builder.CreateFPCast(src_imag, elem_ty, "cpow.src.imag.cast");
            llvm::Value* z = llvm::UndefValue::get(ret_ty);
            z = builder.CreateInsertValue(z, src_real, {0}, "cpow.arg.real");
            z = builder.CreateInsertValue(z, src_imag, {1}, "cpow.arg.imag");
            return z;
        };
        lhs = cast_complex(lhs, expr->args[0]->get_type());
        rhs = cast_complex(rhs, expr->args[1]->get_type());
        auto* ft = llvm::FunctionType::get(ret_ty, {ret_ty, ret_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "cpow", ft);
        return {true, builder.CreateCall(callee, {lhs, rhs}, "cpow")};
    }
    case BuiltinKind::CEXPI: {
        auto angle = convert_expression(expr->args[0].get());
        if (!angle->getType()->isFloatingPointTy())
            angle = builder.CreateSIToFP(angle, llvm::Type::getDoubleTy(ctx), "cexpi.tofp");
        else if (!angle->getType()->isDoubleTy())
            angle = builder.CreateFPCast(angle, llvm::Type::getDoubleTy(ctx), "cexpi.cast");
        auto* sin_fn = llvm::Intrinsic::getDeclaration(module.get(), llvm::Intrinsic::sin, {angle->getType()});
        auto* cos_fn = llvm::Intrinsic::getDeclaration(module.get(), llvm::Intrinsic::cos, {angle->getType()});
        auto* real = builder.CreateCall(cos_fn, {angle}, "cexpi.real");
        auto* imag = builder.CreateCall(sin_fn, {angle}, "cexpi.imag");
        auto* ret_ty = llvm::dyn_cast<llvm::StructType>(convert_type(expr->result_type));
        if (!ret_ty || ret_ty->getNumElements() != 2) {
            lower.error("__builtin_cexpi expects complex return type", expr->location);
            return {true, nullptr};
        }
        llvm::Value* result = llvm::UndefValue::get(ret_ty);
        result = builder.CreateInsertValue(result, real, {0}, "cexpi.set.real");
        result = builder.CreateInsertValue(result, imag, {1}, "cexpi.set.imag");
        return {true, result};
    }
    default:
        return {};
    }
}

llvm::Value* ASTToLLVM::convert_builtin_call_expr(BuiltinCallExpr *expr) {
    auto& ctx = *context;

    // Dispatch self-contained builtin families first; fall through to the
    // remaining-cases switch for core/misc builtins.
    if (auto lowered = lower_builtin_memory_and_stack_group(*this, expr);
        lowered.handled) {
        return lowered.value;
    }
    if (auto lowered = lower_builtin_atomic_and_sync_group(*this, expr);
        lowered.handled) {
        return lowered.value;
    }
    if (auto lowered = lower_builtin_io_group(*this, expr);
        lowered.handled) {
        return lowered.value;
    }
    if (auto lowered = lower_builtin_bit_group(*this, expr);
        lowered.handled) {
        return lowered.value;
    }
    if (auto lowered = lower_builtin_math_group(*this, expr);
        lowered.handled) {
        return lowered.value;
    }
    if (auto lowered = lower_builtin_complex_group(*this, expr);
        lowered.handled) {
        return lowered.value;
    }

    switch (expr->kind) {
    // ========== Tier 1: Critical kernel builtins ==========
    case BuiltinKind::EXPECT:
    case BuiltinKind::EXPECT_WITH_PROBABILITY: {
        // __builtin_expect(expr, val) -> return expr (optionally emit llvm.expect)
        auto val = convert_expression(expr->args[0].get());
        auto expected = convert_expression(expr->args[1].get());
        auto* int_type = llvm::dyn_cast<llvm::IntegerType>(val->getType());
        if (int_type) {
            llvm::Function* expect_fn = llvm::Intrinsic::getDeclaration(
                module.get(), llvm::Intrinsic::expect, {int_type});
            return builder.CreateCall(expect_fn, {val, expected}, "expect");
        }
        return val;
    }
    case BuiltinKind::CONSTANT_P: {
        // __builtin_constant_p(expr) -> compile-time constant check
        return lower_builtin_const_integer(
            *this, expr, expr->const_value.value_or(0));
    }
    case BuiltinKind::IS_CONSTANT_EVALUATED: {
        return llvm::ConstantInt::getFalse(llvm::Type::getInt1Ty(ctx));
    }
    case BuiltinKind::AVAILABLE: {
        // Compatibility behavior: treat __builtin_available(...) as always true.
        return llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), 1);
    }
    case BuiltinKind::VA_ARG_PACK: {
        // TODO(gcc-torture): Implement real vararg-pack forwarding semantics.
        // Current behavior is a compile-compatibility fallback only.
        // Fallback for compile-compatibility when used in variadic forwarding contexts.
        return llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), 0);
    }
    case BuiltinKind::UNREACHABLE: {
        builder.CreateUnreachable();
        // Create a new unreachable block so subsequent code can still be generated
        auto* func = builder.GetInsertBlock()->getParent();
        auto* unreachable_bb = llvm::BasicBlock::Create(ctx, "unreachable", func);
        builder.SetInsertPoint(unreachable_bb);
        return llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx));
    }
    case BuiltinKind::TRAP: {
        llvm::Function* trap_fn = llvm::Intrinsic::getDeclaration(
            module.get(), llvm::Intrinsic::trap);
        builder.CreateCall(trap_fn);
        builder.CreateUnreachable();
        auto* func = builder.GetInsertBlock()->getParent();
        auto* after_trap = llvm::BasicBlock::Create(ctx, "after_trap", func);
        builder.SetInsertPoint(after_trap);
        return llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx));
    }
    case BuiltinKind::ABORT: {
        // __builtin_abort() -> call abort(), then unreachable
        auto* abort_ty = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx), false);
        auto abort_fn = module->getOrInsertFunction("abort", abort_ty);
        builder.CreateCall(abort_fn);
        builder.CreateUnreachable();
        auto* func = builder.GetInsertBlock()->getParent();
        auto* after_abort = llvm::BasicBlock::Create(ctx, "after_abort", func);
        builder.SetInsertPoint(after_abort);
        return llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx));
    }
    case BuiltinKind::EXIT: {
        // __builtin_exit(int status) -> call exit(status), then unreachable
        llvm::Value* status_val = convert_expression(expr->args[0].get());
        auto* exit_ty = llvm::FunctionType::get(
            llvm::Type::getVoidTy(ctx), {llvm::Type::getInt32Ty(ctx)}, false);
        auto exit_fn = module->getOrInsertFunction("exit", exit_ty);
        builder.CreateCall(exit_fn, {status_val});
        builder.CreateUnreachable();
        auto* func = builder.GetInsertBlock()->getParent();
        auto* after_exit = llvm::BasicBlock::Create(ctx, "after_exit", func);
        builder.SetInsertPoint(after_exit);
        return llvm::Constant::getNullValue(llvm::Type::getVoidTy(ctx));
    }
    case BuiltinKind::MALLOC: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "malloc", ft);
        auto size = convert_expression(expr->args[0].get());
        if (size->getType() != i64_ty) size = builder.CreateIntCast(size, i64_ty, false);
        return builder.CreateCall(callee, {size}, "malloc");
    }
    case BuiltinKind::CALLOC: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i64_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "calloc", ft);
        auto count = convert_expression(expr->args[0].get());
        auto size = convert_expression(expr->args[1].get());
        if (count->getType() != i64_ty) count = builder.CreateIntCast(count, i64_ty, false);
        if (size->getType() != i64_ty) size = builder.CreateIntCast(size, i64_ty, false);
        return builder.CreateCall(callee, {count, size}, "calloc");
    }
    case BuiltinKind::REALLOC: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* i64_ty = llvm::Type::getInt64Ty(ctx);
        auto* ft = llvm::FunctionType::get(i8_ptr_ty, {i8_ptr_ty, i64_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "realloc", ft);
        auto ptr = convert_expression(expr->args[0].get());
        auto size = convert_expression(expr->args[1].get());
        if (size->getType() != i64_ty) size = builder.CreateIntCast(size, i64_ty, false);
        return builder.CreateCall(callee, {ptr, size}, "realloc");
    }
    case BuiltinKind::FREE: {
        auto* i8_ptr_ty = llvm::PointerType::getUnqual(ctx);
        auto* void_ty = llvm::Type::getVoidTy(ctx);
        auto* ft = llvm::FunctionType::get(void_ty, {i8_ptr_ty}, false);
        auto callee = get_or_declare_libc_func(module.get(), ctx, "free", ft);
        auto ptr = convert_expression(expr->args[0].get());
        builder.CreateCall(callee, {ptr});
        return llvm::Constant::getNullValue(void_ty);
    }
    case BuiltinKind::TYPES_COMPATIBLE_P: {
        // Compile-time constant, evaluated in sema
        return lower_builtin_const_integer(
            *this, expr, expr->const_value.value_or(0));
    }
    case BuiltinKind::IS_SAME:
    case BuiltinKind::IS_FUNCTION:
    case BuiltinKind::IS_REFERENCE:
    case BuiltinKind::IS_LVALUE_REFERENCE:
    case BuiltinKind::IS_RVALUE_REFERENCE:
    case BuiltinKind::IS_INTEGRAL:
    case BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS:
    case BuiltinKind::IS_DESTRUCTIBLE:
    case BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE:
    case BuiltinKind::HAS_TRIVIAL_DESTRUCTOR:
        return lower_builtin_const_integer(
            *this, expr, expr->const_value.value_or(0));
    case BuiltinKind::CHOOSE_EXPR: {
        // Sema should have already replaced this with the chosen expression
        // but if we get here, evaluate the chosen expression
        if (expr->const_value.has_value()) {
            int64_t choice = *expr->const_value;
            if (choice != 0) {
                return convert_expression(expr->args[0].get());
            } else {
                return convert_expression(expr->args[1].get());
            }
        }
        return convert_expression(expr->args[0].get());
    }
    case BuiltinKind::CONVERTVECTOR: {
        if (expr->args.size() != 1 || expr->type_args.size() != 1) {
            error("__builtin_convertvector expects one expression and one type argument", expr->location);
            return nullptr;
        }
        auto source_val = convert_expression(expr->args[0].get());
        auto source_vec_type =
            desugar_type(expr->args[0]->get_type(), ast_ctx.get()).as_shared<VectorType>();
        auto target_vec_type =
            desugar_type(expr->type_args[0], ast_ctx.get()).as_shared<VectorType>();
        if (!source_vec_type || !target_vec_type) {
            error("__builtin_convertvector requires vector source and vector destination type", expr->location);
            return nullptr;
        }
        if (source_vec_type->num_elements != target_vec_type->num_elements) {
            error("__builtin_convertvector source and destination vectors must have the same number of elements", expr->location);
            return nullptr;
        }
        auto* target_llvm_type = llvm::dyn_cast<llvm::FixedVectorType>(convert_type(expr->type_args[0]));
        if (!target_llvm_type || !source_val->getType()->isVectorTy()) {
            error("__builtin_convertvector requires fixed vector LLVM types", expr->location);
            return nullptr;
        }
        llvm::Type* target_elem_type = target_llvm_type->getElementType();
        llvm::Value* converted = llvm::PoisonValue::get(target_llvm_type);
        for (unsigned i = 0; i < target_llvm_type->getNumElements(); ++i) {
            llvm::Value* index = llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), i);
            llvm::Value* elem = builder.CreateExtractElement(source_val, index, "convvec.elem");
            llvm::Value* cast_elem = cast_llvm_type(elem, target_elem_type, source_vec_type->element_type->isUnsigned());
            converted = builder.CreateInsertElement(converted, cast_elem, index, "convvec.ins");
        }
        return converted;
    }
    case BuiltinKind::SHUFFLEVECTOR: {
        // TODO(gcc-torture): Implement full __builtin_shufflevector lane-mask semantics.
        // Current behavior is a conservative compile/runtime fallback.
        // Conservative lowering: preserve argument evaluation and return the
        // first vector argument when available.
        if (expr->args.empty()) {
            error("__builtin_shufflevector expects at least one argument", expr->location);
            return nullptr;
        }
        llvm::Value* primary = nullptr;
        for (size_t i = 0; i < expr->args.size(); ++i) {
            llvm::Value* value = convert_expression(expr->args[i].get());
            if (!primary && value && value->getType()->isVectorTy()) {
                primary = value;
            }
        }
        if (!primary) {
            error("__builtin_shufflevector requires at least one vector argument", expr->location);
            return nullptr;
        }
        return primary;
    }
    case BuiltinKind::OBJECT_SIZE:
    case BuiltinKind::DYNAMIC_OBJECT_SIZE: {
        // Conservative: return (size_t)-1 for type 0/1, 0 for type 2/3
        auto type_val = eval_constexpr_i64(expr->args[1].get(), ConstEvalMode::builtin_query());
        int64_t type_int = type_val.value_or(0);
        auto* size_type = llvm::Type::getInt64Ty(ctx);
        if (type_int >= 2) {
            return llvm::ConstantInt::get(size_type, 0);
        }
        return llvm::ConstantInt::get(size_type, (uint64_t)-1, false);
    }

    // ========== Tier 2: Overflow builtins ==========
    case BuiltinKind::ADD_OVERFLOW:
    case BuiltinKind::SUB_OVERFLOW:
    case BuiltinKind::MUL_OVERFLOW: {
        auto a_val = convert_expression(expr->args[0].get());
        auto b_val = convert_expression(expr->args[1].get());
        // Third arg is a pointer expression (e.g. &result)
        auto res_ptr = convert_expression(expr->args[2].get());
        auto res_ptr_ctype = expr->args[2]->get_type();
        auto* pointed_type = dyn_cast<PointerType>(res_ptr_ctype.get());
        if (!pointed_type) {
            error("overflow builtin: third arg must be a pointer", expr->location);
            return nullptr;
        }
        auto result_llvm_type = convert_type(pointed_type->pointed_type);
        auto* result_int_type = llvm::dyn_cast<llvm::IntegerType>(result_llvm_type);
        auto* a_int_type = llvm::dyn_cast<llvm::IntegerType>(a_val->getType());
        auto* b_int_type = llvm::dyn_cast<llvm::IntegerType>(b_val->getType());
        if (!result_int_type || !a_int_type || !b_int_type) {
            error("overflow builtin requires integer operands", expr->location);
            return nullptr;
        }

        unsigned a_bits = a_int_type->getBitWidth();
        unsigned b_bits = b_int_type->getBitWidth();
        unsigned result_bits = result_int_type->getBitWidth();
        unsigned wide_bits = result_bits + 1;
        wide_bits = std::max(wide_bits, a_bits + 1);
        wide_bits = std::max(wide_bits, b_bits + 1);
        if (expr->kind == BuiltinKind::MUL_OVERFLOW) {
            wide_bits = std::max(wide_bits, a_bits + b_bits + 1);
        } else {
            wide_bits = std::max(wide_bits, std::max(a_bits, b_bits) + 2);
        }
        auto* wide_type = llvm::IntegerType::get(ctx, wide_bits);

        bool a_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        bool b_unsigned = expr->args[1]->get_type() && expr->args[1]->get_type()->isUnsigned();
        bool result_unsigned = pointed_type->pointed_type->isUnsigned();

        llvm::Value* a_wide = cast_llvm_type(a_val, wide_type, a_unsigned);
        llvm::Value* b_wide = cast_llvm_type(b_val, wide_type, b_unsigned);

        llvm::Value* wide_result = nullptr;
        if (expr->kind == BuiltinKind::ADD_OVERFLOW) {
            wide_result = builder.CreateAdd(a_wide, b_wide, "overflow_add");
        } else if (expr->kind == BuiltinKind::SUB_OVERFLOW) {
            wide_result = builder.CreateSub(a_wide, b_wide, "overflow_sub");
        } else {
            wide_result = builder.CreateMul(a_wide, b_wide, "overflow_mul");
        }

        llvm::Value* result_val = wide_result;
        if (result_val->getType() != result_llvm_type) {
            result_val = builder.CreateTrunc(result_val, result_llvm_type, "overflow_result");
        }
        llvm::Value* roundtrip = cast_llvm_type(result_val, wide_type, result_unsigned);
        llvm::Value* overflow_bit = builder.CreateICmpNE(wide_result, roundtrip, "overflow_bit");
        builder.CreateStore(result_val, res_ptr);
        // Return _Bool (i1 -> i32 via zext)
        return builder.CreateZExt(overflow_bit, llvm::Type::getInt32Ty(ctx), "overflow_int");
    }
    case BuiltinKind::ADD_OVERFLOW_P:
    case BuiltinKind::SUB_OVERFLOW_P: {
        auto a_val = convert_expression(expr->args[0].get());
        auto b_val = convert_expression(expr->args[1].get());
        // Third arg determines the type but the result is discarded
        auto result_type = convert_type(expr->args[2]->get_type());
        auto* result_int_type = llvm::dyn_cast<llvm::IntegerType>(result_type);
        auto* a_int_type = llvm::dyn_cast<llvm::IntegerType>(a_val->getType());
        auto* b_int_type = llvm::dyn_cast<llvm::IntegerType>(b_val->getType());
        if (!result_int_type || !a_int_type || !b_int_type) {
            error("overflow builtin requires integer operands", expr->location);
            return nullptr;
        }
        unsigned a_bits = a_int_type->getBitWidth();
        unsigned b_bits = b_int_type->getBitWidth();
        unsigned result_bits = result_int_type->getBitWidth();
        unsigned wide_bits = std::max({result_bits + 1, a_bits + 1, b_bits + 1, std::max(a_bits, b_bits) + 2});
        auto* wide_type = llvm::IntegerType::get(ctx, wide_bits);

        bool a_unsigned = expr->args[0]->get_type() && expr->args[0]->get_type()->isUnsigned();
        bool b_unsigned = expr->args[1]->get_type() && expr->args[1]->get_type()->isUnsigned();
        bool result_unsigned = expr->args[2]->get_type() && expr->args[2]->get_type()->isUnsigned();

        llvm::Value* a_wide = cast_llvm_type(a_val, wide_type, a_unsigned);
        llvm::Value* b_wide = cast_llvm_type(b_val, wide_type, b_unsigned);
        llvm::Value* wide_result = expr->kind == BuiltinKind::SUB_OVERFLOW_P
            ? builder.CreateSub(a_wide, b_wide, "overflow_p_sub")
            : builder.CreateAdd(a_wide, b_wide, "overflow_p_add");
        llvm::Value* result_val = wide_result;
        if (result_val->getType() != result_type) {
            result_val = builder.CreateTrunc(result_val, result_type, "overflow_p_result");
        }
        llvm::Value* roundtrip = cast_llvm_type(result_val, wide_type, result_unsigned);
        llvm::Value* overflow_bit = builder.CreateICmpNE(wide_result, roundtrip, "overflow_p_bit");
        return builder.CreateZExt(overflow_bit, llvm::Type::getInt32Ty(ctx), "overflow_p_int");
    }

    // ========== Tier 3: Misc builtins ==========
    case BuiltinKind::ASSUME_ALIGNED: {
        // Return the pointer (ignore alignment hint for now)
        return convert_expression(expr->args[0].get());
    }
    case BuiltinKind::CLASSIFY_TYPE: {
        // Compile-time constant evaluated in sema
        return lower_builtin_const_integer(
            *this, expr, expr->const_value.value_or(0));
    }
    case BuiltinKind::BUILTIN_FILE: {
        // Compile-time constant: emit as string literal
        // const_value not used; emit a global string
        // For now, emit empty string if sema didn't provide a StringLiteral arg
        if (!expr->args.empty()) {
            return convert_expression(expr->args[0].get());
        }
        return builder.CreateGlobalStringPtr("", "builtin_file");
    }
    case BuiltinKind::BUILTIN_LINE: {
        return lower_builtin_const_integer(
            *this, expr, expr->const_value.value_or(0));
    }
    case BuiltinKind::BUILTIN_FUNCTION: {
        if (!expr->args.empty()) {
            return convert_expression(expr->args[0].get());
        }
        return builder.CreateGlobalStringPtr("", "builtin_func");
    }
    default:
        break;
    }

    error("unimplemented builtin in convert_builtin_call_expr", expr->location);
    return nullptr;
}
