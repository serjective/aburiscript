#include "ast2llvm.h"
#include "const_lowering.h"
#include "../abi/darwin_blocks.h"
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
#include <limits>
#include <optional>
#include <unordered_set>
#include "lower_helpers.h"

namespace {

std::string block_helper_symbol_suffix(const BlockExpr* expr) {
    if (!expr) {
        return "invalid";
    }
    if (expr->node_id != 0) {
        return std::to_string(expr->node_id);
    }
    if (!expr->location.isInvalid()) {
        return std::to_string(expr->location.offset);
    }
    return "invalid";
}

llvm::GlobalVariable* get_or_create_darwin_block_runtime_class(
    ASTToLLVM& lower,
    darwin_blocks::ConcreteBlockStorageClass storage) {
    std::string symbol_name(
        darwin_blocks::runtime_class_symbol(storage));
    if (auto* existing = lower.module->getGlobalVariable(symbol_name, true)) {
        return existing;
    }
    return new llvm::GlobalVariable(
        *lower.module,
        llvm::Type::getInt8Ty(*lower.context),
        false,
        llvm::GlobalValue::ExternalLinkage,
        nullptr,
        symbol_name);
}

llvm::Function* get_or_create_block_invoke_declaration(ASTToLLVM& lower,
                                                       BlockExpr* expr) {
    if (!expr || !expr->semantic_info.invoke_decl) {
        lower.error("convert_block_expression(): missing synthesized block invoke declaration",
                    expr ? expr->location : SrcLoc());
        return nullptr;
    }

    auto* invoke_decl = expr->semantic_info.invoke_decl.get();
    std::string invoke_name = lower.get_function_llvm_name(*invoke_decl);
    if (auto* existing = lower.module->getFunction(invoke_name)) {
        return existing;
    }

    auto invoke_type =
        desugar_type(QualType(invoke_decl->type), lower.ast_ctx.get())
            .as_shared<FunctionType>();
    if (!invoke_type) {
        lower.error("convert_block_expression(): invalid block invoke type",
                    expr->location);
        return nullptr;
    }

    std::vector<llvm::Type*> param_types;
    param_types.reserve(invoke_decl->parameters.size());
    for (const auto& param_decl_base : invoke_decl->parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(param_decl_base.get());
        if (!param_decl || (param_decl->type && param_decl->type->isVoid())) {
            continue;
        }
        param_types.push_back(lower.convert_param_type(param_decl->type));
    }

    llvm::Type* return_type = lower.convert_type(invoke_type->ret_type);
    auto* llvm_function_type = llvm::FunctionType::get(
        return_type,
        param_types,
        invoke_type->is_variadic);
    auto* function = llvm::Function::Create(
        llvm_function_type,
        llvm::Function::InternalLinkage,
        invoke_name,
        lower.module.get());
    if (invoke_type->exception_spec ==
        FunctionExceptionSpecKind::NonThrowing) {
        function->addFnAttr(llvm::Attribute::NoUnwind);
    }

    if (lower.deferred_inline_set.insert(invoke_decl).second) {
        lower.deferred_inline_defs.push_back(invoke_decl);
    }
    return function;
}

bool block_literal_needs_copy_dispose(const BlockExpr* expr) {
    if (!expr) {
        return false;
    }
    for (const auto& capture : expr->semantic_info.captures) {
        if (capture.kind == BlockCaptureKind::ByRef) {
            return true;
        }
        QualType canonical = desugar_type(capture.capture_type);
        if (canonical && canonical->kind == TypeKind::BlockPointer) {
            return true;
        }
    }
    return false;
}

std::optional<uint32_t> block_capture_copy_dispose_flags(
    const BlockCapture& capture) {
    if (capture.kind == BlockCaptureKind::ByRef) {
        return darwin_blocks::BLOCK_FIELD_IS_BYREF;
    }

    QualType canonical = desugar_type(capture.capture_type);
    if (canonical && canonical->kind == TypeKind::BlockPointer) {
        return darwin_blocks::BLOCK_FIELD_IS_BLOCK;
    }

    return std::nullopt;
}

llvm::Function* get_or_create_block_copy_helper(ASTToLLVM& lower,
                                                BlockExpr* expr,
                                                llvm::StructType* literal_type) {
    if (!expr || !literal_type || !block_literal_needs_copy_dispose(expr)) {
        return nullptr;
    }

    std::string name =
        "__block_copy_helper_" + block_helper_symbol_suffix(expr);
    if (auto* existing = lower.module->getFunction(name)) {
        return existing;
    }

    llvm::Type* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*lower.context),
        {ptr_ty, ptr_ty},
        false);
    auto* fn = llvm::Function::Create(
        fn_ty,
        llvm::Function::InternalLinkage,
        name,
        lower.module.get());

    llvm::IRBuilderBase::InsertPointGuard guard(lower.builder);
    auto* entry_bb = llvm::BasicBlock::Create(*lower.context, "entry", fn);
    lower.builder.SetInsertPoint(entry_bb);

    auto arg_it = fn->arg_begin();
    llvm::Value* dst_ptr = &*arg_it++;
    llvm::Value* src_ptr = &*arg_it;
    dst_ptr = lower.builder.CreatePointerCast(dst_ptr, ptr_ty, "block.copy.dst");
    src_ptr = lower.builder.CreatePointerCast(src_ptr, ptr_ty, "block.copy.src");

    llvm::Function* assign_fn = lower.get_or_create_block_object_assign();
    auto* i32_ty = llvm::Type::getInt32Ty(*lower.context);
    for (size_t capture_index = 0;
         capture_index < expr->semantic_info.captures.size();
         ++capture_index) {
        const auto& capture = expr->semantic_info.captures[capture_index];
        auto copy_flags = block_capture_copy_dispose_flags(capture);
        if (!copy_flags.has_value()) {
            continue;
        }
        unsigned field_index = static_cast<unsigned>(capture_index + 5);
        llvm::Value* dst_slot = lower.builder.CreateStructGEP(
            literal_type, dst_ptr, field_index, "block.copy.capture.dst");
        llvm::Value* src_slot = lower.builder.CreateStructGEP(
            literal_type, src_ptr, field_index, "block.copy.capture.src");
        llvm::Value* src_cell = lower.builder.CreateLoad(
            literal_type->getElementType(field_index),
            src_slot,
            "block.copy.capture.load");
        if (src_cell->getType() != ptr_ty) {
            src_cell = lower.builder.CreatePointerCast(
                src_cell, ptr_ty, "block.copy.capture.cast");
        }
        lower.builder.CreateCall(
            assign_fn,
            {dst_slot,
             src_cell,
             llvm::ConstantInt::get(
                 i32_ty,
                 *copy_flags)});
    }
    lower.builder.CreateRetVoid();
    return fn;
}

llvm::Function* get_or_create_block_dispose_helper(ASTToLLVM& lower,
                                                   BlockExpr* expr,
                                                   llvm::StructType* literal_type) {
    if (!expr || !literal_type || !block_literal_needs_copy_dispose(expr)) {
        return nullptr;
    }

    std::string name =
        "__block_dispose_helper_" + block_helper_symbol_suffix(expr);
    if (auto* existing = lower.module->getFunction(name)) {
        return existing;
    }

    llvm::Type* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    auto* fn_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(*lower.context),
        {ptr_ty},
        false);
    auto* fn = llvm::Function::Create(
        fn_ty,
        llvm::Function::InternalLinkage,
        name,
        lower.module.get());

    llvm::IRBuilderBase::InsertPointGuard guard(lower.builder);
    auto* entry_bb = llvm::BasicBlock::Create(*lower.context, "entry", fn);
    lower.builder.SetInsertPoint(entry_bb);

    llvm::Value* src_ptr = &*fn->arg_begin();
    src_ptr = lower.builder.CreatePointerCast(src_ptr, ptr_ty, "block.dispose.src");

    llvm::Function* dispose_fn = lower.get_or_create_block_object_dispose();
    auto* i32_ty = llvm::Type::getInt32Ty(*lower.context);
    for (size_t capture_index = 0;
         capture_index < expr->semantic_info.captures.size();
         ++capture_index) {
        const auto& capture = expr->semantic_info.captures[capture_index];
        auto copy_flags = block_capture_copy_dispose_flags(capture);
        if (!copy_flags.has_value()) {
            continue;
        }
        unsigned field_index = static_cast<unsigned>(capture_index + 5);
        llvm::Value* src_slot = lower.builder.CreateStructGEP(
            literal_type, src_ptr, field_index, "block.dispose.capture.src");
        llvm::Value* src_cell = lower.builder.CreateLoad(
            literal_type->getElementType(field_index),
            src_slot,
            "block.dispose.capture.load");
        if (src_cell->getType() != ptr_ty) {
            src_cell = lower.builder.CreatePointerCast(
                src_cell, ptr_ty, "block.dispose.capture.cast");
        }
        lower.builder.CreateCall(
            dispose_fn,
            {src_cell,
             llvm::ConstantInt::get(
                 i32_ty,
                 *copy_flags)});
    }
    lower.builder.CreateRetVoid();
    return fn;
}

llvm::GlobalVariable* get_or_create_block_signature_global(ASTToLLVM& lower,
                                                           BlockExpr* expr) {
    if (!expr || !expr->semantic_info.invoke_decl) {
        return nullptr;
    }

    std::string name =
        "__block_signature_" + block_helper_symbol_suffix(expr);
    if (auto* existing = lower.module->getGlobalVariable(name, true)) {
        return existing;
    }

    const TargetInfo* target =
        lower.ast_ctx && lower.ast_ctx->type_ctx
            ? lower.ast_ctx->type_ctx->target.get()
            : nullptr;
    std::string signature = darwin_blocks::encode_block_invoke_signature(
        QualType(expr->semantic_info.invoke_decl->type),
        target);
    if (signature.empty()) {
        return nullptr;
    }

    auto* initializer =
        llvm::ConstantDataArray::getString(*lower.context, signature, true);
    auto* global = new llvm::GlobalVariable(
        *lower.module,
        initializer->getType(),
        true,
        llvm::GlobalValue::InternalLinkage,
        initializer,
        name);
    global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    global->setAlignment(llvm::Align(1));
    return global;
}

llvm::GlobalVariable* get_or_create_block_descriptor_global(
    ASTToLLVM& lower,
    BlockExpr* expr,
    llvm::StructType* literal_type,
    llvm::Function* copy_helper,
    llvm::Function* dispose_helper,
    llvm::GlobalVariable* signature_gv) {
    std::string name =
        "__block_descriptor_" + block_helper_symbol_suffix(expr);
    if (auto* existing = lower.module->getGlobalVariable(name, true)) {
        return existing;
    }

    auto* i64_ty = llvm::Type::getInt64Ty(*lower.context);
    auto* ptr_ty = llvm::PointerType::get(*lower.context, 0);
    std::vector<llvm::Type*> descriptor_fields = {i64_ty, i64_ty};
    if (copy_helper || dispose_helper) {
        descriptor_fields.push_back(ptr_ty);
        descriptor_fields.push_back(ptr_ty);
    }
    if (signature_gv) {
        descriptor_fields.push_back(ptr_ty);
        descriptor_fields.push_back(ptr_ty);
    }
    auto* descriptor_ty =
        llvm::StructType::get(*lower.context, descriptor_fields);
    uint64_t literal_size =
        lower.module->getDataLayout().getTypeAllocSize(literal_type);
    std::vector<llvm::Constant*> initializer_fields;
    initializer_fields.push_back(llvm::ConstantInt::get(i64_ty, 0));
    initializer_fields.push_back(llvm::ConstantInt::get(i64_ty, literal_size));
    if (copy_helper || dispose_helper) {
        initializer_fields.push_back(
            copy_helper
                ? llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
                      copy_helper, ptr_ty)
                : llvm::ConstantPointerNull::get(
                      llvm::cast<llvm::PointerType>(ptr_ty)));
        initializer_fields.push_back(
            dispose_helper
                ? llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
                      dispose_helper, ptr_ty)
                : llvm::ConstantPointerNull::get(
                      llvm::cast<llvm::PointerType>(ptr_ty)));
    }
    if (signature_gv) {
        initializer_fields.push_back(
            llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
                signature_gv, ptr_ty));
        initializer_fields.push_back(
            llvm::ConstantPointerNull::get(
                llvm::cast<llvm::PointerType>(ptr_ty)));
    }
    auto* initializer = llvm::ConstantStruct::get(
        descriptor_ty,
        initializer_fields);
    auto* global = new llvm::GlobalVariable(
        *lower.module,
        descriptor_ty,
        true,
        llvm::GlobalValue::InternalLinkage,
        initializer,
        name);
    global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    return global;
}

llvm::Constant* build_global_block_literal_initializer(ASTToLLVM& lower,
                                                       BlockExpr* expr,
                                                       llvm::StructType* literal_type,
                                                       llvm::Function* invoke_fn,
                                                       llvm::GlobalVariable* descriptor_gv,
                                                       bool has_signature) {
    if (!expr || !literal_type || !invoke_fn || !descriptor_gv) {
        return nullptr;
    }
    if (literal_type->getNumElements() < 5) {
        lower.error("convert_block_expression(): invalid global block literal layout",
                    expr->location);
        return nullptr;
    }

    auto* i32_ty = llvm::Type::getInt32Ty(*lower.context);
    auto* isa_gv = get_or_create_darwin_block_runtime_class(
        lower,
        darwin_blocks::ConcreteBlockStorageClass::Global);
    uint32_t flags = darwin_blocks::BLOCK_IS_GLOBAL;
    if (block_literal_needs_copy_dispose(expr)) {
        flags |= darwin_blocks::BLOCK_HAS_COPY_DISPOSE;
    }
    if (has_signature) {
        flags |= darwin_blocks::BLOCK_HAS_SIGNATURE;
    }

    std::vector<llvm::Constant*> fields;
    fields.reserve(literal_type->getNumElements());
    fields.push_back(llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
        isa_gv,
        llvm::cast<llvm::PointerType>(literal_type->getElementType(0))));
    fields.push_back(llvm::ConstantInt::get(i32_ty, flags));
    fields.push_back(llvm::ConstantInt::get(i32_ty, 0));
    fields.push_back(llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
        invoke_fn,
        llvm::cast<llvm::PointerType>(literal_type->getElementType(3))));
    fields.push_back(llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
        descriptor_gv,
        llvm::cast<llvm::PointerType>(literal_type->getElementType(4))));
    return llvm::ConstantStruct::get(literal_type, fields);
}

llvm::GlobalVariable* get_or_create_global_block_literal(ASTToLLVM& lower,
                                                         BlockExpr* expr,
                                                         llvm::StructType* literal_type,
                                                         llvm::Function* invoke_fn,
                                                         llvm::GlobalVariable* descriptor_gv,
                                                         bool has_signature) {
    std::string name =
        "__block_literal_" + block_helper_symbol_suffix(expr);
    if (auto* existing = lower.module->getGlobalVariable(name, true)) {
        return existing;
    }

    auto* initializer = build_global_block_literal_initializer(
        lower,
        expr,
        literal_type,
        invoke_fn,
        descriptor_gv,
        has_signature);
    if (!initializer) {
        return nullptr;
    }
    auto* global = new llvm::GlobalVariable(
        *lower.module,
        literal_type,
        true,
        llvm::GlobalValue::InternalLinkage,
        initializer,
        name);
    global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    return global;
}

} // namespace

llvm::Value * ASTToLLVM::convert_integer_literal(Expr *expr) {
    auto* int_lit = dyn_cast<IntegerLiteral>(expr);
    if (!int_lit) return nullptr;
    auto parsed = parse_integer_literal_u64(int_lit->get_value());
    if (!parsed.has_value()) {
        error("invalid integer literal", expr->location);
        return nullptr;
    }
    uint64_t value = parsed.value();

    // Use the type from the AST if available, otherwise default to i32
    // todo: unsigned
    auto ctype = int_lit->get_type();
    llvm::Type* type = convert_type(ctype);
    if (!type) type = llvm::Type::getInt32Ty(*context);
    bool isUnsigned = ctype->isUnsigned();
    return llvm::ConstantInt::get(type, value, !isUnsigned);
}

llvm::Value * ASTToLLVM::convert_floating_literal(Expr *expr) {
    auto* float_lit = dyn_cast<FloatingLiteral>(expr);
    if (!float_lit) return nullptr;

    auto ctype = float_lit->get_type();
    llvm::Type* type = convert_type(ctype);
    if (!type) type = llvm::Type::getDoubleTy(*context);

    // Parse string to double - use strtod to handle overflow (inf) and underflow (0/subnormal) gracefully
    double value = std::strtod(float_lit->value.c_str(), nullptr);

    if (float_lit->is_imaginary) {
        // Imaginary literal: produce {0.0, value} complex struct
        auto* struct_ty = llvm::dyn_cast<llvm::StructType>(type);
        if (!struct_ty) {
            error("imaginary literal has non-struct LLVM type", expr->location);
            return nullptr;
        }
        llvm::Type* elem_ty = struct_ty->getElementType(0);
        llvm::Value* result = llvm::UndefValue::get(struct_ty);
        if (elem_ty->isFloatingPointTy()) {
            result = builder.CreateInsertValue(result, llvm::ConstantFP::get(elem_ty, 0.0), {0}, "imag.r");
            result = builder.CreateInsertValue(result, llvm::ConstantFP::get(elem_ty, value), {1}, "imag.i");
            return result;
        }
        if (elem_ty->isIntegerTy()) {
            auto parsed = parse_integer_literal_u64(float_lit->value);
            if (!parsed.has_value()) {
                error("invalid imaginary integer literal", expr->location);
                return nullptr;
            }
            auto complex_type = ctype.as_shared<ComplexType>();
            bool is_unsigned = complex_type && complex_type->element_type->isUnsigned();
            result = builder.CreateInsertValue(result, llvm::ConstantInt::get(elem_ty, 0), {0}, "imag.r");
            result = builder.CreateInsertValue(
                result,
                llvm::ConstantInt::get(elem_ty, parsed.value(), !is_unsigned),
                {1},
                "imag.i");
            return result;
        }
        error("imaginary literal has unsupported complex element type", expr->location);
        return result;
    }

    return llvm::ConstantFP::get(type, value);
}
llvm::Value * ASTToLLVM::convert_character_literal(Expr *expr) {
    auto* char_lit = dyn_cast<CharacterLiteral>(expr);
    if (!char_lit) return nullptr;
    return llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), char_lit->int_value, true);
}

llvm::Constant* ASTToLLVM::build_string_literal_array_constant(const StringLiteral* str_lit, size_t len) {
    if (!str_lit) {
        return nullptr;
    }
    auto arr_type = str_lit->ctype.as_shared<ArrayType>();
    if (!arr_type) {
        return nullptr;
    }
    auto elem_ctype = arr_type->element_type.get_shared();
    if (!elem_ctype) {
        return nullptr;
    }
    llvm::Type* elem_type = convert_type(elem_ctype);
    if (!elem_type) {
        return nullptr;
    }

    auto elem_builtin = dyn_cast_shared<BuiltinType>(elem_ctype);
    bool is_char_array = elem_builtin &&
        (elem_builtin->builtin_kind == BuiltinTypes::Char ||
         elem_builtin->builtin_kind == BuiltinTypes::UChar);

    if (is_char_array) {
        std::vector<char> bytes;
        bytes.reserve(len);
        for (size_t i = 0; i < len; ++i) {
            if (i < str_lit->value.size()) {
                bytes.push_back(str_lit->value[i]);
            } else {
                bytes.push_back('\0');
            }
        }
        return llvm::ConstantDataArray::getString(
            *context, llvm::StringRef(bytes.data(), bytes.size()), false);
    }

    if (!elem_type->isIntegerTy()) {
        return nullptr;
    }

    auto codepoints = decode_utf8_codepoints(str_lit->value);
    auto* int_ty = llvm::cast<llvm::IntegerType>(elem_type);
    unsigned elem_bits = int_ty->getBitWidth();
    std::vector<llvm::Constant*> elems;
    elems.reserve(len);
    for (size_t i = 0; i < len; ++i) {
        uint64_t value = (i < codepoints.size()) ? static_cast<uint64_t>(codepoints[i]) : 0ULL;
        if (elem_bits < 64) {
            value &= ((1ULL << elem_bits) - 1ULL);
        }
        elems.push_back(llvm::ConstantInt::get(int_ty, value, false));
    }
    auto* arr_llvm_ty = llvm::ArrayType::get(elem_type, len);
    return llvm::ConstantArray::get(arr_llvm_ty, elems);
}

llvm::Value * ASTToLLVM::convert_string_literal(Expr *expr) {
    auto* str_lit = dyn_cast<StringLiteral>(expr);
    if (!str_lit) return nullptr;
    auto arr_type = str_lit->ctype.as_shared<ArrayType>();
    if (!arr_type || arr_type->size_kind != ArraySizeKind::Constant || !arr_type->size.has_value()) {
        error("convert_string_literal(): invalid array size for string literal", expr->location);
        return nullptr;
    }

    size_t len = arr_type->size.value();
    llvm::Constant* str_data = build_string_literal_array_constant(str_lit, len);
    if (!str_data) {
        error("convert_string_literal(): failed to build literal data", expr->location);
        return nullptr;
    }
    auto* str_global = new llvm::GlobalVariable(
        *module,
        str_data->getType(),
        true,
        llvm::GlobalValue::PrivateLinkage,
        str_data,
        ".str");
    str_global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    auto* arr_llvm_type = llvm::cast<llvm::ArrayType>(str_data->getType());
    uint64_t abi_align = module->getDataLayout().getABITypeAlign(arr_llvm_type->getElementType()).value();
    str_global->setAlignment(llvm::Align(std::max<uint64_t>(1, abi_align)));
    llvm::Value* zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), 0);
    return builder.CreateInBoundsGEP(
        str_global->getValueType(), str_global, {zero, zero}, "str_lit_ptr");
}

llvm::Value* ASTToLLVM::emit_vla_size_value(const std::shared_ptr<Expr>& expr, bool cache) {
    if (!expr) {
        error("emit_vla_size_value(): missing size expression");
        return nullptr;
    }
    auto it = vla_size_cache.find(expr.get());
    if (it != vla_size_cache.end()) {
        return it->second;
    }
    llvm::Value* val = convert_expression(expr.get());
    if (!val) return nullptr;
    llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
    if (val->getType() != i64) {
        bool isUnsigned = expr->get_type() && expr->get_type()->isUnsigned();
        val = builder.CreateIntCast(val, i64, !isUnsigned, "vla_size_cast");
    }
    if (cache) {
        vla_size_cache[expr.get()] = val;
    }
    return val;
}

llvm::Value* ASTToLLVM::emit_type_size_bytes(std::shared_ptr<CType> type, bool use_cache) {
    type = desugar_type(type, ast_ctx.get());
    if (!type) {
        error("emit_type_size_bytes(): null type");
        return nullptr;
    }
    llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
    if (auto arr = dyn_cast_shared<ArrayType>(type)) {
        if (arr->size_kind == ArraySizeKind::Incomplete) {
            error("emit_type_size_bytes(): sizeof incomplete array type");
            return nullptr;
        }
        llvm::Value* elem_size = emit_type_size_bytes(arr->element_type.get_shared(), use_cache);
        if (!elem_size) return nullptr;

        llvm::Value* dim_val = nullptr;
        if (arr->size_kind == ArraySizeKind::Constant && arr->size.has_value()) {
            dim_val = llvm::ConstantInt::get(i64, arr->size.value());
        } else if (arr->size_kind == ArraySizeKind::Variable) {
            dim_val = emit_vla_size_value(arr->size_expr, use_cache);
        }
        if (!dim_val) return nullptr;

        if (auto dim_c = llvm::dyn_cast<llvm::ConstantInt>(dim_val)) {
            if (auto elem_c = llvm::dyn_cast<llvm::ConstantInt>(elem_size)) {
                uint64_t prod = dim_c->getZExtValue() * elem_c->getZExtValue();
                return llvm::ConstantInt::get(i64, prod);
            }
        }
        return builder.CreateMul(dim_val, elem_size, "vla_size_mul");
    }
    int64_t size_bytes = type->getWidthBytes();
    return llvm::ConstantInt::get(i64, static_cast<uint64_t>(size_bytes));
}

void ASTToLLVM::cache_vla_sizes_for_type(std::shared_ptr<CType> type) {
    std::unordered_set<const CType*> visited;
    std::function<void(const std::shared_ptr<CType>&)> walk =
        [&](const std::shared_ptr<CType>& current) {
            if (!current) {
                return;
            }
            const CType* key = current.get();
            if (!visited.insert(key).second) {
                return;
            }

            if (auto td = dyn_cast_shared<TypedefType>(current)) {
                walk(td->underlying_type.get_shared());
                return;
            }
            if (auto arr = dyn_cast_shared<ArrayType>(current)) {
                if (arr->size_kind == ArraySizeKind::Variable) {
                    emit_vla_size_value(arr->size_expr, true);
                }
                walk(arr->element_type.get_shared());
                return;
            }
            if (auto ptr = dyn_cast_shared<PointerType>(current)) {
                walk(ptr->pointed_type.get_shared());
                return;
            }
            if (auto blk = dyn_cast_shared<BlockPointerType>(current)) {
                walk(blk->pointed_type.get_shared());
                return;
            }
            if (auto func = dyn_cast_shared<FunctionType>(current)) {
                walk(func->ret_type.get_shared());
                for (const auto& param : func->parameters) {
                    walk(param.get_shared());
                }
                return;
            }
            if (auto obj = dyn_cast_shared<ObjectType>(current)) {
                for (const auto& field : obj->semantic_fields()) {
                    walk(field.type.get_shared());
                }
                return;
            }
        };
    walk(type);
}

std::pair<llvm::Type*, llvm::Value*>
ASTToLLVM::get_vla_flat_element_and_count(std::shared_ptr<ArrayType> arr_type) {
    llvm::Type* i64 = llvm::Type::getInt64Ty(*context);
    std::vector<llvm::Value*> dim_sizes;
    std::shared_ptr<CType> cur = desugar_type(arr_type, ast_ctx.get());

    while (auto arr = dyn_cast_shared<ArrayType>(cur)) {
        llvm::Value* dim_val = nullptr;
        if (arr->size_kind == ArraySizeKind::Constant && arr->size.has_value()) {
            dim_val = llvm::ConstantInt::get(i64, arr->size.value());
        } else if (arr->size_kind == ArraySizeKind::Variable) {
            dim_val = emit_vla_size_value(arr->size_expr, true);
        } else {
            error("get_vla_flat_element_and_count: incomplete array dimension");
            return {nullptr, nullptr};
        }
        dim_sizes.push_back(dim_val);
        cur = desugar_type(arr->element_type.get_shared(), ast_ctx.get());
    }

    llvm::Type* elem_llvm_type = convert_type(cur);
    llvm::Value* total = dim_sizes[0];
    for (size_t i = 1; i < dim_sizes.size(); i++) {
        total = builder.CreateMul(total, dim_sizes[i], "vla_dim_mul");
    }
    return {elem_llvm_type, total};
}

llvm::Value* ASTToLLVM::materialize_reference_rvalue(Expr* expr,
                                                     llvm::Value* lowered_value,
                                                     const char* context_name) {
    if (!expr || !lowered_value) {
        return lowered_value;
    }
    if (canonical_type_kind(expr->get_type(), ast_ctx.get()) != TypeKind::Reference) {
        return lowered_value;
    }

    auto ref_type =
        desugar_type(expr->get_type(), ast_ctx.get()).as_shared<ReferenceType>();
    if (!ref_type || !ref_type->referred_type) {
        error(std::string(context_name) + ": invalid reference result type",
              expr->location);
        return nullptr;
    }
    if (!lowered_value->getType()->isPointerTy()) {
        error(std::string(context_name) +
                  ": reference result did not lower to an address",
              expr->location);
        return nullptr;
    }

    llvm::Type* referred_llvm_type = convert_type(ref_type->referred_type.get_shared());
    if (!referred_llvm_type) {
        error(std::string(context_name) +
                  ": failed to lower reference target type",
              expr->location);
        return nullptr;
    }
    return builder.CreateLoad(referred_llvm_type, lowered_value, "ref.rvalue");
}

llvm::Value* ASTToLLVM::convert_var_ref(VarRef *expr) {
    if (expr->symref && expr->symref->kind == SymbolKind::ENUM_CONSTANT) {
        // Enum constant is an rvalue; preserve the symbol integer width so
        // large enumerators are not truncated to i32.
        QualType sym_type = expr->symref->type;
        llvm::Type* llvm_type = sym_type ? convert_type(sym_type.get_shared())
                                         : llvm::Type::getInt32Ty(*context);
        if (!llvm_type || !llvm_type->isIntegerTy()) {
            llvm_type = llvm::Type::getInt32Ty(*context);
        }
        if (sym_type && sym_type->isUnsigned()) {
            return llvm::ConstantInt::get(llvm_type, static_cast<uint64_t>(expr->symref->enum_val), false);
        }
        return llvm::ConstantInt::getSigned(llvm_type, expr->symref->enum_val);
    }
    error("internal error: we shouldn't be in convert_var_ref", expr->location); // should be handled by implict cast
    return nullptr;
}
llvm::Constant* ASTToLLVM::emit_constant_initializer(Expr* expr) {
    if (!expr) return nullptr;

    bool allow_consteval_fast_path =
        !llvm::isa<ExplicitCast>(expr) && !llvm::isa<ImplicitCast>(expr);
    llvm::Type* expr_ty = convert_type(expr->get_type());
    bool expr_is_unsigned = expr->get_type() && expr->get_type()->isUnsigned();
    if (allow_consteval_fast_path && expr_ty) {
        if (auto* lowered = lower_consteval_to_llvm_constant(
                expr, expr_ty, expr_is_unsigned, ConstEvalMode::c_static_initializer())) {
            return lowered;
        }
    }

    auto adjust_member_pointer_constant_owner_offset =
        [&](llvm::Constant* constant_value,
            QualType source_type,
            QualType target_type) -> llvm::Constant* {
        auto source_member_ptr =
            desugar_type(source_type, ast_ctx.get()).as_shared<MemberPointerType>();
        auto target_member_ptr =
            desugar_type(target_type, ast_ctx.get()).as_shared<MemberPointerType>();
        if (!constant_value ||
            !source_member_ptr ||
            !target_member_ptr) {
            return constant_value;
        }
        auto source_member_kind =
            canonical_type_kind(source_member_ptr->member_type, ast_ctx.get());
        auto target_member_kind =
            canonical_type_kind(target_member_ptr->member_type, ast_ctx.get());
        bool function_member_kind =
            source_member_kind == TypeKind::Function &&
            target_member_kind == TypeKind::Function;
        if (source_member_kind != target_member_kind) {
            return constant_value;
        }

        auto source_owner_type =
            desugar_type(source_member_ptr->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto target_owner_type =
            desugar_type(target_member_ptr->class_type, ast_ctx.get())
                .as_shared<ObjectType>();
        auto* source_owner_decl = source_owner_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(source_owner_type->get_decl()))
            : nullptr;
        auto* target_owner_decl = target_owner_type
            ? canonical_cpp_record_decl(dyn_cast<ObjectDecl>(target_owner_type->get_decl()))
            : nullptr;
        if (!source_owner_decl || !target_owner_decl || source_owner_decl == target_owner_decl) {
            return constant_value;
        }

        std::optional<size_t> owner_offset = find_cpp_base_subobject_offset(
            target_owner_decl, source_owner_decl);
        if (!owner_offset.has_value() || *owner_offset == 0) {
            return constant_value;
        }
        if (*owner_offset >
            static_cast<size_t>(std::numeric_limits<int64_t>::max())) {
            return constant_value;
        }

        if (function_member_kind) {
            auto* constant_struct =
                llvm::dyn_cast<llvm::ConstantStruct>(constant_value);
            if (!constant_struct || constant_struct->getNumOperands() != 2) {
                return constant_value;
            }
            llvm::Constant* function_payload =
                constant_struct->getOperand(0);
            auto* this_adjust = llvm::dyn_cast<llvm::ConstantInt>(
                constant_struct->getOperand(1));
            if (!function_payload || !this_adjust ||
                function_payload->isNullValue()) {
                return constant_value;
            }
            llvm::APInt adjusted =
                this_adjust->getValue() + llvm::APInt(
                    this_adjust->getBitWidth(),
                    static_cast<uint64_t>(*owner_offset),
                    false);
            llvm::Constant* adjusted_this = llvm::ConstantInt::get(
                this_adjust->getType(), adjusted);
            return llvm::ConstantStruct::get(
                constant_struct->getType(), {function_payload, adjusted_this});
        }

        auto* constant_int = llvm::dyn_cast<llvm::ConstantInt>(constant_value);
        if (!constant_int) {
            return constant_value;
        }
        if (constant_int->isZero()) {
            return constant_int;
        }
        llvm::APInt adjusted = constant_int->getValue() + llvm::APInt(
            constant_int->getBitWidth(), static_cast<uint64_t>(*owner_offset), false);
        return llvm::ConstantInt::get(constant_int->getType(), adjusted);
    };

    // Integer literal
    if (auto* intLit = dyn_cast<IntegerLiteral>(expr)) {
        auto val = eval_constexpr_i64(intLit, ConstEvalMode::c_ice());
        if (!val.has_value()) return nullptr;
        llvm::Type* ty = convert_type(intLit->get_type());
        bool isUnsigned = intLit->get_type() && intLit->get_type()->isUnsigned();
        if (isUnsigned)
            return llvm::ConstantInt::get(ty, static_cast<uint64_t>(*val));
        return llvm::ConstantInt::getSigned(ty, *val);
    }

    // Float literal
    if (auto* floatLit = dyn_cast<FloatingLiteral>(expr)) {
        llvm::Type* ty = convert_type(floatLit->get_type());
        long double value = std::strtold(floatLit->value.c_str(), nullptr);
        if (ty->isFloatTy()) {
            return llvm::ConstantFP::get(ty, static_cast<double>(static_cast<float>(value)));
        }
        if (ty->isDoubleTy()) {
            return llvm::ConstantFP::get(ty, static_cast<double>(value));
        }
        return llvm::ConstantFP::get(ty, static_cast<double>(value));
    }

    // Character literal
    if (auto* charLit = dyn_cast<CharacterLiteral>(expr)) {
        llvm::Type* ty = convert_type(charLit->get_type());
        return llvm::ConstantInt::get(ty, static_cast<uint64_t>(charLit->int_value));
    }

    if (auto* strLit = dyn_cast<StringLiteral>(expr)) {
        auto arr_type = strLit->ctype.as_shared<ArrayType>();
        if (!arr_type || arr_type->size_kind != ArraySizeKind::Constant ||
            !arr_type->size.has_value()) {
            return nullptr;
        }

        size_t len = arr_type->size.value();
        llvm::Constant* str_data =
            build_string_literal_array_constant(strLit, len);
        if (!str_data) {
            return nullptr;
        }

        auto* str_global = new llvm::GlobalVariable(
            *module,
            str_data->getType(),
            true,
            llvm::GlobalValue::PrivateLinkage,
            str_data,
            ".str");
        str_global->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);

        auto* arr_llvm_type =
            llvm::cast<llvm::ArrayType>(str_data->getType());
        uint64_t abi_align =
            module->getDataLayout()
                .getABITypeAlign(arr_llvm_type->getElementType())
                .value();
        str_global->setAlignment(
            llvm::Align(std::max<uint64_t>(1, abi_align)));

        llvm::Constant* zero =
            llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context), 0);
        llvm::Constant* indices[] = {zero, zero};
        return llvm::ConstantExpr::getInBoundsGetElementPtr(
            str_global->getValueType(), str_global, indices);
    }

    if (auto* member_ptr_lit = dyn_cast<MemberPointerLiteralExpr>(expr)) {
        auto mp_type =
            desugar_type(member_ptr_lit->get_type(), ast_ctx.get())
                .as_shared<MemberPointerType>();
        if (!mp_type) {
            return nullptr;
        }
        if (canonical_type_kind(mp_type->member_type, ast_ctx.get()) == TypeKind::Function ||
            member_ptr_lit->is_function_member) {
            llvm::Value* lowered = convert_member_pointer_literal_expr(member_ptr_lit);
            return llvm::dyn_cast<llvm::Constant>(lowered);
        }
        llvm::Type* ty = convert_type(member_ptr_lit->get_type());
        if (!ty || !ty->isIntegerTy()) {
            return nullptr;
        }
        return llvm::ConstantInt::getSigned(ty, member_ptr_lit->byte_offset);
    }

    // VarRef — look up const global initializer or enum constant
    if (auto* varRef = dyn_cast<VarRef>(expr)) {
        if (varRef->symref && varRef->symref->kind == SymbolKind::ENUM_CONSTANT) {
            llvm::Type* ty = convert_type(varRef->get_type());
            return llvm::ConstantInt::getSigned(ty, varRef->symref->enum_val);
        }
        if (!varRef->symref) return nullptr;
        std::string mangled = mangleCIdentifier(varRef->symref->uid);
        auto it = named_values.find(mangled);
        if (it != named_values.end()) {
            if (auto* gVar = llvm::dyn_cast<llvm::GlobalVariable>(it->second)) {
                if (gVar->hasInitializer() && gVar->isConstant()) {
                    return gVar->getInitializer();
                }
            }
        }
        return nullptr;
    }

    // Compound literal: treat file-scope/block-scope literal initializer payload
    // as a constant aggregate when all elements are constant.
    if (auto* compound = dyn_cast<CompoundLiteralExpr>(expr)) {
        if (!compound->init) {
            return nullptr;
        }
        llvm::Type* litTy = convert_type(compound->type);
        if (!litTy) {
            return nullptr;
        }
        if (auto* initList = dyn_cast<InitListExpr>(compound->init.get())) {
            if (!initList->type && compound->type) {
                initList->type = compound->type;
            }
            return convert_init_list(initList, litTy);
        }
        llvm::Constant* inner = emit_constant_initializer(compound->init.get());
        if (!inner) {
            return nullptr;
        }
        if (inner->getType() == litTy) {
            return inner;
        }
        bool srcUns = compound->init->get_type() && compound->init->get_type()->isUnsigned();
        bool dstUns = compound->type && compound->type->isUnsigned();
        return fold_constant_cast(inner, litTy, srcUns, dstUns, module->getDataLayout());
    }

    // Explicit cast
    if (auto* cast = dyn_cast<ExplicitCast>(expr)) {
        llvm::Type* destTy = convert_type(cast->ctype);
        if (destTy && (destTy->isStructTy() || destTy->isArrayTy() || destTy->isVectorTy())) {
            if (auto* subList = unwrap_init_list_expr(cast->expr.get())) {
                if (!subList->type && cast->ctype) {
                    subList->type = cast->ctype;
                }
                return convert_init_list(subList, destTy);
            }
        }
        llvm::Constant* inner = emit_constant_initializer(cast->expr.get());
        if (!inner) return nullptr;
        if (!destTy) return nullptr;
        inner = adjust_member_pointer_constant_owner_offset(
            inner, cast->expr->get_type(), cast->ctype);
        bool srcUns = cast->expr->get_type() && cast->expr->get_type()->isUnsigned();
        bool dstUns = cast->ctype && cast->ctype->isUnsigned();
        return fold_constant_cast(inner, destTy, srcUns, dstUns, module->getDataLayout());
    }

    // Implicit cast
    if (auto* cast = dyn_cast<ImplicitCast>(expr)) {
        if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
            return emit_constant_initializer(cast->expr.get());
        }
        llvm::Constant* inner = emit_constant_initializer(cast->expr.get());
        if (!inner) return nullptr;
        llvm::Type* destTy = convert_type(cast->get_type());
        inner = adjust_member_pointer_constant_owner_offset(
            inner, cast->expr->get_type(), cast->get_type());
        bool srcUns = cast->expr->get_type() && cast->expr->get_type()->isUnsigned();
        bool dstUns = cast->get_type() && cast->get_type()->isUnsigned();
        return fold_constant_cast(inner, destTy, srcUns, dstUns, module->getDataLayout());
    }

    // Binary operation — constant fold at C++ level
    if (auto* binOp = dyn_cast<BinaryOperation>(expr)) {
        llvm::Constant* lhs = emit_constant_initializer(binOp->left.get());
        llvm::Constant* rhs = emit_constant_initializer(binOp->right.get());
        if (!lhs || !rhs) return nullptr;

        // Float binary ops
        auto* lf = llvm::dyn_cast<llvm::ConstantFP>(lhs);
        auto* rf = llvm::dyn_cast<llvm::ConstantFP>(rhs);
        if (lf && rf) {
            double lv = lf->getValueAPF().convertToDouble();
            double rv = rf->getValueAPF().convertToDouble();
            double res;
            switch (binOp->bop) {
                case BinOpTypes::ADD: res = lv + rv; break;
                case BinOpTypes::SUB: res = lv - rv; break;
                case BinOpTypes::MULT: res = lv * rv; break;
                case BinOpTypes::DIV: res = lv / rv; break;
                default: return nullptr;
            }
            return llvm::ConstantFP::get(lhs->getType(), res);
        }

        // Integer binary ops — use ConstantExpr where available, manual otherwise
        auto* li = llvm::dyn_cast<llvm::ConstantInt>(lhs);
        auto* ri = llvm::dyn_cast<llvm::ConstantInt>(rhs);
        if (li && ri) {
            bool isUnsigned = binOp->get_type() && binOp->get_type()->isUnsigned();
            uint64_t lv = li->getZExtValue();
            uint64_t rv = ri->getZExtValue();
            int64_t slv = li->getSExtValue();
            int64_t srv = ri->getSExtValue();
            llvm::Type* ty = lhs->getType();
            switch (binOp->bop) {
                case BinOpTypes::ADD:
                    return llvm::ConstantExpr::getAdd(lhs, rhs);
                case BinOpTypes::SUB:
                    return llvm::ConstantExpr::getSub(lhs, rhs);
                case BinOpTypes::MULT:
                    return llvm::ConstantExpr::getMul(lhs, rhs);
                case BinOpTypes::DIV:
                    if (rv == 0) return nullptr;
                    if (isUnsigned)
                        return llvm::ConstantInt::get(ty, lv / rv);
                    else
                        return llvm::ConstantInt::getSigned(ty, slv / srv);
                case BinOpTypes::MOD:
                    if (rv == 0) return nullptr;
                    if (isUnsigned)
                        return llvm::ConstantInt::get(ty, lv % rv);
                    else
                        return llvm::ConstantInt::getSigned(ty, slv % srv);
                case BinOpTypes::BITWISE_AND:
                    return llvm::ConstantInt::get(ty, lv & rv);
                case BinOpTypes::BITWISE_OR:
                    return llvm::ConstantInt::get(ty, lv | rv);
                case BinOpTypes::BITWISE_XOR:
                    return llvm::ConstantExpr::getXor(lhs, rhs);
                case BinOpTypes::SHIFT_LEFT:
                    return llvm::ConstantExpr::getShl(lhs, rhs);
                case BinOpTypes::SHIFT_RIGHT:
                    if (isUnsigned)
                        return llvm::ConstantInt::get(ty, lv >> rv);
                    else
                        return llvm::ConstantInt::getSigned(ty, slv >> rv);
                default:
                    return nullptr;
            }
        }

        return nullptr;
    }

    // Unary operation
    if (auto* unaryOp = dyn_cast<UnaryOperation>(expr)) {
        if (unaryOp->uop == UnaryOpTypes::ADDRESS_OF) {
            auto lvalue = get_lvalue(unaryOp->exp.get());
            return llvm::dyn_cast_or_null<llvm::Constant>(lvalue.address);
        }
        llvm::Constant* operand = emit_constant_initializer(unaryOp->exp.get());
        if (!operand) return nullptr;
        switch (unaryOp->uop) {
            case UnaryOpTypes::NEG:
                if (auto* cf = llvm::dyn_cast<llvm::ConstantFP>(operand)) {
                    double v = cf->getValueAPF().convertToDouble();
                    return llvm::ConstantFP::get(operand->getType(), -v);
                }
                return llvm::ConstantExpr::getNeg(operand);
            case UnaryOpTypes::BITWISE_NOT:
                return llvm::ConstantExpr::getNot(operand);
            default:
                return nullptr;
        }
    }

    // SizeOf / AlignOf — use frontend consteval compatibility lane
    if (auto* sizeOf = dyn_cast<SizeOfExpr>(expr)) {
        auto val = eval_constexpr_i64(sizeOf, ConstEvalMode::c_ice());
        if (val.has_value()) {
            llvm::Type* ty = convert_type(sizeOf->get_type());
            return llvm::ConstantInt::get(ty, *val);
        }
        return nullptr;
    }

    // Generic consteval-compat fallback for integer constant expressions
    auto val = eval_constexpr_i64(expr, ConstEvalMode::c_ice());
    if (val.has_value()) {
        llvm::Type* ty = convert_type(expr->get_type());
        if (ty && ty->isIntegerTy()) {
            return llvm::ConstantInt::getSigned(ty, *val);
        }
    }

    return nullptr;
}
// for tenative definitions
llvm::Value* ASTToLLVM::convert_init_list_rvalue_expression(InitListExpr* init_list,
                                                            SrcLoc expr_loc) {
    QualType init_type = init_list->get_type();
    if (!init_type) {
        error("convert_expression(): initializer-list expression requires resolved type",
              expr_loc);
        return nullptr;
    }

    llvm::Type* llvm_init_type = convert_type(init_type.get_shared());
    if (!llvm_init_type) {
        error("convert_expression(): failed to lower initializer-list type",
              expr_loc);
        return nullptr;
    }

    if (!builder.GetInsertBlock()) {
        llvm::Constant* init_const = convert_init_list(init_list, llvm_init_type);
        if (!init_const) {
            error("convert_expression(): non-constant initializer-list expression at global scope",
                  expr_loc);
        }
        return init_const;
    }

    llvm::Function* function = builder.GetInsertBlock()->getParent();
    if (!function) {
        error("convert_expression(): initializer-list expression outside of function",
              expr_loc);
        return nullptr;
    }

    llvm::AllocaInst* tmp_alloca =
        create_entry_alloca(function, llvm_init_type, nullptr, "initlist.rval.tmp");
    if (!tmp_alloca) {
        error("convert_expression(): failed to allocate initializer-list temporary",
              expr_loc);
        return nullptr;
    }

    uint64_t alignment = semantic_type_alignment(init_type.get_shared());
    if (alignment > 0) {
        tmp_alloca->setAlignment(llvm::Align(alignment));
    }

    emit_init_list_store(
        init_list,
        tmp_alloca,
        init_type.get_shared(),
        init_type.is_volatile(),
        init_type.is_atomic());
    auto* load = builder.CreateLoad(llvm_init_type, tmp_alloca, "initlist.rval");
    if (init_type.is_volatile()) {
        load->setVolatile(true);
    }
    if (init_type.is_atomic() &&
        (llvm_init_type->isIntegerTy() || llvm_init_type->isPointerTy())) {
        load->setAtomic(llvm::AtomicOrdering::SequentiallyConsistent);
        load->setAlignment(
            llvm::Align(module->getDataLayout().getTypeAllocSize(llvm_init_type)));
    }
    return load;
}

llvm::Value* ASTToLLVM::convert_cpp_construct_temporary_expression(
    CppConstructExpr* ctor_expr,
    SrcLoc expr_loc) {
    QualType ctor_type = desugar_type(ctor_expr->ctype, ast_ctx.get());
    llvm::Type* llvm_ctor_type = ctor_type
        ? convert_type(ctor_type.get_shared())
        : nullptr;
    if (!llvm_ctor_type) {
        error("convert_expression(): invalid CppConstructExpr type",
              expr_loc);
        return nullptr;
    }

    llvm::Function* function = builder.GetInsertBlock()
        ? builder.GetInsertBlock()->getParent()
        : nullptr;
    if (!function) {
        error("convert_expression(): constructor temporary outside of function",
              expr_loc);
        return nullptr;
    }

    llvm::AllocaInst* tmp_alloca =
        create_entry_alloca(function, llvm_ctor_type, nullptr, "ctor.rval.tmp");
    if (!tmp_alloca) {
        error("convert_expression(): failed to allocate constructor temporary",
              expr_loc);
        return nullptr;
    }

    uint64_t alignment = semantic_type_alignment(ctor_type.get_shared());
    if (alignment > 0) {
        tmp_alloca->setAlignment(llvm::Align(alignment));
    }

    if (!emit_cpp_construct_call(
            ctor_expr,
            tmp_alloca,
            expr_loc,
            "convert_expression() temporary constructor")) {
        return nullptr;
    }

    auto* load = builder.CreateLoad(llvm_ctor_type, tmp_alloca, "ctor.rval");
    if (ctor_expr->ctype.is_volatile()) {
        load->setVolatile(true);
    }
    return load;
}

llvm::Value* ASTToLLVM::convert_block_expression(BlockExpr* expr) {
    if (!expr || !expr->semantic_info.literal_record()) {
        error("convert_block_expression(): missing block semantic record",
              expr ? expr->location : SrcLoc());
        return nullptr;
    }

    auto literal_type =
        desugar_type(expr->semantic_info.literal_type(), ast_ctx.get())
            .as_shared<ObjectType>();
    auto* literal_llvm_type =
        literal_type ? llvm::dyn_cast<llvm::StructType>(
                           convert_type(literal_type))
                     : nullptr;
    if (!literal_llvm_type) {
        error("convert_block_expression(): invalid block literal storage type",
              expr->location);
        return nullptr;
    }

    llvm::Function* invoke_fn =
        get_or_create_block_invoke_declaration(*this, expr);
    if (!invoke_fn) {
        return nullptr;
    }

    llvm::Function* copy_helper =
        get_or_create_block_copy_helper(*this, expr, literal_llvm_type);
    llvm::Function* dispose_helper =
        get_or_create_block_dispose_helper(*this, expr, literal_llvm_type);
    llvm::GlobalVariable* signature_gv =
        get_or_create_block_signature_global(*this, expr);

    auto* descriptor_gv = get_or_create_block_descriptor_global(
        *this,
        expr,
        literal_llvm_type,
        copy_helper,
        dispose_helper,
        signature_gv);
    if (!descriptor_gv) {
        error("convert_block_expression(): failed to create block descriptor",
              expr->location);
        return nullptr;
    }

    auto* block_ptr_ty = llvm::PointerType::getUnqual(*context);
    if (expr->semantic_info.captures.empty()) {
        auto* global_literal = get_or_create_global_block_literal(
            *this,
            expr,
            literal_llvm_type,
            invoke_fn,
            descriptor_gv,
            signature_gv != nullptr);
        if (!global_literal) {
            error("convert_block_expression(): failed to create global block literal",
                  expr->location);
            return nullptr;
        }
        return llvm::ConstantExpr::getPointerBitCastOrAddrSpaceCast(
            global_literal,
            block_ptr_ty);
    }

    llvm::Function* function = builder.GetInsertBlock()
        ? builder.GetInsertBlock()->getParent()
        : nullptr;
    if (!function) {
        error("convert_block_expression(): capturing blocks require function scope",
              expr->location);
        return nullptr;
    }

    llvm::AllocaInst* block_storage =
        create_entry_alloca(function, literal_llvm_type, nullptr, "block.literal");
    if (!block_storage) {
        error("convert_block_expression(): failed to allocate stack block storage",
              expr->location);
        return nullptr;
    }
    block_storage->setAlignment(
        module->getDataLayout().getABITypeAlign(literal_llvm_type));

    auto* i32_ty = llvm::Type::getInt32Ty(*context);
    auto* isa_gv = get_or_create_darwin_block_runtime_class(
        *this,
        darwin_blocks::ConcreteBlockStorageClass::Stack);
    uint32_t block_flags = 0;
    if (block_literal_needs_copy_dispose(expr)) {
        block_flags |= darwin_blocks::BLOCK_HAS_COPY_DISPOSE;
    }
    if (signature_gv) {
        block_flags |= darwin_blocks::BLOCK_HAS_SIGNATURE;
    }

    auto store_literal_field =
        [&](unsigned index,
            llvm::Value* value,
            const char* field_name) -> bool {
            auto* slot = builder.CreateStructGEP(
                literal_llvm_type, block_storage, index, field_name);
            auto* slot_type = literal_llvm_type->getElementType(index);
            if (value->getType() != slot_type) {
                if (value->getType()->isPointerTy() && slot_type->isPointerTy()) {
                    value = builder.CreatePointerCast(value, slot_type);
                } else {
                    bool src_unsigned = false;
                    value = cast_llvm_type(value, slot_type, src_unsigned);
                }
            }
            builder.CreateStore(value, slot);
            return true;
        };

    store_literal_field(0, isa_gv, "block.isa");
    store_literal_field(1, llvm::ConstantInt::get(i32_ty, block_flags), "block.flags");
    store_literal_field(2, llvm::ConstantInt::get(i32_ty, 0), "block.reserved");
    store_literal_field(3, invoke_fn, "block.invoke");
    store_literal_field(4, descriptor_gv, "block.descriptor");

    const llvm::DataLayout& DL = module->getDataLayout();
    for (size_t capture_index = 0;
         capture_index < expr->semantic_info.captures.size();
         ++capture_index) {
        const auto& capture = expr->semantic_info.captures[capture_index];
        if (!capture.symbol) {
            error("convert_block_expression(): block capture missing symbol",
                  expr->location);
            return nullptr;
        }

        unsigned field_index = static_cast<unsigned>(capture_index + 5);
        auto* dest_slot = builder.CreateStructGEP(
            literal_llvm_type,
            block_storage,
            field_index,
            "block.capture");
        auto* dest_type = literal_llvm_type->getElementType(field_index);

        if (capture.kind == BlockCaptureKind::ByRef) {
            llvm::Value* cell_addr = get_block_byref_cell_address(
                capture.symbol.get(),
                expr->location,
                "convert_block_expression()");
            if (!cell_addr) {
                return nullptr;
            }
            if (cell_addr->getType() != dest_type) {
                cell_addr = builder.CreatePointerCast(
                    cell_addr, dest_type, "block.capture.byref.cast");
            }
            auto* store = builder.CreateStore(cell_addr, dest_slot);
            store->setAlignment(DL.getABITypeAlign(dest_type));
            continue;
        }

        VarRef capture_ref(capture.symbol, expr->location);
        auto capture_canonical =
            desugar_type(capture.capture_type, ast_ctx.get());
        bool capture_is_aggregate =
            capture_canonical &&
            (capture_canonical->kind == TypeKind::Object ||
             capture_canonical->kind == TypeKind::Array);
        if (capture_is_aggregate) {
            llvm::Value* src_addr = get_lvalue(&capture_ref).address;
            if (!src_addr) {
                error("convert_block_expression(): aggregate capture requires lvalue source",
                      expr->location);
                return nullptr;
            }
            uint64_t size_bytes = DL.getTypeAllocSize(dest_type);
            builder.CreateMemCpy(
                dest_slot,
                DL.getABITypeAlign(dest_type),
                src_addr,
                llvm::MaybeAlign(1),
                size_bytes);
            continue;
        }

        llvm::Value* capture_value = nullptr;
        if (llvm::Value* src_addr = get_lvalue(&capture_ref).address) {
            llvm::Type* src_type =
                convert_type(remove_reference(capture.symbol->type, ast_ctx.get()).get_shared());
            if (!src_type) {
                error("convert_block_expression(): failed to lower scalar capture source type",
                      expr->location);
                return nullptr;
            }
            capture_value = builder.CreateLoad(src_type, src_addr, "block.capture.load");
        } else {
            capture_value = convert_expression(&capture_ref);
            if (!capture_value) {
                error("convert_block_expression(): failed to lower block capture value",
                      expr->location);
                return nullptr;
            }
        }
        if (capture_value->getType() != dest_type) {
            bool src_unsigned =
                capture.symbol->type && capture.symbol->type->isUnsigned();
            capture_value = cast_llvm_type(capture_value, dest_type, src_unsigned);
        }
        auto* store = builder.CreateStore(capture_value, dest_slot);
        store->setAlignment(DL.getABITypeAlign(dest_type));
    }

    return builder.CreatePointerCast(block_storage, block_ptr_ty, "block.ptr");
}

llvm::Value * ASTToLLVM::convert_expression(Expr *expr) {
    if (!expr) {
        error("convert_expression(): internal error, missing expr node in convert_expression");
        return nullptr;
    }
    switch (expr->get_kind()) {
        case StmtKind::IntegerLiteral:
            return convert_integer_literal(static_cast<IntegerLiteral*>(expr));
        case StmtKind::FloatingLiteral:
            return convert_floating_literal(static_cast<FloatingLiteral*>(expr));
        case StmtKind::CharacterLiteral:
            return convert_character_literal(static_cast<CharacterLiteral*>(expr));
        case StmtKind::StringLiteral:
            return convert_string_literal(static_cast<StringLiteral*>(expr));
        case StmtKind::PredefinedExpr:
            return builder.CreateGlobalStringPtr(
                static_cast<PredefinedExpr*>(expr)->func_name, "__func__");
        case StmtKind::CppThisExpr: {
            auto* this_expr = static_cast<CppThisExpr*>(expr);
            llvm::Function* current_fn =
                builder.GetInsertBlock() ? builder.GetInsertBlock()->getParent() : nullptr;
            if (!current_fn) {
                error("convert_expression(): 'this' expression outside of function",
                      expr->location);
                return nullptr;
            }
            if (current_fn->arg_empty()) {
                error("convert_expression(): missing implicit object argument for 'this'",
                      expr->location);
                return nullptr;
            }
            llvm::Value* this_value = current_fn->getArg(0);
            llvm::Type* expected_type = convert_type(this_expr->get_type());
            if (expected_type && this_value->getType() != expected_type) {
                this_value = cast_llvm_type(this_value, expected_type, false);
            }
            return this_value;
        }
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef:
            return convert_var_ref(static_cast<VarRef*>(expr));
        case StmtKind::BlockByrefAccessExpr: {
            auto lvalue = get_lvalue(expr);
            if (!lvalue.address || !lvalue.type) {
                return nullptr;
            }
            llvm::Type* value_type = convert_type(lvalue.type);
            if (!value_type) {
                error("convert_expression(): failed to lower __block access type",
                      expr->location);
                return nullptr;
            }
            auto* load = builder.CreateLoad(value_type, lvalue.address,
                                            "block.byref.load");
            apply_load_qualifiers(load, expr->get_type(), module->getDataLayout());
            return load;
        }
        case StmtKind::LabelAddressExpr:
            return convert_label_address_expr(static_cast<LabelAddressExpr*>(expr));
        case StmtKind::FuncCall:
            return materialize_reference_rvalue(
                expr,
                convert_function_call(static_cast<FuncCall*>(expr)),
                "convert_expression(): function call");
        case StmtKind::CppMemberCallExpr:
            return materialize_reference_rvalue(
                expr,
                convert_cpp_member_call(static_cast<CppMemberCallExpr*>(expr)),
                "convert_expression(): member call");
        case StmtKind::CppConstructExpr:
            return convert_cpp_construct_temporary_expression(
                static_cast<CppConstructExpr*>(expr), expr->location);
        case StmtKind::CondExpr:
            return convert_conditional_expr(static_cast<CondExpr*>(expr));
        case StmtKind::UnaryOperation:
            return convert_unary_expr(static_cast<UnaryOperation*>(expr));
        case StmtKind::BinaryOperation:
            return convert_binary_expr(static_cast<BinaryOperation*>(expr));
        case StmtKind::CompoundAssignOperation:
            return convert_compound_assignment(
                static_cast<CompoundAssignOperation*>(expr));
        case StmtKind::ImplicitCast:
            return convert_implicit_cast(static_cast<ImplicitCast*>(expr));
        case StmtKind::ExplicitCast:
            return convert_explicit_cast(static_cast<ExplicitCast*>(expr));
        case StmtKind::MemberExpr:
            return convert_member_expr(static_cast<MemberExpr*>(expr));
        case StmtKind::MemberPointerLiteralExpr:
            return convert_member_pointer_literal_expr(
                static_cast<MemberPointerLiteralExpr*>(expr));
        case StmtKind::MemberPointerAccessExpr:
            return convert_member_pointer_access_expr(
                static_cast<MemberPointerAccessExpr*>(expr));
        case StmtKind::ArraySubscriptExpr: {
            auto* subscript = static_cast<ArraySubscriptExpr*>(expr);
            auto array_type = subscript->array ? subscript->array->get_type() : QualType();
            if (canonical_type_kind(array_type, ast_ctx.get()) == TypeKind::Vector) {
                llvm::Value* vec = convert_expression(subscript->array.get());
                llvm::Value* idx = convert_expression(subscript->index.get());
                if (!vec || !idx) {
                    return nullptr;
                }
                return builder.CreateExtractElement(vec, idx, "vec_extract");
            }

            auto lvalue_tup = get_lvalue(subscript);
            llvm::Value* ptr = lvalue_tup.address;
            auto ctype = lvalue_tup.type;
            if (!ptr || !ctype) {
                return nullptr;
            }

            llvm::Type* value_type = convert_type(ctype);
            if (!value_type) {
                error("convert_expression(): failed to lower array subscript type",
                      expr->location);
                return nullptr;
            }
            auto* load = builder.CreateLoad(value_type, ptr, "subscript_load");
            apply_load_qualifiers(load, expr->get_type(), module->getDataLayout());
            return load;
        }
        case StmtKind::InitListExpr:
            return convert_init_list_rvalue_expression(
                static_cast<InitListExpr*>(expr), expr->location);
        case StmtKind::CompoundLiteralExpr:
            return convert_compound_literal(static_cast<CompoundLiteralExpr*>(expr));
        case StmtKind::SizeOfExpr:
            return convert_sizeof_expr(static_cast<SizeOfExpr*>(expr));
        case StmtKind::AlignOfExpr:
            return convert_alignof_expr(static_cast<AlignOfExpr*>(expr));
        case StmtKind::OffsetOfExpr:
            return convert_offsetof_expr(static_cast<OffsetOfExpr*>(expr));
        case StmtKind::StmtExpr:
            return convert_stmt_expr(static_cast<StmtExpr*>(expr));
        case StmtKind::VaArgExpr:
            return convert_va_arg_expr(static_cast<VaArgExpr*>(expr));
        case StmtKind::VaStartExpr:
            return convert_va_start_expr(static_cast<VaStartExpr*>(expr));
        case StmtKind::VaEndExpr:
            return convert_va_end_expr(static_cast<VaEndExpr*>(expr));
        case StmtKind::VaCopyExpr:
            return convert_va_copy_expr(static_cast<VaCopyExpr*>(expr));
        case StmtKind::BuiltinCallExpr:
            return convert_builtin_call_expr(static_cast<BuiltinCallExpr*>(expr));
        case StmtKind::CppTypeIdExpr:
            return convert_cpp_typeid_expression(static_cast<CppTypeIdExpr*>(expr));
        case StmtKind::CppDynamicCastExpr:
            return materialize_reference_rvalue(
                expr,
                convert_cpp_dynamic_cast_expression(
                    static_cast<CppDynamicCastExpr*>(expr)),
                "convert_expression(): dynamic_cast");
        case StmtKind::CppThrowExpr:
            return convert_cpp_throw_expression(static_cast<CppThrowExpr*>(expr));
        case StmtKind::CppNewExpr:
            return convert_cpp_new_expression(static_cast<CppNewExpr*>(expr));
        case StmtKind::CppDeleteExpr:
            return convert_cpp_delete_expression(static_cast<CppDeleteExpr*>(expr));
        case StmtKind::BlockExpr:
            return convert_block_expression(static_cast<BlockExpr*>(expr));
        case StmtKind::CppLambdaExpr: {
            auto* lambda = static_cast<CppLambdaExpr*>(expr);
            if (lambda->semantic_info.closure_record()) {
                convert_declaration(lambda->semantic_info.closure_record());
            } else if (lambda->semantic_info.call_operator_decl) {
                convert_function_declaration(
                    lambda->semantic_info.call_operator_decl);
            }
            if (lambda->semantic_info.closure_initializer) {
                return convert_expression(
                    lambda->semantic_info.closure_initializer.get());
            }
            if (lambda->closure_info.default_capture != CppLambdaCaptureDefault::None ||
                !lambda->closure_info.captures.empty()) {
                error("convert_expression(): lambda captures are not implemented yet",
                      expr->location);
                return nullptr;
            }
            llvm::Type* closure_type = convert_type(expr->get_type());
            if (!closure_type) {
                error("convert_expression(): invalid lambda closure type",
                      expr->location);
                return nullptr;
            }
            if (auto* aggregate_type =
                    llvm::dyn_cast<llvm::StructType>(closure_type)) {
                return llvm::ConstantAggregateZero::get(aggregate_type);
            }
            return llvm::Constant::getNullValue(closure_type);
        }
        case StmtKind::GenericExpr:
        case StmtKind::ErrorExpr:
        default:
            break;
    }

    throw std::runtime_error("unimplemented convert_expression in ASTToLLVM");
}

llvm::Value* ASTToLLVM::convert_label_address_expr(LabelAddressExpr *expr) {
    llvm::Function* function = nullptr;
    if (builder.GetInsertBlock()) {
        function = builder.GetInsertBlock()->getParent();
    }
    if (!function) {
        error("convert_label_address_expr(): not inside a function", expr->location);
        return nullptr;
    }
    std::string label = mangleCIdentifier(expr->label);
    auto it = label_blocks.find(label);
    if (it == label_blocks.end()) {
        error("convert_label_address_expr(): unknown label: " + expr->label, expr->location);
        return nullptr;
    }
    llvm::BasicBlock* labelBB = it->second;
    if (labelBB->getParent() == nullptr) {
        function->insert(function->end(), labelBB);
    }
    return llvm::BlockAddress::get(function, labelBB);
}
