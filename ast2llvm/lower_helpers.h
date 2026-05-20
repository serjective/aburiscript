#ifndef ABURI_AST2LLVM_LOWER_HELPERS_H
#define ABURI_AST2LLVM_LOWER_HELPERS_H

#include "ast2llvm.h"
#include "../helpers/casting.h"
#include "../constexpr/consteval_compat.h"
#include <optional>
#include <vector>
#include <string>

static std::optional<int64_t> eval_constexpr_i64(
    Expr* expr, ConstEvalMode mode = ConstEvalMode::c_ice()) {
    return try_evaluate_with_consteval_compat(expr, mode);
}

static bool record_uses_byte_layout(const ObjectType* record) {
    if (!record) {
        return false;
    }
    if (record->is_packed || record->pack_alignment > 0) {
        return true;
    }
    if (record->has_bitfields()) {
        return true;
    }
    for (const auto& field : record->semantic_fields()) {
        if (field.forced_alignment > 0 ||
            field.is_base_subobject ||
            field.storage_size_override > 0 ||
            field.storage_alignment_override > 0) {
            return true;
        }
    }
    return false;
}

static uint64_t semantic_type_alignment(const std::shared_ptr<CType>& type) {
    if (!type) {
        return 0;
    }
    auto canonical = desugar_type(type);
    if (!canonical) {
        return 0;
    }
    if (auto obj = dyn_cast_shared<ObjectType>(canonical)) {
        size_t align = obj->getAlignment();
        return align > 0 ? static_cast<uint64_t>(align) : 1;
    }
    if (auto arr = dyn_cast_shared<ArrayType>(canonical)) {
        return semantic_type_alignment(arr->element_type.get_shared());
    }
    if (auto vec = dyn_cast_shared<VectorType>(canonical)) {
        int64_t width = vec->getWidthBytes();
        return width > 0 ? static_cast<uint64_t>(width) : 1;
    }
    if (auto complex = dyn_cast_shared<ComplexType>(canonical)) {
        return semantic_type_alignment(complex->element_type);
    }
    if (auto enm = dyn_cast_shared<EnumType>(canonical)) {
        return semantic_type_alignment(enm->semantic_underlying_type());
    }
    int64_t size = canonical->getWidthBytes();
    return size > 0 ? static_cast<uint64_t>(size) : 1;
}

static size_t map_semantic_field_index_to_llvm_index(const ObjectType* record,
                                                      size_t semantic_index) {
    if (!record) {
        return semantic_index;
    }
    const auto& fields = record->semantic_fields();
    size_t current_offset = 0;
    size_t llvm_index = 0;
    for (size_t i = 0; i < fields.size(); ++i) {
        const auto& field = fields[i];
        if (field.offset > current_offset) {
            ++llvm_index;
            current_offset = field.offset;
        }
        if (i == semantic_index) {
            return llvm_index;
        }
        current_offset += object_field_storage_size_bytes(field);
        ++llvm_index;
    }
    return semantic_index;
}

static std::vector<uint32_t> decode_utf8_codepoints(const std::string& text) {
    std::vector<uint32_t> out;
    size_t i = 0;
    while (i < text.size()) {
        unsigned char c0 = static_cast<unsigned char>(text[i]);
        if ((c0 & 0x80) == 0) {
            out.push_back(c0);
            ++i;
            continue;
        }
        auto is_cont = [](unsigned char c) { return (c & 0xC0) == 0x80; };

        if ((c0 & 0xE0) == 0xC0 && i + 1 < text.size()) {
            unsigned char c1 = static_cast<unsigned char>(text[i + 1]);
            if (c0 >= 0xC2 && is_cont(c1)) {
                out.push_back(((c0 & 0x1F) << 6) | (c1 & 0x3F));
                i += 2;
                continue;
            }
        } else if ((c0 & 0xF0) == 0xE0 && i + 2 < text.size()) {
            unsigned char c1 = static_cast<unsigned char>(text[i + 1]);
            unsigned char c2 = static_cast<unsigned char>(text[i + 2]);
            if (is_cont(c1) && is_cont(c2)) {
                uint32_t cp = ((c0 & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
                bool overlong = cp < 0x800;
                bool surrogate = (cp >= 0xD800 && cp <= 0xDFFF);
                if (!overlong && !surrogate) {
                    out.push_back(cp);
                    i += 3;
                    continue;
                }
            }
        } else if ((c0 & 0xF8) == 0xF0 && i + 3 < text.size()) {
            unsigned char c1 = static_cast<unsigned char>(text[i + 1]);
            unsigned char c2 = static_cast<unsigned char>(text[i + 2]);
            unsigned char c3 = static_cast<unsigned char>(text[i + 3]);
            if (is_cont(c1) && is_cont(c2) && is_cont(c3)) {
                uint32_t cp = ((c0 & 0x07) << 18) | ((c1 & 0x3F) << 12) |
                              ((c2 & 0x3F) << 6) | (c3 & 0x3F);
                bool overlong = cp < 0x10000;
                if (!overlong && cp <= 0x10FFFF) {
                    out.push_back(cp);
                    i += 4;
                    continue;
                }
            }
        }

        out.push_back(c0);
        ++i;
    }
    return out;
}

// Strip outer LVALUE_TO_RVALUE implicit casts to reach the underlying lvalue.
// Used when binding references, which operate on lvalues rather than rvalues.
static Expr* unwrap_lvalue_to_rvalue_casts(Expr* expr) {
    Expr* current = expr;
    while (auto* cast = dyn_cast<ImplicitCast>(current)) {
        if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
            current = cast->expr.get();
            continue;
        }
        break;
    }
    return current;
}

// Strip frontend wrappers that do not change which object a reference binds to.
// This keeps the original object address for xvalue bindings such as
// static_cast<T&&>(obj) while preserving casts that must be lowered explicitly.
static Expr* unwrap_reference_binding_expr(Expr* expr) {
    Expr* current = expr;
    while (auto* cast = dyn_cast<ImplicitCast>(current)) {
        if (cast->kind == ImplicitCastTypes::LVALUE_TO_RVALUE) {
            current = cast->expr.get();
            continue;
        }
        if (cast->expr && cast->expr->isLValue()) {
            current = cast->expr.get();
            continue;
        }
        break;
    }
    return current;
}

// Apply volatile and atomic memory semantics to a load instruction.
// Must be called after CreateLoad to ensure memory model compliance.
static void apply_load_qualifiers(llvm::LoadInst* load, const QualType& type,
                                  const llvm::DataLayout& data_layout) {
    if (type.is_volatile()) {
        load->setVolatile(true);
    }
    if (type.is_atomic()) {
        load->setAtomic(llvm::AtomicOrdering::SequentiallyConsistent);
        load->setAlignment(llvm::Align(
            data_layout.getTypeAllocSize(load->getType())));
    }
}

// Apply volatile and atomic memory semantics to a store instruction.
// Must be called after CreateStore to ensure memory model compliance.
static void apply_store_qualifiers(llvm::StoreInst* store, const QualType& type,
                                   const llvm::DataLayout& data_layout) {
    if (type.is_volatile()) {
        store->setVolatile(true);
    }
    if (type.is_atomic()) {
        store->setAtomic(llvm::AtomicOrdering::SequentiallyConsistent);
        store->setAlignment(llvm::Align(
            data_layout.getTypeAllocSize(store->getValueOperand()->getType())));
    }
}

static const StringLiteral* unwrap_string_literal_expr(const Expr* expr) {
    const Expr* current = expr;
    while (current) {
        if (auto* str = dyn_cast<StringLiteral>(current)) {
            return str;
        }
        if (auto* paren = dyn_cast<ParenExpr>(current)) {
            current = paren->subexpr.get();
            continue;
        }
        if (auto* implicit_cast = dyn_cast<ImplicitCast>(current)) {
            current = implicit_cast->expr.get();
            continue;
        }
        if (auto* explicit_cast = dyn_cast<ExplicitCast>(current)) {
            current = explicit_cast->expr.get();
            continue;
        }
        break;
    }
    return nullptr;
}

static InitListExpr* unwrap_init_list_expr(Expr* expr) {
    Expr* current = expr;
    while (current) {
        if (auto* init = dyn_cast<InitListExpr>(current)) {
            return init;
        }
        if (auto* paren = dyn_cast<ParenExpr>(current)) {
            current = paren->subexpr.get();
            continue;
        }
        if (auto* implicit_cast = dyn_cast<ImplicitCast>(current)) {
            current = implicit_cast->expr.get();
            continue;
        }
        if (auto* explicit_cast = dyn_cast<ExplicitCast>(current)) {
            current = explicit_cast->expr.get();
            continue;
        }
        break;
    }
    return nullptr;
}

static bool resolve_member_access_base_subobject(
    ASTToLLVM& lower,
    MemberExpr* member,
    llvm::Value* base_ptr,
    std::shared_ptr<ObjectType> record_type,
    llvm::Value*& resolved_base_ptr,
    std::shared_ptr<ObjectType>& resolved_record_type) {
    resolved_base_ptr = base_ptr;
    resolved_record_type = std::move(record_type);
    if (!member || !base_ptr || !resolved_record_type ||
        !member->virtual_base_record_decl) {
        return true;
    }

    const ObjectDecl* context_record_decl = lower.canonical_cpp_record_decl(
        dyn_cast<ObjectDecl>(resolved_record_type->get_decl()));
    if (!context_record_decl) {
        lower.error("resolve_member_access_base_subobject(): missing member-access record declaration",
                    member->location);
        return false;
    }

    llvm::Value* adjusted_base_ptr = lower.resolve_cpp_virtual_base_subobject_address(
        base_ptr,
        context_record_decl,
        member->virtual_base_record_decl,
        member->location,
        "member access");
    if (!adjusted_base_ptr) {
        lower.error("resolve_member_access_base_subobject(): failed to resolve virtual-base subobject",
                    member->location);
        return false;
    }

    auto virtual_base_record_type =
        member->virtual_base_record_decl->get_record_type();
    auto virtual_base_object_type =
        virtual_base_record_type
            ? desugar_type(QualType(virtual_base_record_type), lower.ast_ctx.get())
                  .as_shared<ObjectType>()
            : nullptr;
    if (!virtual_base_object_type) {
        lower.error("resolve_member_access_base_subobject(): invalid virtual-base record type",
                    member->location);
        return false;
    }

    llvm::Type* llvm_record_type =
        lower.convert_type(virtual_base_object_type);
    if (!llvm_record_type) {
        lower.error("resolve_member_access_base_subobject(): failed to lower virtual-base record type",
                    member->location);
        return false;
    }

    llvm::Type* target_ptr_type = llvm::PointerType::get(llvm_record_type, 0);
    if (adjusted_base_ptr->getType() != target_ptr_type) {
        adjusted_base_ptr = lower.cast_llvm_type(
            adjusted_base_ptr,
            target_ptr_type,
            false);
    }

    resolved_base_ptr = adjusted_base_ptr;
    resolved_record_type = std::move(virtual_base_object_type);
    return true;
}

// Helper: constant-fold a cast from one LLVM constant to another type.
static llvm::Constant* fold_constant_cast(llvm::Constant* inner, llvm::Type* destTy,
                                          bool srcUnsigned, bool destUnsigned,
                                          const llvm::DataLayout& dataLayout) {
    if (inner->getType() == destTy) {
        return inner;
    }

    if (auto* ci = llvm::dyn_cast<llvm::ConstantInt>(inner)) {
        if (destTy->isFloatingPointTy()) {
            if (srcUnsigned) {
                double v = static_cast<double>(ci->getZExtValue());
                return llvm::ConstantFP::get(destTy, v);
            }
            double v = static_cast<double>(ci->getSExtValue());
            return llvm::ConstantFP::get(destTy, v);
        }
        if (destTy->isIntegerTy()) {
            unsigned destBits = destTy->getIntegerBitWidth();
            unsigned srcBits = ci->getType()->getIntegerBitWidth();
            if (destBits < srcBits) {
                return llvm::ConstantExpr::getTrunc(inner, destTy);
            }
            if (destBits > srcBits) {
                if (srcUnsigned) {
                    return llvm::ConstantInt::get(destTy, ci->getZExtValue());
                }
                return llvm::ConstantInt::getSigned(destTy, ci->getSExtValue());
            }
            return inner;
        }
        if (destTy->isPointerTy()) {
            auto* ptrTy = llvm::cast<llvm::PointerType>(destTy);
            unsigned ptrBits = dataLayout.getPointerSizeInBits(ptrTy->getAddressSpace());
            auto* ptrIntTy = llvm::IntegerType::get(inner->getContext(), ptrBits);
            llvm::Constant* intVal = inner;
            unsigned srcBits = ci->getType()->getIntegerBitWidth();
            if (srcBits < ptrBits) {
                llvm::APInt widened = srcUnsigned
                    ? ci->getValue().zext(ptrBits)
                    : ci->getValue().sext(ptrBits);
                intVal = llvm::ConstantInt::get(ptrIntTy, widened);
            } else if (srcBits > ptrBits) {
                intVal = llvm::ConstantInt::get(ptrIntTy, ci->getValue().trunc(ptrBits));
            }
            return llvm::ConstantExpr::getIntToPtr(intVal, destTy);
        }
    }

    if (auto* cf = llvm::dyn_cast<llvm::ConstantFP>(inner)) {
        double v = cf->getValueAPF().convertToDouble();
        if (destTy->isIntegerTy()) {
            if (destUnsigned) {
                return llvm::ConstantInt::get(destTy, static_cast<uint64_t>(v));
            }
            return llvm::ConstantInt::getSigned(destTy, static_cast<int64_t>(v));
        }
        if (destTy->isFloatingPointTy()) {
            return llvm::ConstantFP::get(destTy, v);
        }
    }

    if (inner->getType()->isPointerTy() && destTy->isPointerTy()) {
        return inner;
    }
    if (inner->getType()->isPointerTy() && destTy->isIntegerTy()) {
        return llvm::ConstantExpr::getPtrToInt(inner, destTy);
    }

    return nullptr;
}

#endif
