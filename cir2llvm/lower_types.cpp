#include "lowerer.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

#include <llvm/ADT/ArrayRef.h>
#include <llvm/IR/DerivedTypes.h>

#include "../cir/layout.h"

namespace aburi::cir2llvm {

llvm::ConstantInt* Lowerer::constant_usize(uint64_t value) {
    return llvm::ConstantInt::get(llvm::IntegerType::get(context(),
                                                         static_cast<unsigned>(pointer_bits())),
                                 value,
                                 false);
}

bool Lowerer::is_nullptr_type(cir::TypeId type_id) const {
    type_id = file_.resolved_type(type_id);
    if (!file_.valid(type_id) ||
        file_.type(type_id).kind != cir::TypeKind::Builtin) {
        return false;
    }
    const auto* builtin =
        std::get_if<cir::BuiltinTypePayload>(&file_.type_payload(type_id));
    return builtin && builtin->kind == cir::BuiltinTypeKind::NullPtr;
}

llvm::StructType* Lowerer::llvm_nullptr_carrier_type() {
    llvm::Type* fields[] = {llvm::PointerType::get(context(), 0)};
    return llvm::StructType::get(context(), llvm::ArrayRef<llvm::Type*>(fields));
}

llvm::Constant* Lowerer::llvm_nullptr_carrier_value() {
    return llvm::ConstantStruct::get(
        llvm_nullptr_carrier_type(),
        {llvm::ConstantPointerNull::get(llvm::PointerType::get(context(), 0))});
}

llvm::Type* Lowerer::llvm_type(cir::TypeRef ref) {
    return llvm_type(ref.type);
}

llvm::Type* Lowerer::llvm_type(cir::TypeId type_id) {
    if (!file_.valid(type_id)) {
        return llvm::Type::getInt8Ty(context());
    }
    type_id = file_.resolved_type(type_id);
    const cir::Type& type = file_.type(type_id);
    const cir::TypePayload& payload = file_.type_payload(type_id);
    switch (type.kind) {
        case cir::TypeKind::Builtin:
            return llvm_builtin_type(std::get<cir::BuiltinTypePayload>(payload).kind);
        case cir::TypeKind::Pointer:
        case cir::TypeKind::BlockPointer:

        case cir::TypeKind::LValueReference:
        case cir::TypeKind::RValueReference:
            return llvm::PointerType::get(context(), 0);
        case cir::TypeKind::MemberPointer:
            if (file_.member_pointer_points_to_function(type_id)) {
                return llvm_member_function_pointer_type();
            }
            return llvm::IntegerType::get(context(),
                                          static_cast<unsigned>(pointer_bits()));
        case cir::TypeKind::Array: {
            const auto& array = std::get<cir::ArrayTypePayload>(payload);
            return llvm::ArrayType::get(llvm_type(array.element_type),
                                        static_cast<uint64_t>(*array.size));
        }
        case cir::TypeKind::Function:
            return llvm_function_type(type_id);
        case cir::TypeKind::Record: {
            const cir::RecordFacts* facts = file_.record_facts_for_type(type_id);
            if (!facts || facts->is_incomplete) {
                return llvm::ArrayType::get(llvm::Type::getInt8Ty(context()), 1);
            }
            uint64_t size = static_cast<uint64_t>((facts->size_bits + 7) / 8);
            return llvm::ArrayType::get(llvm::Type::getInt8Ty(context()),
                                        std::max<uint64_t>(1, size));
        }
        case cir::TypeKind::Enum: {
            const auto& enum_payload = std::get<cir::EnumTypePayload>(payload);
            return enum_payload.underlying_type.valid()
                ? llvm_type(enum_payload.underlying_type)
                : llvm::Type::getInt32Ty(context());
        }
        case cir::TypeKind::Vector: {
            const auto& vector = std::get<cir::VectorTypePayload>(payload);
            return llvm::FixedVectorType::get(llvm_type(vector.element_type),
                                              vector.element_count);
        }
        case cir::TypeKind::Complex: {
            const auto& complex = std::get<cir::ComplexTypePayload>(payload);
            return llvm::ArrayType::get(llvm_type(complex.element_type), 2);
        }
        case cir::TypeKind::BitInt: {
            const auto& bit_int = std::get<cir::BitIntTypePayload>(payload);
            return llvm::IntegerType::get(context(), bit_int.bits);
        }
        case cir::TypeKind::Typedef:
            return llvm_type(std::get<cir::TypedefTypePayload>(payload).underlying_type);
        case cir::TypeKind::Place:
            return llvm::PointerType::get(context(), 0);
        default:
            return llvm::Type::getInt8Ty(context());
    }
}

llvm::Type* Lowerer::llvm_builtin_type(cir::BuiltinTypeKind kind) {
    switch (kind) {
        case cir::BuiltinTypeKind::Void:
            return llvm::Type::getVoidTy(context());
        case cir::BuiltinTypeKind::NullPtr:
            return llvm_nullptr_carrier_type();
        case cir::BuiltinTypeKind::MetaInfo:

            return llvm::IntegerType::get(context(), options_.target->pointer_width);
        case cir::BuiltinTypeKind::Bool:
            return llvm::Type::getInt1Ty(context());
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
            return llvm::Type::getInt8Ty(context());
        case cir::BuiltinTypeKind::WChar:
            return llvm::IntegerType::get(context(), options_.target->wchar_width);
        case cir::BuiltinTypeKind::Char16:
        case cir::BuiltinTypeKind::Short:
        case cir::BuiltinTypeKind::UShort:
            return llvm::Type::getInt16Ty(context());
        case cir::BuiltinTypeKind::Char32:
        case cir::BuiltinTypeKind::Int:
        case cir::BuiltinTypeKind::UInt:
            return llvm::Type::getInt32Ty(context());
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::ULong:
            return llvm::IntegerType::get(context(), options_.target->long_width);
        case cir::BuiltinTypeKind::LongLong:
        case cir::BuiltinTypeKind::ULongLong:
            return llvm::Type::getInt64Ty(context());
        case cir::BuiltinTypeKind::Int128:
        case cir::BuiltinTypeKind::UInt128:
            return llvm::IntegerType::get(context(), 128);
        case cir::BuiltinTypeKind::USize:
            return llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()));
        case cir::BuiltinTypeKind::Float16:
            return llvm::Type::getHalfTy(context());
        case cir::BuiltinTypeKind::Float:
            return llvm::Type::getFloatTy(context());
        case cir::BuiltinTypeKind::Double:
            return llvm::Type::getDoubleTy(context());
        case cir::BuiltinTypeKind::LongDouble:
            if (options_.target->long_double_format == LongDoubleFormat::IEEE_QUAD) {
                return llvm::Type::getFP128Ty(context());
            }
            if (options_.target->long_double_format == LongDoubleFormat::X87_EXTENDED) {
                return llvm::Type::getX86_FP80Ty(context());
            }
            return llvm::Type::getDoubleTy(context());
        case cir::BuiltinTypeKind::Other:
            return llvm::Type::getInt8Ty(context());
    }
}

llvm::StructType* Lowerer::llvm_member_function_pointer_type() {
    return llvm::StructType::get(
        context(),
        {llvm::PointerType::get(context(), 0),
         llvm::IntegerType::get(context(), static_cast<unsigned>(pointer_bits()))});
}

llvm::FunctionType* Lowerer::llvm_function_type(cir::TypeId type_id) {
    return classify_function_abi(type_id).llvm_type;
}

std::optional<std::pair<uint64_t, uint64_t>> Lowerer::builtin_size_align(
    cir::BuiltinTypeKind kind) const {
    switch (kind) {
        case cir::BuiltinTypeKind::Void:
            return std::pair<uint64_t, uint64_t>{1, 1};
        case cir::BuiltinTypeKind::NullPtr:
        case cir::BuiltinTypeKind::MetaInfo:
            return std::pair<uint64_t, uint64_t>{pointer_bytes(), pointer_bytes()};
        case cir::BuiltinTypeKind::Bool:
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar:
        case cir::BuiltinTypeKind::UChar:
        case cir::BuiltinTypeKind::Char8:
            return std::pair<uint64_t, uint64_t>{1, 1};
        case cir::BuiltinTypeKind::Char16:
        case cir::BuiltinTypeKind::Short:
        case cir::BuiltinTypeKind::UShort:
        case cir::BuiltinTypeKind::Float16:
            return std::pair<uint64_t, uint64_t>{2, 2};
        case cir::BuiltinTypeKind::WChar:
            return std::pair<uint64_t, uint64_t>{
                static_cast<uint64_t>(std::max(1, options_.target->wchar_width / 8)),
                static_cast<uint64_t>(std::max(1, options_.target->wchar_width / 8))};
        case cir::BuiltinTypeKind::Char32:
        case cir::BuiltinTypeKind::Int:
        case cir::BuiltinTypeKind::UInt:
        case cir::BuiltinTypeKind::Float:
            return std::pair<uint64_t, uint64_t>{4, 4};
        case cir::BuiltinTypeKind::Long:
        case cir::BuiltinTypeKind::ULong: {
            uint64_t bytes = static_cast<uint64_t>(std::max(1, options_.target->long_width / 8));
            return std::pair<uint64_t, uint64_t>{bytes, bytes};
        }
        case cir::BuiltinTypeKind::LongLong:
        case cir::BuiltinTypeKind::ULongLong:
        case cir::BuiltinTypeKind::Double:
            return std::pair<uint64_t, uint64_t>{8, 8};
        case cir::BuiltinTypeKind::Int128:
        case cir::BuiltinTypeKind::UInt128:
            return std::pair<uint64_t, uint64_t>{16, 16};
        case cir::BuiltinTypeKind::USize:
            return std::pair<uint64_t, uint64_t>{pointer_bytes(), pointer_bytes()};
        case cir::BuiltinTypeKind::LongDouble:
            if (options_.target->long_double_format == LongDoubleFormat::IEEE_DOUBLE) {
                return std::pair<uint64_t, uint64_t>{8, 8};
            }
            if (options_.target->long_double_format == LongDoubleFormat::X87_EXTENDED) {
                return std::pair<uint64_t, uint64_t>{16, 16};
            }
            return std::pair<uint64_t, uint64_t>{16, 16};
        case cir::BuiltinTypeKind::Other:
            return std::nullopt;
    }
}

std::optional<uint64_t> Lowerer::size_of_type(cir::TypeId type_id, SrcLoc loc) {
    auto size_align = size_align_of_type(type_id, loc);
    return size_align ? std::optional<uint64_t>(size_align->first) : std::nullopt;
}

std::optional<uint64_t> Lowerer::align_of_type(cir::TypeId type_id, SrcLoc loc) {

    if (!file_.valid(type_id)) {
        error("cannot query alignment of invalid type", loc);
        return std::nullopt;
    }
    if (auto align = cir::align_of_type(file_, type_id)) {
        return static_cast<uint64_t>(*align);
    }
    auto size_align = size_align_of_type(type_id, loc);
    return size_align ? std::optional<uint64_t>(size_align->second) : std::nullopt;
}

std::optional<std::pair<uint64_t, uint64_t>> Lowerer::size_align_of_type(cir::TypeId type_id,
                                                                SrcLoc loc) {
    if (!file_.valid(type_id)) {
        error("cannot query size of invalid type", loc);
        return std::nullopt;
    }
    auto size_align = cir::size_align_of_type(file_, type_id);
    if (!size_align) {
        cir::TypeId resolved = file_.resolved_type(type_id);
        std::string type_name = file_.valid(resolved)
            ? std::string(cir::type_kind_name(file_.type(resolved).kind))
            : "invalid";
        error("cannot query size of unsupported or incomplete type '" +
                  type_name + "'",
              loc);
        return std::nullopt;
    }
    return std::pair<uint64_t, uint64_t>{
        static_cast<uint64_t>(size_align->size_bytes),
        static_cast<uint64_t>(size_align->alignment_bytes)};
}

} // namespace aburi::cir2llvm
