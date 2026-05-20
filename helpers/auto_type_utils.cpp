#include "auto_type_utils.h"

namespace auto_type_utils {

uint8_t auto_type_flavors_in(const std::shared_ptr<CType>& type) {
    if (!type) {
        return 0;
    }
    if (type->kind == TypeKind::Auto) {
        auto* auto_type = static_cast<AutoType*>(type.get());
        if (auto_type->flavor == AutoTypeFlavor::Gnu) {
            return kGnuAutoFlavor;
        }
        if (is_decltype_auto_flavor(auto_type->flavor)) {
            return kDecltypeAutoFlavor;
        }
        return kCxxAutoFlavor;
    }
    if (type->kind == TypeKind::Pointer) {
        auto ptr = std::static_pointer_cast<PointerType>(type);
        return auto_type_flavors_in(ptr->pointed_type.get_shared());
    }
    if (type->kind == TypeKind::Reference) {
        auto ref = std::static_pointer_cast<ReferenceType>(type);
        return auto_type_flavors_in(ref->referred_type.get_shared());
    }
    if (type->kind == TypeKind::BlockPointer) {
        auto blk = std::static_pointer_cast<BlockPointerType>(type);
        return auto_type_flavors_in(blk->pointed_type.get_shared());
    }
    if (type->kind == TypeKind::MemberPointer) {
        auto mem_ptr = std::static_pointer_cast<MemberPointerType>(type);
        return static_cast<uint8_t>(
            auto_type_flavors_in(mem_ptr->class_type.get_shared()) |
            auto_type_flavors_in(mem_ptr->member_type.get_shared()));
    }
    if (type->kind == TypeKind::Array) {
        auto arr = std::static_pointer_cast<ArrayType>(type);
        return auto_type_flavors_in(arr->element_type.get_shared());
    }
    if (type->kind == TypeKind::Typedef) {
        auto alias = std::static_pointer_cast<TypedefType>(type);
        return auto_type_flavors_in(alias->underlying_type.get_shared());
    }
    if (type->kind == TypeKind::Function) {
        auto func = std::static_pointer_cast<FunctionType>(type);
        uint8_t flags = auto_type_flavors_in(func->ret_type.get_shared());
        for (const auto& param : func->parameters) {
            flags = static_cast<uint8_t>(
                flags | auto_type_flavors_in(param.get_shared()));
        }
        return flags;
    }
    return 0;
}

std::shared_ptr<CType> retag_cxx_auto_placeholders(
    const std::shared_ptr<CType>& type,
    AutoTypeFlavor new_flavor) {
    if (!type) {
        return type;
    }
    if (type->kind == TypeKind::Auto) {
        auto* auto_type = static_cast<AutoType*>(type.get());
        if (auto_type->flavor == AutoTypeFlavor::Cxx) {
            return std::make_shared<AutoType>(new_flavor);
        }
        if (auto_type->flavor == AutoTypeFlavor::DecltypeAuto &&
            new_flavor == AutoTypeFlavor::TemplateNonType) {
            return std::make_shared<AutoType>(
                AutoTypeFlavor::DecltypeAutoTemplateNonType);
        }
        return type;
    }
    if (auto ptr = std::dynamic_pointer_cast<PointerType>(type)) {
        return std::make_shared<PointerType>(QualType(
            retag_cxx_auto_placeholders(ptr->pointed_type.get_shared(), new_flavor),
            ptr->pointed_type.get_qualifiers()));
    }
    if (auto ref = std::dynamic_pointer_cast<ReferenceType>(type)) {
        return std::make_shared<ReferenceType>(
            QualType(
                retag_cxx_auto_placeholders(ref->referred_type.get_shared(), new_flavor),
                ref->referred_type.get_qualifiers()),
            ref->reference_kind);
    }
    if (auto mem_ptr = std::dynamic_pointer_cast<MemberPointerType>(type)) {
        return std::make_shared<MemberPointerType>(
            QualType(
                retag_cxx_auto_placeholders(mem_ptr->class_type.get_shared(), new_flavor),
                mem_ptr->class_type.get_qualifiers()),
            QualType(
                retag_cxx_auto_placeholders(mem_ptr->member_type.get_shared(), new_flavor),
                mem_ptr->member_type.get_qualifiers()));
    }
    if (auto blk = std::dynamic_pointer_cast<BlockPointerType>(type)) {
        return std::make_shared<BlockPointerType>(
            QualType(
                retag_cxx_auto_placeholders(blk->pointed_type.get_shared(), new_flavor),
                blk->pointed_type.get_qualifiers()));
    }
    if (auto arr = std::dynamic_pointer_cast<ArrayType>(type)) {
        QualType elem(
            retag_cxx_auto_placeholders(arr->element_type.get_shared(), new_flavor),
            arr->element_type.get_qualifiers());
        if (arr->size_kind == ArraySizeKind::Variable) {
            return std::make_shared<ArrayType>(elem, arr->size_expr);
        }
        return std::make_shared<ArrayType>(elem, arr->size);
    }
    if (auto func = std::dynamic_pointer_cast<FunctionType>(type)) {
        auto rebuilt = std::make_shared<FunctionType>();
        rebuilt->ret_type = QualType(
            retag_cxx_auto_placeholders(func->ret_type.get_shared(), new_flavor),
            func->ret_type.get_qualifiers());
        rebuilt->parameters.reserve(func->parameters.size());
        for (const auto& param : func->parameters) {
            rebuilt->parameters.push_back(QualType(
                retag_cxx_auto_placeholders(param.get_shared(), new_flavor),
                param.get_qualifiers()));
        }
        rebuilt->parameter_pack_flags = func->parameter_pack_flags;
        rebuilt->normalize_parameter_pack_flags();
        rebuilt->is_variadic = func->is_variadic;
        rebuilt->has_prototype = func->has_prototype;
        rebuilt->member_ref_qualifier = func->member_ref_qualifier;
        rebuilt->has_explicit_exception_spec = func->has_explicit_exception_spec;
        rebuilt->exception_spec = func->exception_spec;
        return rebuilt;
    }
    if (auto alias = std::dynamic_pointer_cast<TypedefType>(type)) {
        return std::make_shared<TypedefType>(
            alias->name,
            QualType(
                retag_cxx_auto_placeholders(alias->underlying_type.get_shared(), new_flavor),
                alias->underlying_type.get_qualifiers()),
            alias->typedef_decl);
    }
    return type;
}

std::optional<QualType> extract_auto_placeholder_replacement(
    QualType pattern,
    QualType actual) {
    if (!pattern || !actual) {
        return std::nullopt;
    }
    if (pattern->kind == TypeKind::Auto) {
        return actual;
    }
    if (auto pattern_ptr = pattern.as_shared<PointerType>()) {
        auto actual_ptr = actual.as_shared<PointerType>();
        if (!actual_ptr) {
            return std::nullopt;
        }
        return extract_auto_placeholder_replacement(
            pattern_ptr->pointed_type,
            actual_ptr->pointed_type);
    }
    if (auto pattern_ref = pattern.as_shared<ReferenceType>()) {
        auto actual_ref = actual.as_shared<ReferenceType>();
        if (!actual_ref ||
            pattern_ref->reference_kind != actual_ref->reference_kind) {
            return std::nullopt;
        }
        return extract_auto_placeholder_replacement(
            pattern_ref->referred_type,
            actual_ref->referred_type);
    }
    if (auto pattern_mem_ptr = pattern.as_shared<MemberPointerType>()) {
        auto actual_mem_ptr = actual.as_shared<MemberPointerType>();
        if (!actual_mem_ptr) {
            return std::nullopt;
        }
        if (auto class_deduction = extract_auto_placeholder_replacement(
                pattern_mem_ptr->class_type,
                actual_mem_ptr->class_type)) {
            return class_deduction;
        }
        return extract_auto_placeholder_replacement(
            pattern_mem_ptr->member_type,
            actual_mem_ptr->member_type);
    }
    if (auto pattern_arr = pattern.as_shared<ArrayType>()) {
        auto actual_arr = actual.as_shared<ArrayType>();
        if (!actual_arr) {
            return std::nullopt;
        }
        return extract_auto_placeholder_replacement(
            pattern_arr->element_type,
            actual_arr->element_type);
    }
    if (auto pattern_blk = pattern.as_shared<BlockPointerType>()) {
        auto actual_blk = actual.as_shared<BlockPointerType>();
        if (!actual_blk) {
            return std::nullopt;
        }
        return extract_auto_placeholder_replacement(
            pattern_blk->pointed_type,
            actual_blk->pointed_type);
    }
    return std::nullopt;
}

std::shared_ptr<CType> replace_auto_placeholder(
    const std::shared_ptr<CType>& type,
    const std::shared_ptr<CType>& deduced) {
    if (!type || !deduced) {
        return type;
    }
    if (type->kind == TypeKind::Auto) {
        return deduced;
    }
    if (auto ptr = std::dynamic_pointer_cast<PointerType>(type)) {
        return std::make_shared<PointerType>(
            QualType(
                replace_auto_placeholder(ptr->pointed_type.get_shared(), deduced),
                ptr->pointed_type.get_qualifiers()));
    }
    if (auto ref = std::dynamic_pointer_cast<ReferenceType>(type)) {
        return std::make_shared<ReferenceType>(
            QualType(
                replace_auto_placeholder(ref->referred_type.get_shared(), deduced),
                ref->referred_type.get_qualifiers()),
            ref->reference_kind);
    }
    if (auto blk = std::dynamic_pointer_cast<BlockPointerType>(type)) {
        return std::make_shared<BlockPointerType>(
            QualType(
                replace_auto_placeholder(blk->pointed_type.get_shared(), deduced),
                blk->pointed_type.get_qualifiers()));
    }
    if (auto mem_ptr = std::dynamic_pointer_cast<MemberPointerType>(type)) {
        return std::make_shared<MemberPointerType>(
            QualType(
                replace_auto_placeholder(mem_ptr->class_type.get_shared(), deduced),
                mem_ptr->class_type.get_qualifiers()),
            QualType(
                replace_auto_placeholder(mem_ptr->member_type.get_shared(), deduced),
                mem_ptr->member_type.get_qualifiers()));
    }
    if (auto arr = std::dynamic_pointer_cast<ArrayType>(type)) {
        QualType elem(
            replace_auto_placeholder(arr->element_type.get_shared(), deduced),
            arr->element_type.get_qualifiers());
        if (arr->size_kind == ArraySizeKind::Variable) {
            return std::make_shared<ArrayType>(elem, arr->size_expr);
        }
        return std::make_shared<ArrayType>(elem, arr->size);
    }
    if (auto func = std::dynamic_pointer_cast<FunctionType>(type)) {
        auto rebuilt = std::make_shared<FunctionType>();
        rebuilt->ret_type = QualType(
            replace_auto_placeholder(func->ret_type.get_shared(), deduced),
            func->ret_type.get_qualifiers());
        rebuilt->parameters.reserve(func->parameters.size());
        for (const auto& param : func->parameters) {
            rebuilt->parameters.push_back(QualType(
                replace_auto_placeholder(param.get_shared(), deduced),
                param.get_qualifiers()));
        }
        rebuilt->parameter_pack_flags = func->parameter_pack_flags;
        rebuilt->normalize_parameter_pack_flags();
        rebuilt->is_variadic = func->is_variadic;
        rebuilt->has_prototype = func->has_prototype;
        rebuilt->member_ref_qualifier = func->member_ref_qualifier;
        rebuilt->has_explicit_exception_spec = func->has_explicit_exception_spec;
        rebuilt->exception_spec = func->exception_spec;
        return rebuilt;
    }
    if (auto alias = std::dynamic_pointer_cast<TypedefType>(type)) {
        return std::make_shared<TypedefType>(
            alias->name,
            QualType(
                replace_auto_placeholder(alias->underlying_type.get_shared(), deduced),
                alias->underlying_type.get_qualifiers()),
            alias->typedef_decl);
    }
    return type;
}

std::shared_ptr<CType> replace_cxx_auto_placeholders_with_callback(
    const std::shared_ptr<CType>& type,
    const std::function<QualType(size_t)>& replacement_for_placeholder,
    size_t* next_placeholder_index) {
    if (!type) {
        return type;
    }

    size_t local_placeholder_index = 0;
    if (!next_placeholder_index) {
        next_placeholder_index = &local_placeholder_index;
    }

    if (type->kind == TypeKind::Auto) {
        auto* auto_type = static_cast<AutoType*>(type.get());
        if (auto_type->flavor != AutoTypeFlavor::Cxx) {
            return type;
        }
        QualType replacement =
            replacement_for_placeholder
                ? replacement_for_placeholder((*next_placeholder_index)++)
                : QualType();
        if (!replacement) {
            return type;
        }
        return replacement.get_shared();
    }
    if (auto ptr = std::dynamic_pointer_cast<PointerType>(type)) {
        return std::make_shared<PointerType>(QualType(
            replace_cxx_auto_placeholders_with_callback(
                ptr->pointed_type.get_shared(),
                replacement_for_placeholder,
                next_placeholder_index),
            ptr->pointed_type.get_qualifiers()));
    }
    if (auto ref = std::dynamic_pointer_cast<ReferenceType>(type)) {
        return std::make_shared<ReferenceType>(
            QualType(
                replace_cxx_auto_placeholders_with_callback(
                    ref->referred_type.get_shared(),
                    replacement_for_placeholder,
                    next_placeholder_index),
                ref->referred_type.get_qualifiers()),
            ref->reference_kind);
    }
    if (auto mem_ptr = std::dynamic_pointer_cast<MemberPointerType>(type)) {
        return std::make_shared<MemberPointerType>(
            QualType(
                replace_cxx_auto_placeholders_with_callback(
                    mem_ptr->class_type.get_shared(),
                    replacement_for_placeholder,
                    next_placeholder_index),
                mem_ptr->class_type.get_qualifiers()),
            QualType(
                replace_cxx_auto_placeholders_with_callback(
                    mem_ptr->member_type.get_shared(),
                    replacement_for_placeholder,
                    next_placeholder_index),
                mem_ptr->member_type.get_qualifiers()));
    }
    if (auto blk = std::dynamic_pointer_cast<BlockPointerType>(type)) {
        return std::make_shared<BlockPointerType>(
            QualType(
                replace_cxx_auto_placeholders_with_callback(
                    blk->pointed_type.get_shared(),
                    replacement_for_placeholder,
                    next_placeholder_index),
                blk->pointed_type.get_qualifiers()));
    }
    if (auto arr = std::dynamic_pointer_cast<ArrayType>(type)) {
        QualType elem(
            replace_cxx_auto_placeholders_with_callback(
                arr->element_type.get_shared(),
                replacement_for_placeholder,
                next_placeholder_index),
            arr->element_type.get_qualifiers());
        if (arr->size_kind == ArraySizeKind::Variable) {
            return std::make_shared<ArrayType>(elem, arr->size_expr);
        }
        return std::make_shared<ArrayType>(elem, arr->size);
    }
    if (auto func = std::dynamic_pointer_cast<FunctionType>(type)) {
        auto rebuilt = std::make_shared<FunctionType>();
        rebuilt->ret_type = QualType(
            replace_cxx_auto_placeholders_with_callback(
                func->ret_type.get_shared(),
                replacement_for_placeholder,
                next_placeholder_index),
            func->ret_type.get_qualifiers());
        rebuilt->parameters.reserve(func->parameters.size());
        for (const auto& param : func->parameters) {
            rebuilt->parameters.push_back(QualType(
                replace_cxx_auto_placeholders_with_callback(
                    param.get_shared(),
                    replacement_for_placeholder,
                    next_placeholder_index),
                param.get_qualifiers()));
        }
        rebuilt->parameter_pack_flags = func->parameter_pack_flags;
        rebuilt->normalize_parameter_pack_flags();
        rebuilt->is_variadic = func->is_variadic;
        rebuilt->has_prototype = func->has_prototype;
        rebuilt->member_ref_qualifier = func->member_ref_qualifier;
        rebuilt->has_explicit_exception_spec =
            func->has_explicit_exception_spec;
        rebuilt->exception_spec = func->exception_spec;
        return rebuilt;
    }
    if (auto alias = std::dynamic_pointer_cast<TypedefType>(type)) {
        return std::make_shared<TypedefType>(
            alias->name,
            QualType(
                replace_cxx_auto_placeholders_with_callback(
                    alias->underlying_type.get_shared(),
                    replacement_for_placeholder,
                    next_placeholder_index),
                alias->underlying_type.get_qualifiers()),
            alias->typedef_decl);
    }
    return type;
}

} // namespace auto_type_utils
