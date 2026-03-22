#include "collect.h"
#include "collect_decl_internal.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"
#include <algorithm>
#include <cerrno>
#include <functional>
#include <cstdlib>
#include <limits>
#include <sstream>

using namespace collect_decl_internal;

std::unique_ptr<Decl> Collect::collect_nop_declaration(SrcLoc loc) const {

    return collect_make<NopDecl>(loc);
}


std::unique_ptr<Decl> Collect::collect_typedef_declaration(const std::string& name, QualType type, std::shared_ptr<Symbol> sym, SrcLoc loc) const {

    return collect_make<TypedefDecl>(name, std::move(type), std::move(sym), loc);
}



std::unique_ptr<FuncDecl> Collect::collect_function_declaration(const std::string& name, std::shared_ptr<CType> type, StorageClass storage_class, bool is_inline, std::optional<std::string> asm_label, SrcLoc loc, LanguageLinkage language_linkage) const {

    QualType fn_type(type);
    if (contains_deferred_semantic_type(fn_type.get_shared())) {
        fn_type = resolve_typeof_types(fn_type, loc);
    }
    auto semantic_fn_type = desugar_type(fn_type, ast_ctx_.get());
    auto decl = collect_make<FuncDecl>();
    decl->location = loc;
    decl->name = name;
    decl->type = semantic_fn_type ? semantic_fn_type.get_shared() : fn_type.get_shared();
    decl->storage_class = storage_class;
    decl->is_inline = is_inline;
    decl->set_asm_label(std::move(asm_label));
    decl->set_language_linkage(language_linkage);
    return decl;
}


std::unique_ptr<Decl> Collect::collect_field_declaration(QualType type, const std::string& name, SrcLoc loc) const {

    if (type && contains_deferred_semantic_type(type.get_shared())) {
        type = resolve_typeof_types(type, loc);
    }
    if (!type) {
        report_error("field has unknown type", loc);
    } else {
        auto canonical = desugar_type(type, ast_ctx_.get());
        auto canonical_kind = canonical ? canonical->kind : TypeKind::Other;
        if (canonical_kind == TypeKind::Function) {
            report_error("field cannot have function type", loc);
        }
        if (canonical_kind == TypeKind::Array) {
            auto arr = canonical.as_shared<ArrayType>();
            if (arr && arr->element_type && arr->element_type->kind == TypeKind::Function) {
                report_error("array elements cannot have function type", loc);
            }
        }
    }
    return collect_make<FieldDecl>(std::move(type), name, loc);
}


std::unique_ptr<Decl> Collect::collect_field_declaration(QualType type, const std::string& name, uint32_t bitfield_width, SrcLoc loc) const {

    if (type && contains_deferred_semantic_type(type.get_shared())) {
        type = resolve_typeof_types(type, loc);
    }
    if (!type) {
        report_error("bitfield has unknown type", loc);
    } else {
        auto canonical = desugar_type(type, ast_ctx_.get());
        auto canonical_kind = canonical ? canonical->kind : TypeKind::Other;
        if (!canonical->isInteger() && canonical_kind != TypeKind::Enum) {
            report_error("bitfield must have integer type", loc);
        }
        int64_t type_width = canonical->getWidth();
        if (type_width > 0 && bitfield_width > static_cast<uint32_t>(type_width)) {
            report_error("bitfield width (" + std::to_string(bitfield_width) +
                ") exceeds type width (" + std::to_string(type_width) + ")", loc);
        }
        auto builtin = canonical.as_shared<BuiltinType>();
        if (builtin && builtin->builtin_kind == BuiltinTypes::Bool && bitfield_width > 1) {
            report_error("_Bool bitfield width cannot exceed 1", loc);
        }
    }
    if (bitfield_width == 0 && !name.empty()) {
        report_error("zero-width bitfield must be anonymous", loc);
    }
    return collect_make<FieldDecl>(std::move(type), name, bitfield_width, loc);
}


std::unique_ptr<ObjectDecl> Collect::collect_record_declaration(std::string tag, std::vector<std::unique_ptr<Decl>> fields, std::shared_ptr<CType> record_type, bool is_union, SrcLoc loc) const {

    auto decl = collect_make<ObjectDecl>(std::move(tag), std::move(fields), std::move(record_type), is_union, loc);
    return decl;
}


std::unique_ptr<ObjectDecl> Collect::collect_record_declaration(std::string tag, std::shared_ptr<CType> record_type, bool is_union, SrcLoc loc) const {

    auto decl = collect_make<ObjectDecl>(std::move(tag), std::move(record_type), is_union, loc);
    return decl;
}


std::unique_ptr<EnumConstantDecl> Collect::collect_enum_constant_declaration(std::string name, std::unique_ptr<Expr> init, SrcLoc loc) const {

    return collect_make<EnumConstantDecl>(std::move(name), std::move(init), loc);
}


std::unique_ptr<EnumDecl> Collect::collect_enum_declaration(std::string tag, std::vector<std::unique_ptr<EnumConstantDecl>> constants, std::shared_ptr<CType> enum_type, SrcLoc loc) const {

    return collect_make<EnumDecl>(std::move(tag), std::move(constants), std::move(enum_type), loc);
}


std::unique_ptr<EnumDecl> Collect::collect_enum_declaration(std::string tag, std::shared_ptr<CType> enum_type, SrcLoc loc) const {

    return collect_make<EnumDecl>(std::move(tag), std::move(enum_type), loc);
}
