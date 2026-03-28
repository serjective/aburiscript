#include "collect.h"
#include "collect_decl_internal.h"
#include "../ast/expr_clone.h"
#include "../helpers/qualified_name_utils.h"
#include "../ast/special_members.h"
#include "lookup_engine.h"
#include <algorithm>
#include <cerrno>
#include <functional>
#include <cstdlib>
#include <limits>
#include <sstream>

using namespace collect_decl_internal;

std::shared_ptr<Symbol> Collect::collect_declare_variable_symbol(std::shared_ptr<Scope> scope, std::shared_ptr<GlobalIdentTracker> global_scope, const std::string& name, QualType type, StorageClass storage_class, bool is_constexpr, SrcLoc loc, LanguageLinkage language_linkage) {

    if (!scope || name.empty()) {
        return nullptr;
    }
    materialize_tentative_snapshot_if_needed();
    if (contains_deferred_semantic_type(type.get_shared())) {
        type = resolve_typeof_types(type, loc);
    }
    type = desugar_type(type, ast_ctx_.get());
    if (is_constexpr && type) {
        type = type.with_const();
    }
    bool is_file_scope = is_file_or_namespace_scope(scope);
    if (is_file_scope && storage_class == StorageClass::AUTO) {
        report_error("illegal storage class 'auto' for file-scope declaration", loc);
    }
    if (is_file_scope && storage_class == StorageClass::REGISTER) {
        report_error("register storage class specifier used at file scope", loc);
    }
    if (storage_class == StorageClass::TYPEDEF) {
        report_error("typedef storage class is not valid for variable declaration", loc);
    }
    if (is_constexpr && storage_class == StorageClass::EXTERN) {
        report_error("'constexpr' cannot be combined with 'extern'", loc);
    }
    if (is_constexpr && storage_class == StorageClass::AUTO) {
        report_error("'constexpr' cannot be combined with 'auto'", loc);
    }
    const bool is_cxx_mode = lang_opts_.is_cxx_mode();
    const LanguageLinkage requested_language_linkage =
        effective_language_linkage(language_linkage, is_cxx_mode);
    auto report_linkage_conflict_if_any = [&](const std::shared_ptr<Symbol>& sym) -> bool {
        if (!sym) {
            return false;
        }
        LanguageLinkage existing_linkage =
            effective_language_linkage(sym->get_language_linkage(), is_cxx_mode);
        if (existing_linkage != requested_language_linkage) {
            report_error("conflicting language linkage for '" + name + "'", loc);
            return true;
        }
        return false;
    };
    auto merge_language_linkage = [&](const std::shared_ptr<Symbol>& sym) {
        if (!sym) {
            return;
        }
        if (sym->get_language_linkage() == LanguageLinkage::None) {
            sym->set_language_linkage(requested_language_linkage);
        }
    };
    auto are_compatible_variable_types = [&](QualType lhs, QualType rhs) -> bool {
        lhs = desugar_type(lhs, ast_ctx_.get());
        rhs = desugar_type(rhs, ast_ctx_.get());
        if (!lhs || !rhs) {
            return lhs.get_shared() == rhs.get_shared();
        }
        if (lhs.equals_qualified(rhs)) {
            return true;
        }
        auto lhs_arr = lhs.as_shared<ArrayType>();
        auto rhs_arr = rhs.as_shared<ArrayType>();
        if (lhs_arr && rhs_arr) {
            if (lhs.get_qualifiers() != rhs.get_qualifiers()) {
                return false;
            }
            if (!lhs_arr->element_type.equals_qualified(rhs_arr->element_type)) {
                return false;
            }
            bool lhs_const = (lhs_arr->size_kind == ArraySizeKind::Constant && lhs_arr->size.has_value());
            bool rhs_const = (rhs_arr->size_kind == ArraySizeKind::Constant && rhs_arr->size.has_value());
            if (lhs_const && rhs_const) {
                return lhs_arr->size.value() == rhs_arr->size.value();
            }
            return true;
        }
        return false;
    };
    auto reconcile_array_redeclaration_types = [&](QualType& existing_type, QualType& new_type) {
        existing_type = desugar_type(existing_type, ast_ctx_.get());
        new_type = desugar_type(new_type, ast_ctx_.get());
        auto existing_arr = existing_type.as_shared<ArrayType>();
        auto new_arr = new_type.as_shared<ArrayType>();
        if (!existing_arr || !new_arr) {
            return;
        }
        if (existing_type.get_qualifiers() != new_type.get_qualifiers()) {
            return;
        }
        if (!existing_arr->element_type.equals_qualified(new_arr->element_type)) {
            return;
        }
        bool existing_complete =
            existing_arr->size_kind == ArraySizeKind::Constant && existing_arr->size.has_value();
        bool new_complete =
            new_arr->size_kind == ArraySizeKind::Constant && new_arr->size.has_value();
        if (!existing_complete && new_complete) {
            existing_type = new_type;
        } else if (existing_complete && !new_complete) {
            new_type = existing_type;
        }
    };
    auto existing = lookup_ordinary_symbol(scope, name, false);
    if (existing) {
        if (existing->kind == SymbolKind::VARIABLE) {
            bool same_type = false;
            same_type = are_compatible_variable_types(existing->type, type);
            if (!same_type) {
                report_error("conflicting types for '" + name + "'", loc);
            }
            report_linkage_conflict_if_any(existing);
            reconcile_array_redeclaration_types(existing->type, type);
            bool both_extern = (existing->storage_class == StorageClass::EXTERN &&
                storage_class == StorageClass::EXTERN);
            bool redeclares_linked_visible_symbol =
                (!is_file_scope &&
                 storage_class == StorageClass::EXTERN &&
                 existing->linkage != VariableLinkage::NONE);
            if (!is_file_scope && !both_extern && !redeclares_linked_visible_symbol) {
                report_error("redefinition of '" + name + "'", loc);
            }
            if (is_file_scope && existing->is_constexpr && is_constexpr) {
                report_error("redefinition of '" + name + "'", loc);
            }
            if (existing->is_constexpr != is_constexpr) {
                report_error("conflicting constexpr specifier for '" + name + "'", loc);
            }
            if (is_file_scope) {
                if (existing->linkage == VariableLinkage::INTERNAL &&
                    storage_class == StorageClass::EXTERN) {
                    // Keep internal linkage from prior static declaration.
                } else if (existing->linkage == VariableLinkage::EXTERNAL &&
                    storage_class == StorageClass::STATIC) {
                    report_error("static declaration of '" + name + "' follows non-static declaration", loc);
                }
            }
            if (is_file_scope && existing->storage_class == StorageClass::EXTERN &&
                storage_class != StorageClass::EXTERN) {
                existing->storage_class = storage_class;
            }
            merge_language_linkage(existing);
            return existing;
        }
        if (existing->kind == SymbolKind::ENUM_CONSTANT) {
            report_error("redefinition of enum constant '" + name + "'", loc);
            return existing;
        }
        report_error("redefinition of '" + name + "' as variable", loc);
        return existing;
    }
    // C11 6.2.2p4: block-scope extern + visible prior declaration with linkage
    // must denote the same object.
    if (!is_file_scope && storage_class == StorageClass::EXTERN) {
        auto visible = lookup_ordinary_symbol(scope, name, true);
        if (visible && visible->kind == SymbolKind::VARIABLE &&
            visible->linkage != VariableLinkage::NONE) {
            bool same_type = are_compatible_variable_types(visible->type, type);
            if (!same_type) {
                report_error("conflicting types for '" + name + "'", loc);
            }
            report_linkage_conflict_if_any(visible);
            if (visible->is_constexpr != is_constexpr) {
                report_error("conflicting constexpr specifier for '" + name + "'", loc);
            }
            reconcile_array_redeclaration_types(visible->type, type);
            merge_language_linkage(visible);
            bind_symbol_in_scope(scope, name, visible);
            return visible;
        }
    }
    VariableLinkage linkage = VariableLinkage::NONE;
    if (storage_class == StorageClass::EXTERN) {
        linkage = VariableLinkage::EXTERNAL;
    } else if (storage_class == StorageClass::STATIC) {
        linkage = is_file_scope ? VariableLinkage::INTERNAL : VariableLinkage::NONE;
    } else if (is_file_scope) {
        linkage = VariableLinkage::EXTERNAL;
    }
    auto sym = std::make_shared<Symbol>(name, SymbolKind::VARIABLE, std::move(type), storage_class, linkage);
    sym->is_constexpr = is_constexpr;
    sym->set_language_linkage(requested_language_linkage);
    if (global_scope) {
        record_global_scope_mutation(global_scope);
        global_scope->add_to_global_scope(sym);
    }
    bind_symbol_in_scope(scope, name, sym);
    return sym;
}


std::shared_ptr<Symbol> Collect::collect_declare_variable_symbol(const std::string& name, QualType type, StorageClass storage_class, bool is_constexpr, SrcLoc loc, LanguageLinkage language_linkage) {

    return collect_declare_variable_symbol(session_.current_scope_, session_.current_global_scope_, name, type, storage_class, is_constexpr, loc, language_linkage);
}


std::shared_ptr<Symbol> Collect::collect_declare_function_symbol(std::shared_ptr<Scope> scope, std::shared_ptr<GlobalIdentTracker> global_scope, const std::string& name, QualType type, StorageClass storage_class, bool is_inline, bool is_definition, SrcLoc loc, LanguageLinkage language_linkage, bool is_cpp_member_function) {

    if (!scope || name.empty()) {
        return nullptr;
    }
    materialize_tentative_snapshot_if_needed();
    if (contains_deferred_semantic_type(type.get_shared())) {
        type = resolve_typeof_types(type, loc);
    }
    type = desugar_type(type, ast_ctx_.get());
    auto effective_decl_scope = scope;
    while (effective_decl_scope &&
           scope_flags_contains(effective_decl_scope->flags,
                                ScopeFlags::TemplateParameterScope) &&
           effective_decl_scope->parent) {
        effective_decl_scope = effective_decl_scope->parent;
    }
    bool is_file_scope = is_file_or_namespace_scope(effective_decl_scope);
    auto namespace_prefix_for_scope = [](const std::shared_ptr<Scope>& scope)
        -> std::optional<std::string> {
        return qualified_name_utils::namespace_prefix_from_scope(scope);
    };
    auto decl_scope = effective_decl_scope ? effective_decl_scope : scope;
    if (!is_file_scope && !is_definition && !is_cpp_member_function) {
        while (decl_scope && decl_scope->parent) {
            decl_scope = decl_scope->parent;
        }
        if (!decl_scope) {
            decl_scope = scope;
        }
    }
    if (decl_scope != scope) {
        auto local_existing = lookup_ordinary_symbol(scope, name, false);
        if (local_existing && local_existing->kind != SymbolKind::FUNCTION) {
            report_error("redefinition of '" + name + "' as function", loc);
            return local_existing;
        }
    }
    if (!is_file_scope && is_definition && !is_cpp_member_function) {
        report_error("no nested functions (non-implemented GCC extension)", loc);
    }
    if (storage_class != StorageClass::NONE &&
        storage_class != StorageClass::EXTERN &&
        storage_class != StorageClass::STATIC) {
        report_error("invalid storage specifier for a function", loc);
    }
    if (!is_file_scope &&
        storage_class == StorageClass::STATIC &&
        !is_cpp_member_function) {
        report_error("cannot declare a static function inside a function", loc);
    }
    const bool is_cxx_mode = lang_opts_.is_cxx_mode();
    const LanguageLinkage requested_language_linkage =
        effective_language_linkage(language_linkage, is_cxx_mode);
    auto report_linkage_conflict_if_any = [&](const std::shared_ptr<Symbol>& sym) -> bool {
        if (!sym) {
            return false;
        }
        LanguageLinkage existing_linkage =
            effective_language_linkage(sym->get_language_linkage(), is_cxx_mode);
        if (existing_linkage != requested_language_linkage) {
            report_error("conflicting language linkage for '" + name + "'", loc);
            return true;
        }
        return false;
    };
    auto merge_language_linkage = [&](const std::shared_ptr<Symbol>& sym) {
        if (!sym) {
            return;
        }
        if (sym->get_language_linkage() == LanguageLinkage::None) {
            sym->set_language_linkage(requested_language_linkage);
        }
    };
    if (auto func_type = type.as_shared<FunctionType>()) {
        auto ret = func_type->ret_type;
        if (ret && ret->kind == TypeKind::Array) {
            report_error("function cannot return an array type", loc);
        }
        if (ret && ret->kind == TypeKind::Function) {
            report_error("function cannot return a function type", loc);
        }
    }
    auto existing = lookup_ordinary_symbol(decl_scope, name, false);
    if (!existing && !is_file_scope && !is_cpp_member_function) {
        auto parent_visible = lookup_ordinary_symbol(decl_scope, name, true);
        if (parent_visible && parent_visible->kind == SymbolKind::FUNCTION) {
            existing = parent_visible;
        }
    }
    if (existing && existing->kind == SymbolKind::FUNCTION) {
        auto function_types_match = [&](const std::shared_ptr<Symbol>& candidate) {
            if (!candidate) {
                return false;
            }
            if (candidate->type && type) {
                return candidate->type.equals_unqualified(type);
            }
            return candidate->type.get_shared() == type.get_shared();
        };

        bool same_type = function_types_match(existing);
        if (lang_opts_.is_cxx_mode() && !same_type) {
            auto cands = LookupEngine::lookup_unqualified_function_candidates(
                name, decl_scope, false);
            std::shared_ptr<Symbol> signature_match = nullptr;
            for (const auto& cand : cands) {
                if (!cand || cand->kind != SymbolKind::FUNCTION) {
                    continue;
                }
                if (!function_types_match(cand)) {
                    if (!signature_match &&
                        function_signatures_match_ignoring_return_type(cand->type, type)) {
                        signature_match = cand;
                    }
                    continue;
                }
                existing = cand;
                same_type = true;
                break;
            }
            if (!same_type) {
                if (signature_match) {
                    existing = signature_match;
                } else {
                    // C++ mode: same name + different function type introduces a new overload.
                    existing = nullptr;
                }
            }
        }

        if (existing) {
            if (auto ns_prefix = namespace_prefix_for_scope(decl_scope)) {
                if (!get_symbol_cxx_qualifier_prefix(existing.get())) {
                    set_symbol_cxx_qualifier_prefix(existing.get(), *ns_prefix);
                }
            }
            if (!same_type) {
                report_error("conflicting types for '" + name + "'", loc);
                if (decl_scope != scope && !is_definition) {
                    bind_symbol_in_scope(scope, name, existing);
                }
                return existing;
            }
            report_linkage_conflict_if_any(existing);
            bool static_after_non_static_conflict = false;
            if (is_definition) {
                if (existing->is_defined) {
                    report_error("redefinition of function '" + name + "'", loc);
                } else {
                    existing->is_defined = true;
                }
            }
            if (is_file_scope) {
                if (existing->storage_class != StorageClass::STATIC &&
                    storage_class == StorageClass::STATIC) {
                    report_error("static declaration of '" + name + "' follows non-static declaration", loc);
                    static_after_non_static_conflict = true;
                }
            }
            if (is_inline) {
                existing->is_inline = true;
            } else {
                existing->had_non_inline_declaration = true;
            }
            if (existing->storage_class == StorageClass::STATIC) {
                existing->linkage = VariableLinkage::INTERNAL;
            } else if (storage_class == StorageClass::STATIC &&
                       !static_after_non_static_conflict) {
                existing->storage_class = StorageClass::STATIC;
                existing->linkage = VariableLinkage::INTERNAL;
            } else {
                existing->linkage = VariableLinkage::EXTERNAL;
            }
            if (decl_scope != scope && !is_definition) {
                bind_symbol_in_scope(scope, name, existing);
            }
            merge_language_linkage(existing);
            return existing;
        }
    } else if (existing) {
        report_error("redefinition of '" + name + "' as function", loc);
        return existing;
    }
    VariableLinkage linkage = (storage_class == StorageClass::STATIC)
        ? VariableLinkage::INTERNAL
        : VariableLinkage::EXTERNAL;
    auto sym = std::make_shared<Symbol>(name, SymbolKind::FUNCTION, std::move(type), storage_class,
        linkage, is_inline);
    if (auto ns_prefix = namespace_prefix_for_scope(decl_scope)) {
        set_symbol_cxx_qualifier_prefix(sym.get(), *ns_prefix);
    }
    sym->is_defined = is_definition;
    sym->set_language_linkage(requested_language_linkage);
    if (global_scope) {
        record_global_scope_mutation(global_scope);
        global_scope->add_to_global_scope(sym);
    }
    bind_symbol_in_scope(decl_scope, name, sym);
    if (decl_scope != scope && !is_definition) {
        bind_symbol_in_scope(scope, name, sym);
    }
    return sym;
}


std::shared_ptr<Symbol> Collect::collect_declare_function_symbol(const std::string& name, QualType type, StorageClass storage_class, bool is_inline, bool is_definition, SrcLoc loc, LanguageLinkage language_linkage, bool is_cpp_member_function) {

    return collect_declare_function_symbol(
        session_.current_scope_,
        session_.current_global_scope_,
        name,
        type,
        storage_class,
        is_inline,
        is_definition,
        loc,
        language_linkage,
        is_cpp_member_function);
}


std::shared_ptr<Symbol> Collect::collect_declare_typedef_symbol(std::shared_ptr<Scope> scope, std::shared_ptr<GlobalIdentTracker> global_scope, const std::string& name, QualType type, SrcLoc loc) {

    if (!scope || name.empty()) {
        return nullptr;
    }
    materialize_tentative_snapshot_if_needed();
    auto existing = lookup_ordinary_symbol(scope, name, false);
    if (existing) {
        if (existing->kind == SymbolKind::TYPE) {
            auto existing_desugared =
                desugar_type(existing->type, ast_ctx_.get());
            auto incoming_desugared =
                desugar_type(type, ast_ctx_.get());
            if (existing_desugared.equals_qualified(incoming_desugared) ||
                existing_desugared.equals_unqualified(incoming_desugared)) {
                return existing;
            }
            report_error("typedef redefinition with different type: '" + name + "' (previously '" +
                existing->type.to_string() + "', now as '" + type.to_string() + "')", loc);
            return nullptr;
        }
        report_error("redefinition of '" + name + "' as a typedef; it was previously declared as a different kind of symbol", loc);
        return nullptr;
    }
    auto typedef_type = std::make_shared<TypedefType>(name, type.without_qualifiers());
    auto sym = std::make_shared<Symbol>(
        name,
        SymbolKind::TYPE,
        QualType(typedef_type, type.get_qualifiers()),
        StorageClass::TYPEDEF);
    if (global_scope) {
        record_global_scope_mutation(global_scope);
        global_scope->add_to_global_scope(sym);
    }
    bind_symbol_in_scope(scope, name, sym);
    return sym;
}


std::shared_ptr<Symbol> Collect::collect_declare_typedef_symbol(const std::string& name, QualType type, SrcLoc loc) {

    return collect_declare_typedef_symbol(session_.current_scope_, session_.current_global_scope_, name, type, loc);
}

std::shared_ptr<Symbol> Collect::collect_declare_type_name_symbol(
    std::shared_ptr<Scope> scope,
    const std::string& name,
    QualType type,
    SrcLoc loc) {

    if (!scope || name.empty()) {
        return nullptr;
    }
    materialize_tentative_snapshot_if_needed();
    auto existing = lookup_ordinary_symbol(scope, name, false);
    if (existing) {
        if (existing->kind == SymbolKind::TYPE) {
            auto existing_desugared =
                desugar_type(existing->type, ast_ctx_.get());
            auto incoming_desugared =
                desugar_type(type, ast_ctx_.get());
            if (existing_desugared.equals_qualified(incoming_desugared) ||
                existing_desugared.equals_unqualified(incoming_desugared)) {
                return existing;
            }
            report_error(
                "type-name redefinition with different type: '" + name + "'",
                loc);
            return nullptr;
        }
        report_error(
            "redefinition of '" + name +
                "' as a type-name; it was previously declared as a different kind of symbol",
            loc);
        return nullptr;
    }

    auto sym = std::make_shared<Symbol>(
        name,
        SymbolKind::TYPE,
        std::move(type),
        StorageClass::NONE);
    bind_symbol_in_scope(scope, name, sym);
    return sym;
}

std::shared_ptr<Symbol> Collect::collect_declare_type_name_symbol(
    const std::string& name,
    QualType type,
    SrcLoc loc) {

    return collect_declare_type_name_symbol(session_.current_scope_, name, std::move(type), loc);
}
