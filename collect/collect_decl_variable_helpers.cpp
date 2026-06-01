#include "collect.h"
#include "collect_decl_internal.h"
#include "collect_internal.h"
#include "../helpers/auto_type_utils.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include <algorithm>
#include <limits>
#include <sstream>

using namespace collect_decl_internal;

namespace {
bool constructor_accessible_from_context(
    const RecordSemanticState::Constructor& ctor,
    const ObjectDecl* record_decl,
    const ObjectDecl* access_context_decl,
    const ASTContext* ast_ctx,
    QualType access_context_type) {
    switch (ctor.declared_access) {
        case RecordMemberAccess::Public:
            return true;
        case RecordMemberAccess::Private:
            return collect_internal::can_access_private_member_in_context(
                record_decl,
                access_context_decl,
                ast_ctx,
                access_context_type);
        case RecordMemberAccess::Protected:
            return collect_internal::can_access_protected_member_in_context(
                record_decl,
                access_context_decl,
                record_decl,
                /*is_static_member=*/false,
                ast_ctx,
                access_context_type);
    }
    return false;
}

QualType replace_auto_placeholder_qualtype(QualType pattern, QualType deduced) {
    if (!pattern) {
        return pattern;
    }

    if (isa<AutoType>(pattern.get())) {
        if (!deduced) {
            return pattern;
        }
        uint8_t merged_quals = static_cast<uint8_t>(
            pattern.get_qualifiers() | deduced.get_qualifiers());
        return QualType(deduced.get_shared(), merged_quals);
    }

    auto raw = pattern.get_shared();
    if (!raw) {
        return pattern;
    }

    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        return QualType(
            std::make_shared<PointerType>(
                replace_auto_placeholder_qualtype(ptr->pointed_type, deduced)),
            pattern.get_qualifiers());
    }

    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        return QualType(
            std::make_shared<ReferenceType>(
                replace_auto_placeholder_qualtype(ref->referred_type, deduced),
                ref->reference_kind),
            pattern.get_qualifiers());
    }

    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        return QualType(
            std::make_shared<BlockPointerType>(
                replace_auto_placeholder_qualtype(blk->pointed_type, deduced)),
            pattern.get_qualifiers());
    }

    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        return QualType(
            std::make_shared<MemberPointerType>(
                replace_auto_placeholder_qualtype(mem_ptr->class_type, deduced),
                replace_auto_placeholder_qualtype(mem_ptr->member_type, deduced)),
            pattern.get_qualifiers());
    }

    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        QualType elem =
            replace_auto_placeholder_qualtype(arr->element_type, deduced);
        if (arr->size_kind == ArraySizeKind::Variable) {
            return QualType(
                std::make_shared<ArrayType>(elem, arr->size_expr),
                pattern.get_qualifiers());
        }
        auto rebuilt = std::make_shared<ArrayType>(elem, arr->size);
        rebuilt->size_kind = arr->size_kind;
        return QualType(rebuilt, pattern.get_qualifiers());
    }

    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        auto rebuilt = std::make_shared<FunctionType>();
        rebuilt->ret_type =
            replace_auto_placeholder_qualtype(func->ret_type, deduced);
        rebuilt->parameters.reserve(func->parameters.size());
        for (const auto& param : func->parameters) {
            rebuilt->parameters.push_back(
                replace_auto_placeholder_qualtype(param, deduced));
        }
        rebuilt->parameter_pack_flags = func->parameter_pack_flags;
        rebuilt->normalize_parameter_pack_flags();
        rebuilt->is_variadic = func->is_variadic;
        rebuilt->has_prototype = func->has_prototype;
        rebuilt->member_ref_qualifier = func->member_ref_qualifier;
        rebuilt->has_explicit_exception_spec =
            func->has_explicit_exception_spec;
        rebuilt->exception_spec = func->exception_spec;
        rebuilt->exception_spec_expr = func->exception_spec_expr;
        return QualType(rebuilt, pattern.get_qualifiers());
    }

    return pattern;
}
}

void Collect::resolve_auto_variable_type_from_expr(
    QualType& declared_type,
    const Expr* init_expr,
    const std::shared_ptr<Symbol>& sym,
    const std::string& name,
    SrcLoc loc) {
    bool has_auto_type = declared_type && contains_auto_type(declared_type.get_shared());
    if (!has_auto_type) {
        return;
    }

    uint8_t auto_flavors =
        auto_type_utils::auto_type_flavors_in(declared_type.get_shared());
    bool has_gnu_auto_type =
        (auto_flavors & auto_type_utils::kGnuAutoFlavor) != 0;
    bool has_ordinary_cxx_auto_type =
        (auto_flavors & auto_type_utils::kCxxAutoFlavor) != 0;
    bool has_decltype_auto_type =
        (auto_flavors & auto_type_utils::kDecltypeAutoFlavor) != 0;
    if (has_gnu_auto_type &&
        (has_ordinary_cxx_auto_type || has_decltype_auto_type)) {
        report_error("cannot mix '__auto_type' and 'auto' in the same declaration", loc);
    }
    if (has_ordinary_cxx_auto_type && has_decltype_auto_type) {
        report_error("cannot mix 'auto' and 'decltype(auto)' in the same declaration", loc);
    }
    bool treat_as_decltype_auto =
        has_decltype_auto_type && !has_gnu_auto_type && !has_ordinary_cxx_auto_type;
    bool treat_as_cxx_auto =
        has_ordinary_cxx_auto_type && !has_gnu_auto_type && !has_decltype_auto_type;

    if (has_gnu_auto_type && !session_.func_state_.in_function) {
        report_error("'__auto_type' is not allowed at file scope", loc);
    }
    if (treat_as_decltype_auto &&
        !auto_type_utils::is_decltype_auto_placeholder(
            declared_type.get_shared())) {
        report_error(
            "'decltype(auto)' cannot be used with pointers, references, arrays, or function declarators",
            loc);
        return;
    }
    if (!init_expr) {
        if (treat_as_decltype_auto) {
            report_error(
                "declaration of variable '" + name +
                    "' with deduced type 'decltype(auto)' requires an initializer",
                loc);
        } else if (treat_as_cxx_auto) {
            report_error(
                "declaration of variable '" + name +
                    "' with deduced type 'auto' requires an initializer",
                loc);
        } else {
            report_error("'__auto_type' requires an initializer", loc);
        }
        return;
    }
    // A typed InitListExpr is a C++ type-construction expression such as T{};
    // only raw braced-init-lists need the unsupported auto-list-deduction path.
    if (auto* init_list = dyn_cast<InitListExpr>(init_expr);
        init_list && (!treat_as_cxx_auto || !init_list->type)) {
        if (treat_as_decltype_auto) {
            report_error(
                "cannot deduce 'decltype(auto)' from initializer list",
                loc);
        } else if (treat_as_cxx_auto) {
            report_error(
                "C++ parser unsupported syntax: auto braced-init-list deduction",
                loc);
        } else {
            report_error("cannot use '__auto_type' with initializer list", loc);
        }
        return;
    }

    if (treat_as_decltype_auto) {
        auto initializer_is_template_dependent = [&]() {
            if (expression_depends_on_template_parameters(init_expr)) {
                return true;
            }
            QualType init_type = const_cast<Expr*>(init_expr)->get_type();
            return init_type &&
                   (type_depends_on_template_parameters(init_type, ast_ctx_.get()) ||
                    contains_deferred_semantic_type(init_type.get_shared()));
        };
        QualType deduced_type = resolve_decltype_expression_type(
            const_cast<Expr*>(init_expr),
            true,
            declared_type,
            loc,
            DeferredTypeResolutionMode::TryRealize);
        bool unresolved_placeholder =
            deduced_type &&
            auto_type_utils::auto_type_flavors_in(deduced_type.get_shared()) != 0;
        if ((!deduced_type || unresolved_placeholder) &&
            initializer_is_template_dependent()) {
            return;
        }
        if (!deduced_type || unresolved_placeholder) {
            deduced_type = resolve_decltype_expression_type(
                const_cast<Expr*>(init_expr),
                true,
                declared_type,
                loc,
                DeferredTypeResolutionMode::Finalize);
        }
        if (!deduced_type) {
            report_error("cannot deduce type for 'decltype(auto)'", loc);
            return;
        }
        if (auto_type_utils::auto_type_flavors_in(deduced_type.get_shared()) != 0) {
            report_error(
                "cannot deduce type for 'decltype(auto)': unresolved placeholder",
                loc);
            return;
        }
        if (!require_deduced_auto_type_constraint(
                auto_type_utils::find_first_constrained_auto_placeholder(
                    declared_type.get_shared()),
                deduced_type,
                loc,
                name.empty() ? "variable" : "variable '" + name + "'")) {
            return;
        }
        declared_type =
            replace_auto_placeholder_qualtype(declared_type, deduced_type);
        if (sym) {
            sym->type = declared_type;
        }
        return;
    }

    auto deduced_qt = const_cast<Expr*>(init_expr)->get_type();
    if (contains_deferred_semantic_type(deduced_qt.get_shared())) {
        deduced_qt = resolve_typeof_types(deduced_qt, loc);
    }
    if (!deduced_qt) {
        if (treat_as_cxx_auto) {
            report_error("cannot deduce type for 'auto': initializer has no type", loc);
        } else {
            report_error(
                "cannot deduce type for '__auto_type': initializer has no type",
                loc);
        }
        return;
    }

    if (treat_as_cxx_auto) {
        // C++ auto deduction strips top-level references and cv-qualifiers
        // from the initializer's type before replacing the placeholder.
        deduced_qt = remove_reference(deduced_qt, ast_ctx_.get()).without_qualifiers();
    }

    QualType deduction_source = deduced_qt;
    auto deduction_source_raw =
        desugar_type(deduction_source, ast_ctx_.get()).get_shared();
    auto deduction_source_kind =
        deduction_source_raw ? deduction_source_raw->kind : TypeKind::Other;
    if (deduction_source_kind == TypeKind::Array) {
        auto arr = dyn_cast_shared<ArrayType>(deduction_source_raw);
        deduction_source = QualType(std::make_shared<PointerType>(arr->element_type));
    } else if (deduction_source_kind == TypeKind::Function) {
        deduction_source =
            QualType(std::make_shared<PointerType>(QualType(deduction_source_raw)));
    }

    QualType deduced_placeholder = deduction_source;
    if (treat_as_cxx_auto) {
        auto extracted = auto_type_utils::extract_auto_placeholder_replacement(
            remove_reference(declared_type, ast_ctx_.get()),
            deduction_source);
        if (!extracted.has_value() || !extracted->get_shared()) {
            report_error(
                "cannot deduce type for 'auto' from initializer of type '" +
                    deduction_source.to_string() + "'",
                loc);
            return;
        }
        deduced_placeholder = *extracted;
    }

    if (!require_deduced_auto_type_constraint(
            auto_type_utils::find_first_constrained_auto_placeholder(
                declared_type.get_shared()),
            deduced_placeholder,
            loc,
            name.empty() ? "variable" : "variable '" + name + "'")) {
        return;
    }

    declared_type =
        replace_auto_placeholder_qualtype(declared_type, deduced_placeholder);
    if (sym) {
        sym->type = declared_type;
    }
}

void Collect::resolve_auto_variable_type(QualType& declared_type,
                                         std::unique_ptr<Expr>& init,
                                         const std::shared_ptr<Symbol>& sym,
                                         const std::string& name,
                                         SrcLoc loc) {
    resolve_auto_variable_type_from_expr(
        declared_type,
        init.get(),
        sym,
        name,
        loc);
}

void Collect::reconcile_array_declared_type_with_symbol(
    QualType& declared_type,
    const std::shared_ptr<Symbol>& sym) const {
    if (!sym || !declared_type) {
        return;
    }
    auto sym_arr = sym->type.as_shared<ArrayType>();
    auto decl_arr = declared_type.as_shared<ArrayType>();
    if (!sym_arr || !decl_arr) {
        return;
    }
    if (!sym_arr->element_type.equals_qualified(decl_arr->element_type)) {
        return;
    }
    bool sym_complete =
        sym_arr->size_kind == ArraySizeKind::Constant && sym_arr->size.has_value();
    bool decl_complete =
        decl_arr->size_kind == ArraySizeKind::Constant && decl_arr->size.has_value();
    if (!sym_complete && decl_complete) {
        sym->type = declared_type;
    } else if (sym_complete && !decl_complete) {
        declared_type = sym->type;
    }
}

void Collect::validate_variable_declared_type(QualType& declared_type,
                                                      const std::string& name,
                                                      const std::unique_ptr<Expr>& init,
                                                      StorageClass storage_class,
                                                      bool is_inline,
                                                      bool is_file_scope,
                                                      bool is_cpp_static_data_member,
                                                      SrcLoc loc) const {
    auto declared_kind = [&]() {
        return canonical_type_kind(declared_type, ast_ctx_.get());
    };

    if (!declared_type) {
        report_error("declaration of '" + name + "' has unknown type", loc);
        return;
    }

    if (is_inline) {
        if (!lang_opts_.is_cxx_mode()) {
            report_error("inline can only appear on functions", loc);
        } else if (!is_file_scope && !is_cpp_static_data_member) {
            report_error(
                "inline can only appear on namespace-scope variables and static data members",
                loc);
        }
    }
    if (declared_kind() == TypeKind::Function) {
        report_error("variable '" + name + "' declared as function type", loc);
    }
    if (declared_kind() == TypeKind::Reference &&
        !init &&
        storage_class != StorageClass::EXTERN) {
        report_error("declaration of reference variable requires an initializer", loc);
    }
    if (declared_type->isVoid()) {
        if (storage_class == StorageClass::EXTERN) {
            // GNU extension: allow extern void symbols used as linker anchors.
            declared_type = QualType(get_builtin_char(), declared_type.get_qualifiers());
        } else {
            report_error("variable has incomplete type 'void'", loc);
        }
    }
    if (declared_type.is_restrict() &&
        declared_kind() != TypeKind::Pointer &&
        declared_kind() != TypeKind::Array) {
        report_error("'restrict' qualifier can only be applied to pointer types", loc);
    }
    if (declared_type.is_atomic() && declared_kind() == TypeKind::Array) {
        report_error("_Atomic cannot be applied to an array type", loc);
    }
    bool allow_tentative_incomplete_object =
        !lang_opts_.is_cxx_mode() &&
        is_file_scope &&
        init == nullptr &&
        (storage_class == StorageClass::NONE || storage_class == StorageClass::STATIC);
    bool allow_incomplete_cpp_static_data_member =
        lang_opts_.is_cxx_mode() &&
        is_cpp_static_data_member &&
        init == nullptr &&
        storage_class == StorageClass::STATIC;
    if (declared_kind() == TypeKind::Object &&
        declared_type->isIncomplete() &&
        storage_class != StorageClass::EXTERN &&
        !allow_tentative_incomplete_object &&
        !allow_incomplete_cpp_static_data_member) {
        report_error("variable has incomplete type '" + declared_type.to_string() + "'", loc);
    }
    if (declared_kind() == TypeKind::Array) {
        auto arr =
            desugar_type(declared_type, ast_ctx_.get()).as_shared<ArrayType>();
        if (arr && arr->size_kind == ArraySizeKind::Variable && is_file_scope) {
            report_error("variable length array declaration not allowed at file scope", loc);
        }
        bool is_incomplete_array = arr &&
            (arr->size_kind == ArraySizeKind::Incomplete ||
             (arr->size_kind == ArraySizeKind::Constant && !arr->size.has_value()));
        if (is_incomplete_array &&
            !init &&
            !is_file_scope &&
            storage_class != StorageClass::EXTERN) {
            report_error(
                "definition of variable with array type needs an explicit size or initializer",
                loc);
        }
    }
}

std::vector<RecordSemanticState::Constructor>
Collect::instantiate_constructor_template_candidates(
    const RecordSemanticState& record_state,
    const std::vector<Expr*>& ctor_args,
    SrcLoc loc) {

    std::vector<RecordSemanticState::Constructor> template_constructors;
    if (record_state.method_templates.empty()) {
        return template_constructors;
    }
    std::vector<Expr*> deduction_args;
    deduction_args.reserve(ctor_args.size() + 1);
    deduction_args.push_back(nullptr);
    for (Expr* arg : ctor_args) {
        deduction_args.push_back(arg);
    }

    for (const auto& method_template : record_state.method_templates) {
        auto* function_template = method_template.decl;
        if (!function_template) {
            continue;
        }
        if (!dyn_cast<CppConstructorDecl>(function_template->function_decl())) {
            continue;
        }

        std::vector<TemplateArgument> specialization_arguments;
        std::shared_ptr<Symbol> probe_symbol = nullptr;
        if (!probe_function_template_call_specialization(
                function_template,
                deduction_args,
                loc,
                probe_symbol,
                nullptr,
                &specialization_arguments)) {
            continue;
        }

        std::shared_ptr<Symbol> specialization_symbol = nullptr;
        auto* specialization_decl =
            instantiate_function_template_specialization(
                function_template,
                specialization_arguments,
                loc,
                &specialization_symbol,
                /*instantiate_definition=*/false);
        auto* specialized_ctor =
            dyn_cast<CppConstructorDecl>(specialization_decl);
        if (!specialized_ctor || !specialization_symbol) {
            continue;
        }

        RecordSemanticState::Constructor ctor;
        ctor.name = specialized_ctor->name;
        ctor.type = QualType(specialized_ctor->type);
        ctor.declared_access = method_template.declared_access;
        ctor.is_implicit = false;
        ctor.is_explicit = specialized_ctor->is_explicit;
        ctor.is_deleted = specialized_ctor->is_deleted;
        ctor.decl = specialized_ctor;
        ctor.symbol = std::move(specialization_symbol);
        ctor.function_template = function_template;
        template_constructors.push_back(std::move(ctor));
    }

    return template_constructors;
}

Collect::ConstructorCandidateEval
Collect::evaluate_variable_constructor_candidate(
    const RecordSemanticState::Constructor& ctor,
    const ObjectDecl* record_decl,
    const std::vector<std::unique_ptr<Expr>>& ctor_args,
    bool ctor_is_copy_initialization) {

    ConstructorCandidateEval eval;
    eval.ctor = &ctor;
    if (ctor.is_implicit) {
        eval.provenance = OverloadCandidateProvenance::ImplicitSpecialMember;
    } else if (ctor.function_template ||
               (ctor.symbol &&
                get_symbol_function_template_specialization(ctor.symbol.get()))) {
        eval.provenance =
            OverloadCandidateProvenance::ConstructorTemplateSpecialization;
    } else {
        eval.provenance = OverloadCandidateProvenance::Constructor;
    }
    eval.function_type =
        desugar_type(ctor.type, ast_ctx_.get()).as_shared<FunctionType>();
    if (!eval.function_type) {
        return eval;
    }

    CppConstructorUserParamInfo param_info = cpp_compute_constructor_user_param_info(ctor);
    eval.user_param_start = param_info.user_param_start;
    eval.max_user_param_count = param_info.max_user_param_count;
    eval.required_user_param_count = param_info.required_user_param_count;
    const ObjectDecl* access_context_decl =
        collect_internal::current_access_context_record_decl(
            session_.func_state_.current_function_is_cpp_member,
            session_.func_state_.current_function_cpp_this_type,
            session_.func_state_.current_function_cpp_friend_access_type,
            session_.current_cpp_record_lookup_type_,
            ast_ctx_.get(),
            session_.func_state_.current_function_cpp_access_context_type);
    QualType access_context_type =
        collect_internal::current_access_context_record_type(
            session_.func_state_.current_function_is_cpp_member,
            session_.func_state_.current_function_cpp_this_type,
            session_.func_state_.current_function_cpp_friend_access_type,
            session_.current_cpp_record_lookup_type_,
            ast_ctx_.get(),
            session_.func_state_.current_function_cpp_access_context_type);

    if (ctor.is_implicit) {
        eval.is_synthesized_implicit_ctor = true;
        if (eval.max_user_param_count == 1 &&
            eval.user_param_start < eval.function_type->parameters.size()) {
            QualType implicit_param_type =
                decay_parameter_type(eval.function_type->parameters[eval.user_param_start]);
            eval.synthesized_param_type = implicit_param_type;
            auto ref_type =
                desugar_type(implicit_param_type, ast_ctx_.get())
                    .as_shared<ReferenceType>();
            auto referred_record =
                ref_type && ref_type->referred_type
                    ? desugar_type(ref_type->referred_type, ast_ctx_.get())
                          .as_shared<ObjectType>()
                    : nullptr;
            QualType record_type_for_copy =
                record_decl ? QualType(record_decl->get_record_type()) : QualType();
            if (ref_type &&
                ref_type->isLValueReference() &&
                referred_record &&
                (referred_record->get_decl() == record_decl ||
                 types_equivalent_after_template_argument_canonicalization(
                     ref_type->referred_type,
                     record_type_for_copy,
                     ast_ctx_.get(),
                     /*ignore_top_level_qualifiers=*/true))) {
                eval.is_synthesized_implicit_copy = true;
            }
        }

        if (!constructor_accessible_from_context(
                ctor,
                record_decl,
                access_context_decl,
                ast_ctx_.get(),
                access_context_type) ||
            ctor.is_deleted ||
            (ctor_is_copy_initialization && ctor.is_explicit) ||
            ctor_args.size() < eval.required_user_param_count ||
            ctor_args.size() > eval.max_user_param_count) {
            return eval;
        }

        eval.viable = true;
        eval.conversions.reserve(ctor_args.size());
        for (size_t i = 0; i < ctor_args.size(); ++i) {
            size_t param_idx = eval.user_param_start + i;
            if (param_idx >= eval.function_type->parameters.size()) {
                eval.viable = false;
                break;
            }
            QualType param_type = decay_parameter_type(eval.function_type->parameters[param_idx]);
            auto seq = build_cpp_overload_conversion_sequence(
                ctor_args[i].get(), param_type, /*allow_user_defined=*/false);
            if (!seq.viable) {
                eval.viable = false;
                eval.conversions.push_back(seq);
                break;
            }
            eval.conversions.push_back(seq);
        }
        return eval;
    }

    if (!ctor.symbol ||
        ctor.is_deleted ||
        (ctor_is_copy_initialization && ctor.is_explicit) ||
        !constructor_accessible_from_context(
            ctor,
            record_decl,
            access_context_decl,
            ast_ctx_.get(),
            access_context_type) ||
        ctor_args.size() < eval.required_user_param_count ||
        ctor_args.size() > eval.max_user_param_count) {
        return eval;
    }

    eval.viable = true;
    eval.conversions.reserve(ctor_args.size());
    for (size_t i = 0; i < ctor_args.size(); ++i) {
        size_t param_idx = eval.user_param_start + i;
        if (param_idx >= eval.function_type->parameters.size()) {
            eval.viable = false;
            break;
        }
        QualType param_type = decay_parameter_type(eval.function_type->parameters[param_idx]);
        auto seq = build_cpp_overload_conversion_sequence(
            ctor_args[i].get(), param_type, /*allow_user_defined=*/false);
        if (!seq.viable) {
            eval.viable = false;
            eval.conversions.push_back(seq);
            break;
        }
        eval.conversions.push_back(seq);
    }
    return eval;
}

std::string Collect::describe_variable_constructor_candidate(
    const ConstructorCandidateEval& eval,
    const ObjectDecl* record_decl,
    QualType declared_type) const {

    const ObjectDecl* access_context_decl =
        collect_internal::current_access_context_record_decl(
            session_.func_state_.current_function_is_cpp_member,
            session_.func_state_.current_function_cpp_this_type,
            session_.func_state_.current_function_cpp_friend_access_type,
            session_.current_cpp_record_lookup_type_,
            ast_ctx_.get(),
            session_.func_state_.current_function_cpp_access_context_type);
    QualType access_context_type =
        collect_internal::current_access_context_record_type(
            session_.func_state_.current_function_is_cpp_member,
            session_.func_state_.current_function_cpp_this_type,
            session_.func_state_.current_function_cpp_friend_access_type,
            session_.current_cpp_record_lookup_type_,
            ast_ctx_.get(),
            session_.func_state_.current_function_cpp_access_context_type);
    auto constructor_is_accessible =
        [&](const RecordSemanticState::Constructor* ctor) {
            return ctor &&
                   constructor_accessible_from_context(
                       *ctor,
                       record_decl,
                       access_context_decl,
                       ast_ctx_.get(),
                       access_context_type);
        };

    if (eval.is_synthesized_implicit_ctor && !eval.ctor) {
        return "<invalid constructor>";
    }
    if (eval.is_synthesized_implicit_copy) {
        std::ostringstream os;
        std::string ctor_name =
            (record_decl && !record_decl->tag.empty()) ? record_decl->tag
                                                       : declared_type.to_string();
        os << ctor_name << "(" << eval.synthesized_param_type.to_string() << ") [implicit]";
        if (eval.ctor && eval.ctor->is_deleted) {
            os << " = delete";
        }
        if (eval.ctor && !constructor_is_accessible(eval.ctor)) {
            os << " [not accessible]";
        }
        return os.str();
    }
    if (eval.is_synthesized_implicit_ctor) {
        std::ostringstream os;
        std::string ctor_name =
            (record_decl && !record_decl->tag.empty()) ? record_decl->tag
                                                       : declared_type.to_string();
        os << ctor_name << "(";
        bool wrote_param = false;
        if (eval.function_type) {
            for (size_t param_idx = eval.user_param_start;
                 param_idx < eval.function_type->parameters.size();
                 ++param_idx) {
                QualType param_type = eval.function_type->parameters[param_idx];
                if (param_type &&
                    param_type->isVoid() &&
                    eval.function_type->parameters.size() == eval.user_param_start + 1) {
                    break;
                }
                if (wrote_param) {
                    os << ", ";
                }
                os << param_type.to_string();
                wrote_param = true;
            }
        }
        os << ") [implicit]";
        if (eval.ctor && eval.ctor->is_deleted) {
            os << " = delete";
        }
        if (eval.ctor && !constructor_is_accessible(eval.ctor)) {
            os << " [not accessible]";
        }
        return os.str();
    }
    if (!eval.ctor) {
        return "<invalid constructor>";
    }

    std::ostringstream os;
    if (eval.ctor->is_explicit) {
        os << "explicit ";
    }
    os << eval.ctor->name << "(";
    if (!eval.function_type) {
        os << "<invalid>";
    } else {
        bool wrote_param = false;
        for (size_t param_idx = eval.user_param_start;
             param_idx < eval.function_type->parameters.size();
             ++param_idx) {
            QualType param_type = eval.function_type->parameters[param_idx];
            if (param_type &&
                param_type->isVoid() &&
                eval.function_type->parameters.size() == eval.user_param_start + 1) {
                break;
            }
            if (wrote_param) {
                os << ", ";
            }
            os << param_type.to_string();
            wrote_param = true;
        }
    }
    os << ")";
    if (eval.ctor->is_deleted) {
        os << " = delete";
    }
    if (!constructor_is_accessible(eval.ctor)) {
        os << " [not accessible]";
    }
    return os.str();
}

std::string Collect::describe_variable_constructor_candidates(
    const std::vector<ConstructorCandidateEval>& evaluated,
    const std::vector<size_t>& indices,
    const ObjectDecl* record_decl,
    QualType declared_type) const {

    std::ostringstream os;
    size_t emitted = 0;
    for (size_t idx : indices) {
        if (idx >= evaluated.size()) {
            continue;
        }
        if (emitted > 0) {
            os << ", ";
        }
        os << describe_variable_constructor_candidate(
            evaluated[idx], record_decl, declared_type);
        ++emitted;
        if (emitted == 4 && indices.size() > emitted) {
            os << ", ...";
            break;
        }
    }
    return os.str();
}

bool Collect::is_better_variable_constructor_candidate(
    const ConstructorCandidateEval& lhs,
    const ConstructorCandidateEval& rhs) const {

    bool strictly_better = false;
    size_t compare_count = std::min(lhs.conversions.size(), rhs.conversions.size());
    for (size_t i = 0; i < compare_count; ++i) {
        int lhs_rank = static_cast<int>(lhs.conversions[i].rank);
        int rhs_rank = static_cast<int>(rhs.conversions[i].rank);
        if (lhs_rank > rhs_rank) {
            return false;
        }
        if (lhs_rank < rhs_rank) {
            strictly_better = true;
            continue;
        }
        if (lhs.conversions[i].rank == ConversionSequenceRank::ExactMatch) {
            int lhs_subrank = exact_match_subrank_for_overload(lhs.conversions[i]);
            int rhs_subrank = exact_match_subrank_for_overload(rhs.conversions[i]);
            if (lhs_subrank > rhs_subrank) {
                return false;
            }
            if (lhs_subrank < rhs_subrank) {
                strictly_better = true;
            }
        }
    }
    if (strictly_better) {
        return true;
    }

    auto is_template_constructor = [](OverloadCandidateProvenance provenance) {
        return provenance ==
            OverloadCandidateProvenance::ConstructorTemplateSpecialization;
    };
    bool lhs_template_constructor =
        is_template_constructor(lhs.provenance);
    bool rhs_template_constructor =
        is_template_constructor(rhs.provenance);
    if (lhs_template_constructor != rhs_template_constructor) {
        return !lhs_template_constructor && rhs_template_constructor;
    }

    return false;
}

std::optional<size_t> Collect::select_best_variable_constructor_candidate_index(
    const std::vector<ConstructorCandidateEval>& evaluated,
    const std::vector<size_t>& viable_indices) const {

    std::optional<size_t> best_index;
    for (size_t idx : viable_indices) {
        bool better_than_all = true;
        for (size_t other : viable_indices) {
            if (idx == other) {
                continue;
            }
            if (!is_better_variable_constructor_candidate(
                    evaluated[idx], evaluated[other])) {
                better_than_all = false;
                break;
            }
        }
        if (!better_than_all) {
            continue;
        }
        if (best_index.has_value()) {
            return std::nullopt;
        }
        best_index = idx;
    }
    return best_index;
}

bool Collect::materialize_variable_constructor_selection(
    const ConstructorCandidateEval& chosen,
    std::vector<std::unique_ptr<Expr>> ctor_args,
    bool ctor_is_list_init,
    QualType declared_type,
    SrcLoc loc,
    VariableInitializationSelection& selection) {

    if (!chosen.ctor || !chosen.function_type) {
        report_error("internal error: selected constructor is missing semantic symbol", loc);
        return false;
    }

    std::vector<std::unique_ptr<Expr>> all_ctor_args;
    all_ctor_args.reserve(chosen.max_user_param_count);
    for (auto& provided_arg : ctor_args) {
        all_ctor_args.push_back(std::move(provided_arg));
    }

    if (chosen.is_synthesized_implicit_copy && !chosen.ctor->symbol) {
        if (all_ctor_args.size() != 1) {
            report_error(
                "internal error: implicit copy constructor requires one argument",
                loc);
            return false;
        }
        selection.nonconstructor_init_expr = process_initializer_for_type(
            std::move(all_ctor_args.front()),
            declared_type,
            loc);
        return true;
    }
    if (chosen.ctor->is_implicit &&
        chosen.max_user_param_count == 0 &&
        !chosen.ctor->symbol) {
        selection.constructor_is_list_init = ctor_is_list_init;
        selection.constructor_args.clear();
        selection.constructor_symbol = nullptr;
        selection.selected_implicit_default_constructor_without_symbol = true;
        return true;
    }
    if (chosen.ctor->is_implicit && !chosen.ctor->symbol) {
        if (!all_ctor_args.empty()) {
            report_error(
                "internal error: unsupported synthesized implicit constructor argument set",
                loc);
            return false;
        }
        selection.constructor_is_list_init = ctor_is_list_init;
        selection.constructor_args.clear();
        selection.constructor_symbol = nullptr;
        selection.selected_implicit_default_constructor_without_symbol = true;
        return true;
    }
    if (!chosen.ctor->symbol) {
        report_error("internal error: selected constructor is missing semantic symbol", loc);
        return false;
    }

    for (size_t arg_index = all_ctor_args.size();
         arg_index < chosen.max_user_param_count;
         ++arg_index) {
        size_t param_idx = chosen.user_param_start + arg_index;
        const auto* defaults = get_symbol_cpp_default_arguments(chosen.ctor->symbol.get());
        const Expr* default_expr =
            (defaults && param_idx < defaults->size()) ? (*defaults)[param_idx] : nullptr;
        if (!default_expr) {
            report_error(
                "internal error: missing constructor default argument metadata",
                loc);
            return false;
        }
        std::string clone_error;
        auto cloned_default = clone_expr_tree(default_expr, ast_ctx_.get(), &clone_error);
        if (!cloned_default) {
            std::string message =
                clone_error.empty()
                    ? "default argument expression is not supported"
                    : "default argument expression is not supported: " + clone_error;
            report_error(message, default_expr->location);
            return false;
        }
        all_ctor_args.push_back(std::move(cloned_default));
    }

    std::vector<std::unique_ptr<Expr>> converted_args;
    converted_args.reserve(all_ctor_args.size());
    for (size_t i = 0; i < all_ctor_args.size(); ++i) {
        size_t param_idx = chosen.user_param_start + i;
        QualType param_type =
            decay_parameter_type(chosen.function_type->parameters[param_idx]);
        auto arg = std::move(all_ctor_args[i]);
        const ImplicitConversionSequence* selected_seq =
            i < chosen.conversions.size() ? &chosen.conversions[i] : nullptr;
        if (selected_seq &&
            selected_seq->kind == ConversionSequenceKind::UserDefined &&
            canonical_type_kind(param_type, ast_ctx_.get()) !=
                TypeKind::Reference) {
            SrcLoc arg_loc = arg ? arg->location : loc;
            arg = build_cpp_user_defined_conversion_expr(
                std::move(arg), param_type, arg_loc);
            if (!arg || isa<ErrorExpr>(arg.get())) {
                report_error(
                    "invalid user-defined conversion in constructor argument",
                    arg_loc);
                return false;
            }
            converted_args.push_back(std::move(arg));
            continue;
        }

        if (canonical_type_kind(param_type, ast_ctx_.get()) == TypeKind::Object &&
            dyn_cast<InitListExpr>(Collect::strip_implicit_casts(arg.get()))) {
            SrcLoc arg_loc = arg ? arg->location : loc;
            arg = convert_cpp_braced_init_argument(
                std::move(arg), param_type, arg_loc);
            if (!arg || isa<ErrorExpr>(arg.get())) {
                report_error(
                    "invalid braced-initializer constructor argument",
                    arg_loc);
                return false;
            }
            converted_args.push_back(std::move(arg));
            continue;
        }

        if (canonical_type_kind(param_type, ast_ctx_.get()) ==
            TypeKind::Reference) {
            auto seq = build_cpp_overload_conversion_sequence(
                arg.get(),
                param_type,
                /*allow_user_defined=*/false);
            if (!seq.viable) {
                report_conversion_failure(
                    "constructor argument",
                    arg ? arg->get_type() : QualType(),
                    param_type,
                    arg ? arg->location : loc);
                return false;
            }
        } else {
            arg = collect_apply_standard_conversions(
                std::move(arg), ExprUseContext::InitScalar);
            arg = cast_if_needed(std::move(arg), param_type);
        }
        converted_args.push_back(std::move(arg));
    }

    selection.constructor_symbol = chosen.ctor->symbol;
    selection.constructor_args = std::move(converted_args);
    selection.constructor_is_list_init = ctor_is_list_init;
    note_specialization_use_for_symbol(selection.constructor_symbol, loc);
    if (auto completion_error =
            complete_selected_function_template_specialization_symbol(
                selection.constructor_symbol,
                loc,
                "failed to instantiate selected constructor template specialization")) {
        (void)completion_error;
        report_error(
            "failed to instantiate selected constructor template specialization",
            loc);
        return false;
    }
    return true;
}

bool Collect::select_constructor_for_variable_initialization(
    std::shared_ptr<ObjectType> record_type,
    std::vector<std::unique_ptr<Expr>> ctor_args,
    bool ctor_is_list_init,
    bool ctor_is_copy_initialization,
    QualType declared_type,
    SrcLoc loc,
    VariableInitializationSelection& selection) {
    selection.constructor_symbol = nullptr;
    selection.constructor_args.clear();
    selection.constructor_is_list_init = false;
    selection.selected_implicit_default_constructor_without_symbol = false;
    selection.nonconstructor_init_expr.reset();

    if (!record_type) {
        return false;
    }
    const TagDecl* tag_decl = record_type->get_decl();
    const ObjectDecl* record_decl =
        (tag_decl && tag_decl->is_record_decl())
            ? static_cast<const ObjectDecl*>(tag_decl)
            : nullptr;
    if (!record_decl) {
        return false;
    }
    const RecordSemanticState* record_state = record_semantics_cache_lookup(record_decl);
    if (!record_state ||
        (record_state->constructors.empty() &&
         record_state->method_templates.empty())) {
        return false;
    }

    std::vector<Expr*> raw_ctor_args;
    raw_ctor_args.reserve(ctor_args.size());
    for (const auto& arg : ctor_args) {
        raw_ctor_args.push_back(arg.get());
    }
    std::vector<RecordSemanticState::Constructor> template_constructors =
        instantiate_constructor_template_candidates(
            *record_state,
            raw_ctor_args,
            loc);

    std::vector<ConstructorCandidateEval> evaluated;
    evaluated.reserve(
        record_state->constructors.size() + template_constructors.size());
    for (const auto& ctor : record_state->constructors) {
        evaluated.push_back(evaluate_variable_constructor_candidate(
            ctor, record_decl, ctor_args, ctor_is_copy_initialization));
    }
    for (const auto& ctor : template_constructors) {
        evaluated.push_back(evaluate_variable_constructor_candidate(
            ctor, record_decl, ctor_args, ctor_is_copy_initialization));
    }

    std::vector<size_t> viable_indices;
    viable_indices.reserve(evaluated.size());
    for (size_t idx = 0; idx < evaluated.size(); ++idx) {
        if (evaluated[idx].viable) {
            viable_indices.push_back(idx);
        }
    }

    if (viable_indices.empty()) {
        std::vector<size_t> all_indices;
        all_indices.reserve(evaluated.size());
        for (size_t idx = 0; idx < evaluated.size(); ++idx) {
            all_indices.push_back(idx);
        }
        std::string candidates = describe_variable_constructor_candidates(
            evaluated, all_indices, record_decl, declared_type);
        report_error(
            "no matching constructor for initialization of '" +
                declared_type.to_string() + "'" +
                (candidates.empty() ? "" : "; candidate constructors: " + candidates),
            loc);
        return false;
    }

    auto best_index = select_best_variable_constructor_candidate_index(
        evaluated, viable_indices);
    if (!best_index.has_value()) {
        std::string candidates = describe_variable_constructor_candidates(
            evaluated, viable_indices, record_decl, declared_type);
        report_error(
            "constructor call for '" + declared_type.to_string() +
                "' is ambiguous" +
                (candidates.empty() ? "" : "; viable candidates: " + candidates),
            loc);
        return false;
    }

    return materialize_variable_constructor_selection(
        evaluated[*best_index],
        std::move(ctor_args),
        ctor_is_list_init,
        declared_type,
        loc,
        selection);
}

std::shared_ptr<Symbol> Collect::select_destructor_for_variable(
    const std::string& name,
    QualType declared_type,
    const std::shared_ptr<ObjectType>& record_type,
    SrcLoc loc) const {
    if (!record_type) {
        return nullptr;
    }

    const auto* record_decl = dyn_cast<ObjectDecl>(record_type->get_decl());
    const RecordSemanticState* record_state =
        record_decl ? record_semantics_cache_lookup(record_decl) : nullptr;
    if (!record_state || record_state->destructors.empty()) {
        return nullptr;
    }

    std::vector<size_t> viable_indices;
    viable_indices.reserve(record_state->destructors.size());

    auto describe_destructor = [&](const RecordSemanticState::Destructor& dtor) {
        std::ostringstream os;
        os << dtor.name << "(";
        auto fn_type =
            desugar_type(dtor.type, ast_ctx_.get()).as_shared<FunctionType>();
        bool wrote_param = false;
        if (fn_type) {
            size_t user_param_start = 0;
            if (!fn_type->parameters.empty() &&
                is_this_parameter_for_record(
                    fn_type->parameters.front(), record_type, ast_ctx_.get())) {
                user_param_start = 1;
            }
            for (size_t idx = user_param_start; idx < fn_type->parameters.size(); ++idx) {
                QualType param_type = fn_type->parameters[idx];
                if (param_type &&
                    param_type->isVoid() &&
                    fn_type->parameters.size() == user_param_start + 1) {
                    continue;
                }
                if (wrote_param) {
                    os << ", ";
                }
                os << param_type.to_string();
                wrote_param = true;
            }
        }
        os << ")";
        if (dtor.is_deleted) {
            os << " = delete";
        }
        if (dtor.declared_access != RecordMemberAccess::Public) {
            os << " [not accessible]";
        }
        return os.str();
    };

    auto describe_destructor_candidates = [&](const std::vector<size_t>& indices) {
        std::ostringstream os;
        size_t emitted = 0;
        for (size_t idx : indices) {
            if (idx >= record_state->destructors.size()) {
                continue;
            }
            if (emitted > 0) {
                os << ", ";
            }
            os << describe_destructor(record_state->destructors[idx]);
            ++emitted;
            if (emitted == 4 && indices.size() > emitted) {
                os << ", ...";
                break;
            }
        }
        return os.str();
    };

    for (size_t idx = 0; idx < record_state->destructors.size(); ++idx) {
        const auto& dtor = record_state->destructors[idx];
        if (!cpp_destructor_is_viable_candidate(dtor, false)) {
            continue;
        }
        viable_indices.push_back(idx);
    }

    if (viable_indices.empty()) {
        std::vector<size_t> all_indices;
        all_indices.reserve(record_state->destructors.size());
        for (size_t idx = 0; idx < record_state->destructors.size(); ++idx) {
            all_indices.push_back(idx);
        }
        std::string candidates = describe_destructor_candidates(all_indices);
        report_error(
            "no viable destructor for variable '" + name +
                "' of type '" + declared_type.to_string() + "'" +
                (candidates.empty() ? "" : "; candidate destructors: " + candidates),
            loc);
        return nullptr;
    }

    auto selected_symbol = record_state->destructors[viable_indices.front()].symbol;
    note_specialization_use_for_symbol(selected_symbol, loc);
    return selected_symbol;
}
