#include "collect.h"
#include "collect_decl_internal.h"
#include "../helpers/auto_type_utils.h"
#include "../ast/expr_clone.h"
#include "../ast/special_members.h"
#include <algorithm>
#include <limits>
#include <sstream>

using namespace collect_decl_internal;

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
    bool has_cxx_auto_type =
        (auto_flavors & auto_type_utils::kCxxAutoFlavor) != 0;
    if (has_gnu_auto_type && has_cxx_auto_type) {
        report_error("cannot mix '__auto_type' and 'auto' in the same declaration", loc);
    }
    bool treat_as_cxx_auto = has_cxx_auto_type && !has_gnu_auto_type;

    if (!treat_as_cxx_auto && !session_.func_state_.in_function) {
        report_error("'__auto_type' is not allowed at file scope", loc);
    }
    if (!init_expr) {
        if (treat_as_cxx_auto) {
            report_error(
                "declaration of variable '" + name +
                    "' with deduced type 'auto' requires an initializer",
                loc);
        } else {
            report_error("'__auto_type' requires an initializer", loc);
        }
        return;
    }
    if (isa<InitListExpr>(init_expr)) {
        if (treat_as_cxx_auto) {
            report_error(
                "C++ parser unsupported syntax: auto braced-init-list deduction",
                loc);
        } else {
            report_error("cannot use '__auto_type' with initializer list", loc);
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

    auto deduced = desugar_type(deduced_qt, ast_ctx_.get()).get_shared();
    auto deduced_kind = deduced ? deduced->kind : TypeKind::Other;
    if (deduced_kind == TypeKind::Array) {
        auto arr = dyn_cast_shared<ArrayType>(deduced);
        deduced = std::make_shared<PointerType>(arr->element_type);
    } else if (deduced_kind == TypeKind::Function) {
        deduced = std::make_shared<PointerType>(QualType(deduced));
    }

    auto replaced = replace_auto_type(declared_type.get_shared(), deduced);
    declared_type = QualType(replaced, declared_type.get_qualifiers());
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
                                                      SrcLoc loc) const {
    auto declared_kind = [&]() {
        return canonical_type_kind(declared_type, ast_ctx_.get());
    };

    if (!declared_type) {
        report_error("declaration of '" + name + "' has unknown type", loc);
        return;
    }

    if (is_inline) {
        report_error("inline can only appear on functions", loc);
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
    if (declared_kind() == TypeKind::Object &&
        declared_type->isIncomplete() &&
        storage_class != StorageClass::EXTERN &&
        !allow_tentative_incomplete_object) {
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

Collect::ConstructorCandidateEval
Collect::evaluate_variable_constructor_candidate(
    const RecordSemanticState::Constructor& ctor,
    const ObjectDecl* record_decl,
    const std::vector<std::unique_ptr<Expr>>& ctor_args,
    bool ctor_is_copy_initialization) {

    ConstructorCandidateEval eval;
    eval.ctor = &ctor;
    eval.function_type =
        desugar_type(ctor.type, ast_ctx_.get()).as_shared<FunctionType>();
    if (!eval.function_type) {
        return eval;
    }

    CppConstructorUserParamInfo param_info = cpp_compute_constructor_user_param_info(ctor);
    eval.user_param_start = param_info.user_param_start;
    eval.max_user_param_count = param_info.max_user_param_count;
    eval.required_user_param_count = param_info.required_user_param_count;

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
            if (ref_type &&
                ref_type->isLValueReference() &&
                referred_record &&
                referred_record->get_decl() == record_decl) {
                eval.is_synthesized_implicit_copy = true;
            }
        }

        if (!cpp_access_allows_member(ctor.declared_access, false) ||
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
        !cpp_access_allows_member(ctor.declared_access, false) ||
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
        if (eval.ctor && eval.ctor->declared_access != RecordMemberAccess::Public) {
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
        if (eval.ctor && eval.ctor->declared_access != RecordMemberAccess::Public) {
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
    if (eval.ctor->declared_access != RecordMemberAccess::Public) {
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
    return strictly_better;
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

    if (chosen.is_synthesized_implicit_copy) {
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
    if (!record_state || record_state->constructors.empty()) {
        return false;
    }

    std::vector<ConstructorCandidateEval> evaluated;
    evaluated.reserve(record_state->constructors.size());
    for (const auto& ctor : record_state->constructors) {
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
