#ifndef ABURI_PARSER_CPP_OUT_OF_LINE_MATCH_H
#define ABURI_PARSER_CPP_OUT_OF_LINE_MATCH_H

#include "../ast/ast.h"

inline bool cpp_out_of_line_type_matches(QualType lhs,
                                         QualType rhs,
                                         bool ignore_top_level_qualifiers) {
    if (!lhs || !rhs) {
        return lhs.get_shared() == rhs.get_shared();
    }

    lhs = desugar_typedefs(lhs);
    rhs = desugar_typedefs(rhs);
    if (ignore_top_level_qualifiers) {
        lhs = QualType(lhs.get_shared());
        rhs = QualType(rhs.get_shared());
    } else if (lhs.get_qualifiers() != rhs.get_qualifiers()) {
        return false;
    }

    if (!lhs || !rhs) {
        return lhs.get_shared() == rhs.get_shared();
    }

    auto* lhs_raw = lhs.get();
    auto* rhs_raw = rhs.get();
    if (!lhs_raw || !rhs_raw) {
        return lhs_raw == rhs_raw;
    }
    if (lhs_raw->kind != rhs_raw->kind) {
        return ignore_top_level_qualifiers
            ? lhs.equals_unqualified(rhs)
            : lhs.equals_qualified(rhs);
    }

    if (auto* lhs_parm = dyn_cast<TemplateTypeParmType>(lhs_raw)) {
        auto* rhs_parm = dyn_cast<TemplateTypeParmType>(rhs_raw);
        return rhs_parm &&
               lhs_parm->depth == rhs_parm->depth &&
               lhs_parm->index == rhs_parm->index;
    }
    if (auto* lhs_ptr = dyn_cast<PointerType>(lhs_raw)) {
        auto* rhs_ptr = dyn_cast<PointerType>(rhs_raw);
        return rhs_ptr &&
               cpp_out_of_line_type_matches(
                   lhs_ptr->pointed_type,
                   rhs_ptr->pointed_type,
                   false);
    }
    if (auto* lhs_ref = dyn_cast<ReferenceType>(lhs_raw)) {
        auto* rhs_ref = dyn_cast<ReferenceType>(rhs_raw);
        return rhs_ref &&
               lhs_ref->reference_kind == rhs_ref->reference_kind &&
               cpp_out_of_line_type_matches(
                   lhs_ref->referred_type,
                   rhs_ref->referred_type,
                   false);
    }
    if (auto* lhs_mem_ptr = dyn_cast<MemberPointerType>(lhs_raw)) {
        auto* rhs_mem_ptr = dyn_cast<MemberPointerType>(rhs_raw);
        return rhs_mem_ptr &&
               cpp_out_of_line_type_matches(
                   lhs_mem_ptr->class_type,
                   rhs_mem_ptr->class_type,
                   false) &&
               cpp_out_of_line_type_matches(
                   lhs_mem_ptr->member_type,
                   rhs_mem_ptr->member_type,
                   false);
    }
    if (auto* lhs_block_ptr = dyn_cast<BlockPointerType>(lhs_raw)) {
        auto* rhs_block_ptr = dyn_cast<BlockPointerType>(rhs_raw);
        return rhs_block_ptr &&
               cpp_out_of_line_type_matches(
                   lhs_block_ptr->pointed_type,
                   rhs_block_ptr->pointed_type,
                   false);
    }
    if (auto* lhs_array = dyn_cast<ArrayType>(lhs_raw)) {
        auto* rhs_array = dyn_cast<ArrayType>(rhs_raw);
        if (!rhs_array || lhs_array->size_kind != rhs_array->size_kind) {
            return false;
        }
        if (lhs_array->size_kind == ArraySizeKind::Constant &&
            lhs_array->size.has_value() &&
            rhs_array->size.has_value() &&
            lhs_array->size.value() != rhs_array->size.value()) {
            return false;
        }
        return cpp_out_of_line_type_matches(
            lhs_array->element_type,
            rhs_array->element_type,
            false);
    }
    if (auto* lhs_func = dyn_cast<FunctionType>(lhs_raw)) {
        auto* rhs_func = dyn_cast<FunctionType>(rhs_raw);
        if (!rhs_func ||
            lhs_func->member_ref_qualifier != rhs_func->member_ref_qualifier ||
            lhs_func->has_prototype != rhs_func->has_prototype ||
            lhs_func->is_variadic != rhs_func->is_variadic ||
            lhs_func->has_explicit_exception_spec !=
                rhs_func->has_explicit_exception_spec ||
            lhs_func->exception_spec != rhs_func->exception_spec ||
            lhs_func->parameters.size() != rhs_func->parameters.size()) {
            return false;
        }
        if (!cpp_out_of_line_type_matches(
                lhs_func->ret_type,
                rhs_func->ret_type,
                true)) {
            return false;
        }
        for (size_t idx = 0; idx < lhs_func->parameters.size(); ++idx) {
            if (!cpp_out_of_line_type_matches(
                    lhs_func->parameters[idx],
                    rhs_func->parameters[idx],
                    true)) {
                return false;
            }
        }
        return true;
    }
    if (auto* lhs_specialization = dyn_cast<TemplateSpecializationType>(lhs_raw)) {
        auto* rhs_specialization = dyn_cast<TemplateSpecializationType>(rhs_raw);
        if (!rhs_specialization ||
            lhs_specialization->template_name != rhs_specialization->template_name ||
            lhs_specialization->arguments.size() !=
                rhs_specialization->arguments.size()) {
            return false;
        }
        if (lhs_specialization->primary_template &&
            rhs_specialization->primary_template &&
            lhs_specialization->primary_template !=
                rhs_specialization->primary_template) {
            return false;
        }
        for (size_t idx = 0; idx < lhs_specialization->arguments.size(); ++idx) {
            const auto& lhs_argument = lhs_specialization->arguments[idx];
            const auto& rhs_argument = rhs_specialization->arguments[idx];
            if (lhs_argument.kind != rhs_argument.kind) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Type &&
                !cpp_out_of_line_type_matches(
                    lhs_argument.type,
                    rhs_argument.type,
                    false)) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Value &&
                !lhs_argument.equals(rhs_argument)) {
                return false;
            }
        }
        return true;
    }
    if (auto* lhs_dependent = dyn_cast<DependentNameType>(lhs_raw)) {
        auto* rhs_dependent = dyn_cast<DependentNameType>(rhs_raw);
        if (!rhs_dependent ||
            lhs_dependent->member_name != rhs_dependent->member_name ||
            lhs_dependent->template_arguments.size() !=
                rhs_dependent->template_arguments.size()) {
            return false;
        }
        if (!cpp_out_of_line_type_matches(
                lhs_dependent->qualifier_type,
                rhs_dependent->qualifier_type,
                false)) {
            return false;
        }
        for (size_t idx = 0; idx < lhs_dependent->template_arguments.size(); ++idx) {
            const auto& lhs_argument = lhs_dependent->template_arguments[idx];
            const auto& rhs_argument = rhs_dependent->template_arguments[idx];
            if (lhs_argument.kind != rhs_argument.kind) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Type &&
                !cpp_out_of_line_type_matches(
                    lhs_argument.type,
                    rhs_argument.type,
                    false)) {
                return false;
            }
            if (lhs_argument.kind == TemplateArgumentKind::Value &&
                !lhs_argument.equals(rhs_argument)) {
                return false;
            }
        }
        return true;
    }
    if (auto* lhs_vector = dyn_cast<VectorType>(lhs_raw)) {
        auto* rhs_vector = dyn_cast<VectorType>(rhs_raw);
        return rhs_vector &&
               lhs_vector->total_bytes == rhs_vector->total_bytes &&
               cpp_out_of_line_type_matches(
                   lhs_vector->element_type,
                   rhs_vector->element_type,
                   false);
    }

    return ignore_top_level_qualifiers
        ? lhs.equals_unqualified(rhs)
        : lhs.equals_qualified(rhs);
}

inline bool cpp_primary_template_owner_matches(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments) {
    if (!class_template) {
        return false;
    }
    TemplateArgumentBindings bindings;
    if (!bind_template_arguments_to_parameters(
            class_template->parameters,
            arguments,
            bindings,
            nullptr)) {
        return false;
    }
    if (bindings.size() != class_template->parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < bindings.size(); ++idx) {
        const auto* argument = bindings[idx].single_argument();
        if (!argument) {
            return false;
        }
        if (auto* type_parameter =
                dyn_cast<TemplateTypeParmDecl>(class_template->parameters[idx].get())) {
            if (argument->kind != TemplateArgumentKind::Type ||
                !argument->type ||
                argument->type.get_qualifiers() != QUAL_NONE) {
                return false;
            }
            auto argument_type = desugar_typedefs(argument->type);
            auto* argument_parm =
                dyn_cast<TemplateTypeParmType>(argument_type.get());
            const auto* expected_parm = type_parameter->type.get();
            if (!argument_parm || !expected_parm ||
                argument_parm->depth != expected_parm->depth ||
                argument_parm->index != expected_parm->index) {
                return false;
            }
            continue;
        }
        auto* non_type_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(class_template->parameters[idx].get());
        if (!non_type_parameter ||
            argument->kind != TemplateArgumentKind::Value ||
            !argument->is_dependent ||
            argument->referenced_parameter != non_type_parameter) {
            return false;
        }
    }
    return true;
}

#endif // ABURI_PARSER_CPP_OUT_OF_LINE_MATCH_H
