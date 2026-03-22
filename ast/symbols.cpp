#include "symbols.h"
#include "ast_context.h"

namespace {
// Threading: see ast.cpp — same singleton pattern.  NOT thread-safe.
ASTContext& fallback_side_table_context() {
    static ASTContext fallback;
    return fallback;
}

ASTContext& current_side_table_context() {
    if (ASTContext* active = get_active_side_table_ast_context()) {
        return *active;
    }
    return fallback_side_table_context();
}

ASTContext& side_table_context_for(const Symbol* sym) {
    if (ASTContext* active = get_active_side_table_ast_context()) {
        return *active;
    }
    if (ASTContext* owner = get_side_table_ast_context_for(sym)) {
        return *owner;
    }
    return fallback_side_table_context();
}
} // namespace

void set_symbol_cxx_qualifier_prefix(const Symbol* sym,
                                     std::optional<std::string> prefix) {
    side_table_context_for(sym).set_symbol_cxx_qualifier_prefix(sym, std::move(prefix));
}

const std::string* get_symbol_cxx_qualifier_prefix(const Symbol* sym) {
    return side_table_context_for(sym).get_symbol_cxx_qualifier_prefix(sym);
}

void clear_symbol_cxx_qualifier_prefixes() {
    current_side_table_context().clear_symbol_cxx_qualifier_prefixes();
}

void set_symbol_owner_record_type(const Symbol* sym, QualType owner_type) {
    side_table_context_for(sym).set_symbol_owner_record_type(sym, owner_type);
}

QualType get_symbol_owner_record_type(const Symbol* sym) {
    return side_table_context_for(sym).get_symbol_owner_record_type(sym);
}

void clear_symbol_owner_record_types() {
    current_side_table_context().clear_symbol_owner_record_types();
}

void set_symbol_function_template_specialization(
    const Symbol* sym,
    const FunctionTemplateSpecializationInfo& info) {
    side_table_context_for(sym).set_symbol_function_template_specialization(
        sym, info);
}

const FunctionTemplateSpecializationInfo*
get_symbol_function_template_specialization(const Symbol* sym) {
    return side_table_context_for(sym)
        .get_symbol_function_template_specialization(sym);
}

void clear_symbol_function_template_specializations() {
    current_side_table_context().clear_symbol_function_template_specializations();
}

bool merge_symbol_cpp_default_arguments(
    const Symbol* sym,
    const std::vector<const Expr*>& defaults,
    size_t* conflict_param_index) {
    return side_table_context_for(sym).merge_symbol_cpp_default_arguments(
        sym, defaults, conflict_param_index);
}

const std::vector<const Expr*>* get_symbol_cpp_default_arguments(
    const Symbol* sym) {
    return side_table_context_for(sym).get_symbol_cpp_default_arguments(sym);
}

void clear_symbol_cpp_default_arguments() {
    current_side_table_context().clear_symbol_cpp_default_arguments();
}
