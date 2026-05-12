#include "symbols.h"
#include "ast_context.h"

namespace {
ASTContext* current_side_table_context() {
    return get_active_side_table_ast_context();
}

ASTContext* side_table_context_for(const Symbol* sym) {
    if (ASTContext* owner = get_side_table_ast_context_for(sym)) {
        return owner;
    }
    return get_active_side_table_ast_context();
}
} // namespace

VariableLinkage function_symbol_linkage_for_storage(
    StorageClass storage_class,
    bool is_cpp_member_function) {
    if (storage_class == StorageClass::STATIC && !is_cpp_member_function) {
        return VariableLinkage::INTERNAL;
    }
    return VariableLinkage::EXTERNAL;
}

void set_symbol_cxx_qualifier_prefix(const Symbol* sym,
                                     std::optional<std::string> prefix) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        ctx->set_symbol_cxx_qualifier_prefix(sym, std::move(prefix));
    }
}

const std::string* get_symbol_cxx_qualifier_prefix(const Symbol* sym) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        return ctx->get_symbol_cxx_qualifier_prefix(sym);
    }
    return nullptr;
}

void clear_symbol_cxx_qualifier_prefixes() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_symbol_cxx_qualifier_prefixes();
    }
}

void set_symbol_owner_record_type(const Symbol* sym, QualType owner_type) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        ctx->set_symbol_owner_record_type(sym, owner_type);
    }
}

QualType get_symbol_owner_record_type(const Symbol* sym) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        return ctx->get_symbol_owner_record_type(sym);
    }
    return QualType();
}

void clear_symbol_owner_record_types() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_symbol_owner_record_types();
    }
}

void set_symbol_function_template_specialization(
    const Symbol* sym,
    const FunctionTemplateSpecializationInfo& info) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        ctx->set_symbol_function_template_specialization(sym, info);
    }
}

const FunctionTemplateSpecializationInfo*
get_symbol_function_template_specialization(const Symbol* sym) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        return ctx->get_symbol_function_template_specialization(sym);
    }
    return nullptr;
}

void clear_symbol_function_template_specializations() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_symbol_function_template_specializations();
    }
}

void set_symbol_variable_template_specialization(
    const Symbol* sym,
    const VariableTemplateSpecializationInfo& info) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        ctx->set_symbol_variable_template_specialization(sym, info);
    }
}

const VariableTemplateSpecializationInfo*
get_symbol_variable_template_specialization(const Symbol* sym) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        return ctx->get_symbol_variable_template_specialization(sym);
    }
    return nullptr;
}

void clear_symbol_variable_template_specializations() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_symbol_variable_template_specializations();
    }
}

bool merge_symbol_cpp_default_arguments(
    const Symbol* sym,
    const std::vector<const Expr*>& defaults,
    size_t* conflict_param_index) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        return ctx->merge_symbol_cpp_default_arguments(
            sym, defaults, conflict_param_index);
    }
    return false;
}

const std::vector<const Expr*>* get_symbol_cpp_default_arguments(
    const Symbol* sym) {
    if (ASTContext* ctx = side_table_context_for(sym)) {
        return ctx->get_symbol_cpp_default_arguments(sym);
    }
    return nullptr;
}

void clear_symbol_cpp_default_arguments() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_symbol_cpp_default_arguments();
    }
}
