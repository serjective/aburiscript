#include "ast.h"
#include "ast_context.h"

namespace {
ASTContext* current_side_table_context() {
    return get_active_side_table_ast_context();
}

ASTContext* side_table_context_for(const FuncDecl* decl) {
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return owner;
    }
    return get_active_side_table_ast_context();
}

ASTContext* side_table_context_for(const VariableDecl* decl) {
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return owner;
    }
    return get_active_side_table_ast_context();
}

ASTContext* side_table_context_for(const TemplateDecl* decl) {
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return owner;
    }
    return get_active_side_table_ast_context();
}

ASTContext* side_table_context_for(const TemplateParameterDecl* decl) {
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return owner;
    }
    return get_active_side_table_ast_context();
}

ASTContext* side_table_context_for(const ParamDecl* decl) {
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return owner;
    }
    return get_active_side_table_ast_context();
}
} // namespace

std::string make_lambda_closure_internal_name(SrcLoc loc) {
    if (!loc.isInvalid()) {
        return "__lambda_" + std::to_string(loc.offset);
    }
    return "__lambda_invalid";
}

std::string make_block_internal_name(SrcLoc loc) {
    if (!loc.isInvalid()) {
        return "__block_" + std::to_string(loc.offset);
    }
    return "__block_invalid";
}

LambdaSemanticInfo make_lambda_semantic_info(ASTContext& ctx, SrcLoc loc) {
    LambdaSemanticInfo info;
    auto base_name = make_lambda_closure_internal_name(loc);
    auto closure_type = std::make_shared<ObjectType>(base_name, false, false);
    auto closure_decl =
        make_ast<ObjectDecl>(ctx, base_name, closure_type, false, loc);
    closure_decl->tag =
        base_name + "_" + std::to_string(closure_decl->node_id);

    // Treat the synthesized closure as a complete empty C++ object now so
    // ordinary uses like `auto f = [] {};` can move onto a real object type
    // before generated members and captures are added later.
    RecordSemanticState closure_state;
    closure_state.is_incomplete = false;
    closure_state.alignment = 1;
    closure_state.non_virtual_alignment = 1;
    closure_state.size_bits = 8;
    closure_state.non_virtual_size_bits = 8;
    record_semantics_cache_set(&ctx, closure_decl.get(), std::move(closure_state));

    ctx.set_cpp_lambda_closure_decl_info(
        closure_decl->node_id,
        CppLambdaClosureDeclInfo{});

    info.closure_semantic_decl = std::move(closure_decl);
    return info;
}

BlockSemanticInfo make_block_semantic_info(ASTContext& ctx, SrcLoc loc) {
    BlockSemanticInfo info;
    auto base_name = make_block_internal_name(loc);
    auto literal_type = std::make_shared<ObjectType>(base_name, false, false);
    auto literal_decl =
        make_ast<ObjectDecl>(ctx, base_name, literal_type, false, loc);
    literal_decl->tag =
        base_name + "_" + std::to_string(literal_decl->node_id);

    RecordSemanticState literal_state;
    literal_state.is_incomplete = false;
    literal_state.alignment = 1;
    literal_state.non_virtual_alignment = 1;
    literal_state.size_bits = 8;
    literal_state.non_virtual_size_bits = 8;
    record_semantics_cache_set(&ctx, literal_decl.get(), std::move(literal_state));

    info.literal_semantic_decl = std::move(literal_decl);
    return info;
}

void set_func_decl_cxx_qualifier_prefix(const FuncDecl* decl,
                                        std::optional<std::string> prefix) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_func_decl_cxx_qualifier_prefix(decl, std::move(prefix));
    }
}

const std::string* get_func_decl_cxx_qualifier_prefix(const FuncDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_func_decl_cxx_qualifier_prefix(decl);
    }
    return nullptr;
}

void clear_func_decl_cxx_qualifier_prefixes() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_func_decl_cxx_qualifier_prefixes();
    }
}

void set_func_decl_owner_record_type(const FuncDecl* decl, QualType owner_type) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_func_decl_owner_record_type(decl, owner_type);
    }
}

QualType get_func_decl_owner_record_type(const FuncDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_func_decl_owner_record_type(decl);
    }
    return QualType();
}

void clear_func_decl_owner_record_types() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_func_decl_owner_record_types();
    }
}

void set_func_decl_function_template_specialization(
    const FuncDecl* decl,
    const FunctionTemplateSpecializationInfo& info) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_func_decl_function_template_specialization(decl, info);
    }
}

const FunctionTemplateSpecializationInfo*
get_func_decl_function_template_specialization(const FuncDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_func_decl_function_template_specialization(decl);
    }
    return nullptr;
}

void clear_func_decl_function_template_specializations() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_func_decl_function_template_specializations();
    }
}

void set_variable_decl_variable_template_specialization(
    const VariableDecl* decl,
    const VariableTemplateSpecializationInfo& info) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_variable_decl_variable_template_specialization(decl, info);
    }
}

const VariableTemplateSpecializationInfo*
get_variable_decl_variable_template_specialization(const VariableDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_variable_decl_variable_template_specialization(decl);
    }
    return nullptr;
}

void clear_variable_decl_variable_template_specializations() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_variable_decl_variable_template_specializations();
    }
}

void set_template_decl_canonical_decl(const TemplateDecl* decl,
                                      const TemplateDecl* canonical_decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_template_decl_canonical_decl(decl, canonical_decl);
    }
}

const TemplateDecl* get_template_decl_canonical_decl(const TemplateDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_template_decl_canonical_decl(decl);
    }
    return nullptr;
}

void clear_template_decl_canonical_decls() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_template_decl_canonical_decls();
    }
}

void set_template_parameter_default_argument(
    const TemplateParameterDecl* decl,
    std::optional<TemplateArgument> argument) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_template_parameter_default_argument(decl, std::move(argument));
    }
}

const TemplateArgument* get_template_parameter_default_argument(
    const TemplateParameterDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_template_parameter_default_argument(decl);
    }
    return nullptr;
}

void clear_template_parameter_default_arguments() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_template_parameter_default_arguments();
    }
}

bool merge_template_decl_default_arguments(
    const TemplateDecl* decl,
    size_t* conflict_param_index) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->merge_template_decl_default_arguments(
            decl, conflict_param_index);
    }
    return false;
}

const std::vector<std::optional<TemplateArgument>>*
get_template_decl_default_arguments(const TemplateDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_template_decl_default_arguments(decl);
    }
    return nullptr;
}

void clear_template_decl_default_arguments() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_template_decl_default_arguments();
    }
}

void set_param_decl_default_argument(const ParamDecl* decl,
                                     std::unique_ptr<Expr> expr) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        ctx->set_param_decl_default_argument(decl, std::move(expr));
    }
}

const Expr* get_param_decl_default_argument(const ParamDecl* decl) {
    if (ASTContext* ctx = side_table_context_for(decl)) {
        return ctx->get_param_decl_default_argument(decl);
    }
    return nullptr;
}

void clear_param_decl_default_arguments() {
    if (ASTContext* ctx = current_side_table_context()) {
        ctx->clear_param_decl_default_arguments();
    }
}

bool is_unary_operator(std::string& c) {
    // ++ and -- are handled differently in terms of unary_expression parsing, see 6.5.3 C spec
    if (c == "&" || c == "*" || c == "+" || c == "-" || c == "~" || c == "!" || c == "++" || c == "--") return true;
    return false;
}
UnaryOpTypes string2uop(std::string& c) {
    if (c == "~") return UnaryOpTypes::BITWISE_NOT;
    if (c == "-") return UnaryOpTypes::NEG;
    if (c == "+") return UnaryOpTypes::POSITIVE;
    if (c == "!") return UnaryOpTypes::LOGICAL_NOT;
    if (c == "++") return UnaryOpTypes::INCREMENT;
    if (c == "--") return UnaryOpTypes::DECREMENT;
    if (c == "*") return UnaryOpTypes::DEREFERENCE;
    if (c == "&") return UnaryOpTypes::ADDRESS_OF;
    return UnaryOpTypes::UNKNOWN;
}
BinOpTypes string2bop(std::string& c) {
    if (c == ",") return BinOpTypes::COMMA;
    if (c == ".*") return BinOpTypes::MEMBER_PTR_DOT;
    if (c == "->*") return BinOpTypes::MEMBER_PTR_ARROW;
    if (c == "*") return BinOpTypes::MULT;
    if (c == "/") return BinOpTypes::DIV;
    if (c == "%") return BinOpTypes::MOD;
    if (c == "+") return BinOpTypes::ADD;
    if (c == "-") return BinOpTypes::SUB;
    if (c == "&") return BinOpTypes::BITWISE_AND;
    if (c == "|") return BinOpTypes::BITWISE_OR;
    if (c == "^") return BinOpTypes::BITWISE_XOR;
    if (c == "?") return BinOpTypes::QUESTION;
    if (c == "&&") return BinOpTypes::LOGICAL_AND;
    if (c == "||") return BinOpTypes::LOGICAL_OR;
    if (c == "^") return BinOpTypes::BITWISE_XOR;
    if (c == "&&") return BinOpTypes::LOGICAL_AND;
    if (c == "||") return BinOpTypes::LOGICAL_OR;
    if (c == "<<") return BinOpTypes::SHIFT_LEFT;
    if (c == ">>") return BinOpTypes::SHIFT_RIGHT;
    if (c == "<") return BinOpTypes::LESS_THAN;
    if (c == "<=") return BinOpTypes::LESS_EQUAL_THAN;
    if (c == ">=") return BinOpTypes::GREATER_EQUAL_THAN;
    if (c == ">") return BinOpTypes::GREATER_THAN;
    if (c == "!=") return BinOpTypes::NOT_EQUAL;
    if (c == "==") return BinOpTypes::EQUAL;
    if (c == "=") return BinOpTypes::ASSIGN;
    if (c == "+=") return BinOpTypes::ASSIGN_ADD;
    if (c == "-=") return BinOpTypes::ASSIGN_SUB;
    if (c == "*=") return BinOpTypes::ASSIGN_MUL;
    if (c == "/=") return BinOpTypes::ASSIGN_DIV;
    if (c == "%=") return BinOpTypes::ASSIGN_MOD;
    if (c == "&=") return BinOpTypes::ASSIGN_AND;
    if (c == "|=") return BinOpTypes::ASSIGN_OR;
    if (c == "^=") return BinOpTypes::ASSIGN_XOR;
    if (c == "<<=") return BinOpTypes::ASSIGN_LSHIFT;
    if (c == ">>=") return BinOpTypes::ASSIGN_RSHIFT;
    return BinOpTypes::UNKNOWN;
}
bool is_assignment_binop(BinOpTypes typ) {
    switch (typ) {
        case BinOpTypes::ASSIGN:
        case BinOpTypes::ASSIGN_ADD:
        case BinOpTypes::ASSIGN_SUB:
        case BinOpTypes::ASSIGN_DIV:
        case BinOpTypes::ASSIGN_MOD:
        case BinOpTypes::ASSIGN_MUL:
        case BinOpTypes::ASSIGN_AND:
        case BinOpTypes::ASSIGN_OR:
        case BinOpTypes::ASSIGN_XOR:
        case BinOpTypes::ASSIGN_LSHIFT:
        case BinOpTypes::ASSIGN_RSHIFT:
            return true;
        default:
            return false;
    }
}
bool is_binary_operator(std::string c) {
    if (string2bop(c) != BinOpTypes::UNKNOWN) return true;
    return false;

}
