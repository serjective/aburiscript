#include "ast.h"
#include "ast_context.h"

namespace {
// Threading: this compiler assumes single-threaded compilation per process.
// fallback_side_table_context provides a default ASTContext for side-table
// lookups when no explicit context is active.  It is NOT thread-safe.
// If parallel compilation is introduced, move into a session-owned context.
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

ASTContext& side_table_context_for(const FuncDecl* decl) {
    if (ASTContext* active = get_active_side_table_ast_context()) {
        return *active;
    }
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return *owner;
    }
    return fallback_side_table_context();
}

ASTContext& side_table_context_for(const TemplateDecl* decl) {
    if (ASTContext* active = get_active_side_table_ast_context()) {
        return *active;
    }
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return *owner;
    }
    return fallback_side_table_context();
}

ASTContext& side_table_context_for(const TemplateParameterDecl* decl) {
    if (ASTContext* active = get_active_side_table_ast_context()) {
        return *active;
    }
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return *owner;
    }
    return fallback_side_table_context();
}

ASTContext& side_table_context_for(const ParamDecl* decl) {
    if (ASTContext* active = get_active_side_table_ast_context()) {
        return *active;
    }
    if (ASTContext* owner = get_side_table_ast_context_for(decl)) {
        return *owner;
    }
    return fallback_side_table_context();
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
    record_semantics_cache_set(closure_decl.get(), std::move(closure_state));

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
    record_semantics_cache_set(literal_decl.get(), std::move(literal_state));

    info.literal_semantic_decl = std::move(literal_decl);
    return info;
}

void set_func_decl_cxx_qualifier_prefix(const FuncDecl* decl,
                                        std::optional<std::string> prefix) {
    side_table_context_for(decl).set_func_decl_cxx_qualifier_prefix(decl, std::move(prefix));
}

const std::string* get_func_decl_cxx_qualifier_prefix(const FuncDecl* decl) {
    return side_table_context_for(decl).get_func_decl_cxx_qualifier_prefix(decl);
}

void clear_func_decl_cxx_qualifier_prefixes() {
    current_side_table_context().clear_func_decl_cxx_qualifier_prefixes();
}

void set_func_decl_owner_record_type(const FuncDecl* decl, QualType owner_type) {
    side_table_context_for(decl).set_func_decl_owner_record_type(decl, owner_type);
}

QualType get_func_decl_owner_record_type(const FuncDecl* decl) {
    return side_table_context_for(decl).get_func_decl_owner_record_type(decl);
}

void clear_func_decl_owner_record_types() {
    current_side_table_context().clear_func_decl_owner_record_types();
}

void set_func_decl_function_template_specialization(
    const FuncDecl* decl,
    const FunctionTemplateSpecializationInfo& info) {
    side_table_context_for(decl).set_func_decl_function_template_specialization(
        decl, info);
}

const FunctionTemplateSpecializationInfo*
get_func_decl_function_template_specialization(const FuncDecl* decl) {
    return side_table_context_for(decl)
        .get_func_decl_function_template_specialization(decl);
}

void clear_func_decl_function_template_specializations() {
    current_side_table_context().clear_func_decl_function_template_specializations();
}

void set_template_decl_canonical_decl(const TemplateDecl* decl,
                                      const TemplateDecl* canonical_decl) {
    side_table_context_for(decl).set_template_decl_canonical_decl(
        decl, canonical_decl);
}

const TemplateDecl* get_template_decl_canonical_decl(const TemplateDecl* decl) {
    return side_table_context_for(decl).get_template_decl_canonical_decl(decl);
}

void clear_template_decl_canonical_decls() {
    current_side_table_context().clear_template_decl_canonical_decls();
}

void set_template_parameter_default_argument(
    const TemplateParameterDecl* decl,
    std::optional<TemplateArgument> argument) {
    side_table_context_for(decl).set_template_parameter_default_argument(
        decl, std::move(argument));
}

const TemplateArgument* get_template_parameter_default_argument(
    const TemplateParameterDecl* decl) {
    return side_table_context_for(decl).get_template_parameter_default_argument(
        decl);
}

void clear_template_parameter_default_arguments() {
    current_side_table_context().clear_template_parameter_default_arguments();
}

bool merge_template_decl_default_arguments(
    const TemplateDecl* decl,
    size_t* conflict_param_index) {
    return side_table_context_for(decl).merge_template_decl_default_arguments(
        decl, conflict_param_index);
}

const std::vector<std::optional<TemplateArgument>>*
get_template_decl_default_arguments(const TemplateDecl* decl) {
    return side_table_context_for(decl).get_template_decl_default_arguments(
        decl);
}

void clear_template_decl_default_arguments() {
    current_side_table_context().clear_template_decl_default_arguments();
}

void set_param_decl_default_argument(const ParamDecl* decl,
                                     std::unique_ptr<Expr> expr) {
    side_table_context_for(decl).set_param_decl_default_argument(decl, std::move(expr));
}

const Expr* get_param_decl_default_argument(const ParamDecl* decl) {
    return side_table_context_for(decl).get_param_decl_default_argument(decl);
}

void clear_param_decl_default_arguments() {
    current_side_table_context().clear_param_decl_default_arguments();
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
