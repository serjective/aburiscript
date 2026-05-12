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

namespace {
const TemplateDecl* template_decl_from_decl_for_lookup(const Decl* decl) {
    if (!decl) {
        return nullptr;
    }
    switch (decl->get_kind()) {
        case DeclKind::AliasTemplateDecl:
        case DeclKind::FunctionTemplateDecl:
        case DeclKind::VariableTemplateDecl:
        case DeclKind::ClassTemplateDecl:
        case DeclKind::ConceptDecl:
        case DeclKind::CppDeductionGuideDecl:
        case DeclKind::VariableTemplatePartialSpecializationDecl:
        case DeclKind::ClassTemplatePartialSpecializationDecl:
            return static_cast<const TemplateDecl*>(decl);
        default:
            return nullptr;
    }
}

bool template_decl_defines_lookup_entity(const TemplateDecl* decl) {
    if (!decl) {
        return false;
    }
    if (auto* function_template =
            dyn_cast<FunctionTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        return function_decl_defines_entity(function_template->function_decl());
    }
    if (auto* class_template =
            dyn_cast<ClassTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        return class_template->record_decl() &&
               class_template->record_decl()->is_definition;
    }
    if (auto* variable_template =
            dyn_cast<VariableTemplateDecl>(const_cast<TemplateDecl*>(decl))) {
        auto* variable = variable_template->variable_decl();
        return variable &&
               (variable->init ||
                variable->storage_class != StorageClass::EXTERN);
    }
    if (auto* partial =
            dyn_cast<ClassTemplatePartialSpecializationDecl>(
                const_cast<TemplateDecl*>(decl))) {
        return partial->record_decl() && partial->record_decl()->is_definition;
    }
    if (auto* variable_partial =
            dyn_cast<VariableTemplatePartialSpecializationDecl>(
                const_cast<TemplateDecl*>(decl))) {
        auto* variable = variable_partial->variable_decl();
        return variable &&
               (variable->init ||
                variable->storage_class != StorageClass::EXTERN);
    }
    return true;
}

const FunctionTemplateDecl* function_template_from_decl_for_lookup(
    const Decl* decl) {
    return dyn_cast<FunctionTemplateDecl>(
        const_cast<TemplateDecl*>(template_decl_from_decl_for_lookup(decl)));
}

bool function_template_lookup_owners_match(const FuncDecl* lhs,
                                           const FuncDecl* rhs) {
    if (!lhs || !rhs) {
        return lhs == rhs;
    }

    QualType lhs_owner = get_func_decl_owner_record_type(lhs);
    QualType rhs_owner = get_func_decl_owner_record_type(rhs);
    if (lhs_owner || rhs_owner) {
        return lhs_owner.equals_unqualified(rhs_owner);
    }

    const std::string* lhs_prefix = get_func_decl_cxx_qualifier_prefix(lhs);
    const std::string* rhs_prefix = get_func_decl_cxx_qualifier_prefix(rhs);
    if (lhs_prefix || rhs_prefix) {
        return lhs_prefix && rhs_prefix && *lhs_prefix == *rhs_prefix;
    }

    return true;
}

bool template_parameters_have_same_lookup_shape(
    const TemplateParameterList& lhs,
    const TemplateParameterList& rhs);

bool template_parameter_has_lookup_constraint(
    const TemplateParameterDecl* parameter) {
    if (!parameter) {
        return false;
    }
    if (auto* type_parameter = dyn_cast<TemplateTypeParmDecl>(
            const_cast<TemplateParameterDecl*>(parameter))) {
        return type_parameter->type_constraint != nullptr;
    }
    return false;
}

bool template_parameters_have_same_lookup_shape(
    const TemplateParameterList& lhs,
    const TemplateParameterList& rhs) {
    if (lhs.size() != rhs.size()) {
        return false;
    }
    for (size_t idx = 0; idx < lhs.size(); ++idx) {
        const TemplateParameterDecl* lhs_parameter = lhs[idx].get();
        const TemplateParameterDecl* rhs_parameter = rhs[idx].get();
        if (!lhs_parameter || !rhs_parameter) {
            if (lhs_parameter != rhs_parameter) {
                return false;
            }
            continue;
        }
        if (lhs_parameter->get_kind() != rhs_parameter->get_kind() ||
            lhs_parameter->depth != rhs_parameter->depth ||
            lhs_parameter->index != rhs_parameter->index ||
            lhs_parameter->is_parameter_pack !=
                rhs_parameter->is_parameter_pack ||
            template_parameter_has_lookup_constraint(lhs_parameter) ||
            template_parameter_has_lookup_constraint(rhs_parameter)) {
            return false;
        }

        if (auto* lhs_non_type = dyn_cast<TemplateNonTypeParmDecl>(
                const_cast<TemplateParameterDecl*>(lhs_parameter))) {
            auto* rhs_non_type = dyn_cast<TemplateNonTypeParmDecl>(
                const_cast<TemplateParameterDecl*>(rhs_parameter));
            if (!rhs_non_type ||
                !template_parameter_types_have_same_lookup_shape(
                    lhs_non_type->type,
                    rhs_non_type->type)) {
                return false;
            }
            continue;
        }

        if (auto* lhs_template = dyn_cast<TemplateTemplateParmDecl>(
                const_cast<TemplateParameterDecl*>(lhs_parameter))) {
            auto* rhs_template = dyn_cast<TemplateTemplateParmDecl>(
                const_cast<TemplateParameterDecl*>(rhs_parameter));
            if (!rhs_template ||
                !template_parameters_have_same_lookup_shape(
                    lhs_template->parameters,
                    rhs_template->parameters)) {
                return false;
            }
        }
    }
    return true;
}

bool function_templates_have_same_structural_lookup_identity(
    const FunctionTemplateDecl* lhs,
    const FunctionTemplateDecl* rhs) {
    if (!lhs || !rhs) {
        return lhs == rhs;
    }
    if (lhs->associated_constraint || rhs->associated_constraint) {
        return false;
    }

    const FuncDecl* lhs_function = lhs->function_decl();
    const FuncDecl* rhs_function = rhs->function_decl();
    if (!lhs_function || !rhs_function) {
        return false;
    }
    if (lhs_function->trailing_requires_clause ||
        rhs_function->trailing_requires_clause) {
        return false;
    }
    if (lhs_function->name != rhs_function->name) {
        return false;
    }
    if (!function_template_lookup_owners_match(lhs_function, rhs_function)) {
        return false;
    }
    if (!template_parameters_have_same_lookup_shape(
            lhs->parameters,
            rhs->parameters)) {
        return false;
    }

    auto lhs_type =
        desugar_type(QualType(lhs_function->type)).as_shared<FunctionType>();
    auto rhs_type =
        desugar_type(QualType(rhs_function->type)).as_shared<FunctionType>();
    if (!lhs_type || !rhs_type) {
        return false;
    }
    if (lhs_type->parameters.size() != rhs_type->parameters.size()) {
        return false;
    }
    if (lhs_type->is_variadic != rhs_type->is_variadic) {
        return false;
    }
    if (lhs_type->has_prototype != rhs_type->has_prototype) {
        return false;
    }
    if (lhs_type->member_ref_qualifier != rhs_type->member_ref_qualifier) {
        return false;
    }
    if (!function_exception_specs_equal(*lhs_type, *rhs_type)) {
        return false;
    }
    if (!template_parameter_types_have_same_lookup_shape(lhs_type->ret_type,
                                                        rhs_type->ret_type)) {
        return false;
    }

    for (size_t idx = 0; idx < lhs_type->parameters.size(); ++idx) {
        if (!template_parameter_types_have_same_lookup_shape(
                lhs_type->parameters[idx],
                rhs_type->parameters[idx])) {
            return false;
        }
    }

    return true;
}
} // namespace

const TemplateDecl* get_template_decl_lookup_identity(const Decl* decl) {
    const TemplateDecl* template_decl = template_decl_from_decl_for_lookup(decl);
    if (!template_decl) {
        return nullptr;
    }
    const TemplateDecl* canonical = get_template_decl_canonical_decl(template_decl);
    return canonical ? canonical : template_decl;
}

bool template_decls_share_lookup_identity(const Decl* lhs, const Decl* rhs) {
    const TemplateDecl* lhs_identity = get_template_decl_lookup_identity(lhs);
    const TemplateDecl* rhs_identity = get_template_decl_lookup_identity(rhs);
    if (lhs_identity && rhs_identity && lhs_identity == rhs_identity) {
        return true;
    }
    return function_templates_have_same_structural_lookup_identity(
        function_template_from_decl_for_lookup(lhs),
        function_template_from_decl_for_lookup(rhs));
}

bool template_decl_is_preferred_lookup_representative(
    const Decl* existing,
    const Decl* candidate) {
    const TemplateDecl* existing_template =
        template_decl_from_decl_for_lookup(existing);
    const TemplateDecl* candidate_template =
        template_decl_from_decl_for_lookup(candidate);
    if (!candidate_template) {
        return false;
    }
    if (!existing_template) {
        return true;
    }

    bool existing_defines =
        template_decl_defines_lookup_entity(existing_template);
    bool candidate_defines =
        template_decl_defines_lookup_entity(candidate_template);
    if (candidate_defines != existing_defines) {
        return candidate_defines;
    }
    return true;
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
    if (c == "<=>") return BinOpTypes::THREE_WAY_COMPARE;
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
bool is_compound_assignment_binop(BinOpTypes typ) {
    return is_assignment_binop(typ) && typ != BinOpTypes::ASSIGN;
}
bool is_binary_operator(std::string c) {
    if (string2bop(c) != BinOpTypes::UNKNOWN) return true;
    return false;

}
