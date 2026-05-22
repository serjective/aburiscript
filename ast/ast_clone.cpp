#include "ast_clone.h"

#include "ast_context.h"
#include "expr_clone.h"
#include "../constexpr/consteval_compat.h"

#include <type_traits>

namespace {
template <typename NodeType>
void assign_node_id(NodeType* node, ASTContext* ast_ctx) {
    if (node && ast_ctx) {
        node->node_id = ast_ctx->next_node_id();
    }
}

std::unique_ptr<Stmt> fail_stmt_clone(std::string* error_out,
                                      const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return nullptr;
}

std::unique_ptr<Decl> fail_decl_clone(std::string* error_out,
                                      const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return nullptr;
}

bool set_expr_error(std::string* error_out, const std::string& message) {
    if (error_out && error_out->empty()) {
        *error_out = message;
    }
    return false;
}

QualType get_sizeof_result_type(ASTContext* ast_ctx) {
    if (ast_ctx && ast_ctx->type_ctx) {
        if (auto size_t_type =
                ast_ctx->type_ctx->get_builtin(BuiltinTypes::ULong)) {
            return QualType(size_t_type);
        }
        if (auto int_type = ast_ctx->type_ctx->get_builtin(BuiltinTypes::Int)) {
            return QualType(int_type);
        }
    }
    return nullptr;
}

std::unique_ptr<Expr> make_pack_size_integer_literal(size_t pack_size,
                                                     ASTContext* ast_ctx,
                                                     SrcLoc loc) {
    auto value = std::to_string(pack_size);
    const std::string* interned_value =
        ast_ctx ? ast_ctx->intern_identifier(value) : nullptr;
    auto result_type = get_sizeof_result_type(ast_ctx);
    std::unique_ptr<Expr> literal;
    if (interned_value) {
        literal =
            std::make_unique<IntegerLiteral>(interned_value, result_type, loc);
    } else {
        literal = std::make_unique<IntegerLiteral>(
            std::move(value),
            result_type,
            loc);
    }
    assign_node_id(literal.get(), ast_ctx);
    return literal;
}

QualType rewrite_type(QualType type, ASTCloneContext& ctx) {
    // Cloned lambdas and nested templates synthesize fresh semantic owners.
    // Walk composite types after the caller's rewrite hook so references to
    // those fresh declarations stay internally consistent.
    auto apply_clone_type_remaps =
        [&](auto&& self, QualType current_type) -> QualType {
            if (!current_type) {
                return current_type;
            }

            auto raw = current_type.get_shared();
            uint8_t quals = current_type.get_qualifiers();
            if (!raw) {
                return current_type;
            }

            auto remap_template_argument =
                [&](const TemplateArgument& argument) -> TemplateArgument {
                TemplateArgument remapped = argument;
                switch (argument.kind) {
                    case TemplateArgumentKind::Type:
                        remapped.type = self(self, argument.type);
                        break;
                    case TemplateArgumentKind::Template:
                        if (argument.referenced_parameter) {
                            auto it = ctx.template_parameter_remap.find(
                                argument.referenced_parameter);
                            if (it != ctx.template_parameter_remap.end()) {
                                remapped.referenced_parameter = it->second;
                            }
                        }
                        break;
                    case TemplateArgumentKind::Value:
                        remapped.value_type = self(self, argument.value_type);
                        if (argument.referenced_parameter) {
                            auto it = ctx.template_parameter_remap.find(
                                argument.referenced_parameter);
                            if (it != ctx.template_parameter_remap.end()) {
                                remapped.referenced_parameter = it->second;
                            }
                        }
                        break;
                }
                remapped.is_dependent =
                    template_argument_depends_on_template_parameters(
                        remapped,
                        ctx.ast_ctx);
                return remapped;
            };

            if (auto parm_type = dyn_cast_shared<TemplateTypeParmType>(raw)) {
                if (!parm_type->parameter_decl) {
                    return current_type;
                }
                auto it = ctx.template_parameter_remap.find(
                    parm_type->parameter_decl);
                if (it == ctx.template_parameter_remap.end() || !it->second) {
                    return current_type;
                }
                auto* rebound = dyn_cast<TemplateTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(it->second));
                if (!rebound || !rebound->type) {
                    return current_type;
                }
                return QualType(rebound->type, quals);
            }
            if (auto auto_type = dyn_cast_shared<AutoType>(raw)) {
                if (!auto_type->type_constraint) {
                    return current_type;
                }
                bool changed = false;
                auto rewritten_constraint =
                    std::make_shared<CppTypeConstraint>(
                        *auto_type->type_constraint);
                for (auto& argument :
                     rewritten_constraint->template_arguments) {
                    auto rewritten_argument = remap_template_argument(argument);
                    changed = changed || !rewritten_argument.equals(argument);
                    argument = std::move(rewritten_argument);
                }
                if (!changed) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<AutoType>(
                        auto_type->flavor,
                        std::move(rewritten_constraint)),
                    quals);
            }
            if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
                auto rewritten = self(self, typedef_type->underlying_type);
                if (rewritten.equals_qualified(typedef_type->underlying_type)) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<TypedefType>(
                        typedef_type->name,
                        rewritten,
                        typedef_type->typedef_decl),
                    quals);
            }
            if (auto specialization =
                    dyn_cast_shared<TemplateSpecializationType>(raw)) {
                bool changed = false;
                const Decl* primary_template = specialization->primary_template;
                const TemplateDecl* template_decl = nullptr;
                if (primary_template) {
                    switch (primary_template->get_kind()) {
                        case DeclKind::AliasTemplateDecl:
                        case DeclKind::FunctionTemplateDecl:
                        case DeclKind::VariableTemplateDecl:
                        case DeclKind::ClassTemplateDecl:
                        case DeclKind::VariableTemplatePartialSpecializationDecl:
                        case DeclKind::ClassTemplatePartialSpecializationDecl:
                            template_decl =
                                static_cast<const TemplateDecl*>(
                                    primary_template);
                            break;
                        default:
                            break;
                    }
                }
                if (template_decl) {
                    auto it = ctx.template_decl_remap.find(template_decl);
                    if (it != ctx.template_decl_remap.end() && it->second) {
                        primary_template = it->second;
                        changed = true;
                    }
                }

                std::vector<TemplateArgument> rewritten_arguments;
                rewritten_arguments.reserve(specialization->arguments.size());
                for (const auto& argument : specialization->arguments) {
                    auto rewritten_argument = remap_template_argument(argument);
                    changed = changed || !rewritten_argument.equals(argument);
                    rewritten_arguments.push_back(std::move(rewritten_argument));
                }
                if (!changed) {
                    return current_type;
                }
                auto rewritten_specialization =
                    std::make_shared<TemplateSpecializationType>(
                        specialization->template_name,
                        primary_template,
                        std::move(rewritten_arguments),
                        specialization->is_dependent,
                        specialization->is_class_template_placeholder);
                QualType rewritten_type(rewritten_specialization, quals);
                cache_existing_class_template_specialization_resolved_type(
                    ctx.ast_ctx,
                    rewritten_type,
                    ctx.publish_type_resolution_to_persistent_store);
                return rewritten_type;
            }
            if (auto dependent_name =
                    dyn_cast_shared<DependentNameType>(raw)) {
                auto rewritten_qualifier =
                    self(self, dependent_name->qualifier_type);
                bool changed = !rewritten_qualifier.equals_qualified(
                    dependent_name->qualifier_type);
                std::vector<TemplateArgument> rewritten_arguments;
                rewritten_arguments.reserve(
                    dependent_name->template_arguments.size());
                for (const auto& argument : dependent_name->template_arguments) {
                    auto rewritten_argument = remap_template_argument(argument);
                    changed = changed || !rewritten_argument.equals(argument);
                    rewritten_arguments.push_back(std::move(rewritten_argument));
                }
                if (!changed) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<DependentNameType>(
                        rewritten_qualifier,
                        dependent_name->member_name,
                        std::move(rewritten_arguments),
                        dependent_name->is_current_instantiation,
                        dependent_name->requires_typename_keyword,
                        dependent_name->requires_template_keyword),
                    quals);
            }
            if (auto object = dyn_cast_shared<ObjectType>(raw)) {
                if (ctx.record_type_remap.empty()) {
                    return current_type;
                }
                auto remap_it = ctx.record_type_remap.find(
                    dyn_cast<ObjectDecl>(object->get_decl()));
                if (remap_it == ctx.record_type_remap.end() || !remap_it->second) {
                    return current_type;
                }
                return QualType(
                    remap_it->second.get_shared(),
                    static_cast<uint8_t>(
                        remap_it->second.get_qualifiers() | quals));
            }
            if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
                auto rewritten = self(self, ptr->pointed_type);
                if (rewritten.equals_qualified(ptr->pointed_type)) {
                    return current_type;
                }
                return QualType(std::make_shared<PointerType>(rewritten), quals);
            }
            if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
                auto rewritten = self(self, ref->referred_type);
                if (rewritten.equals_qualified(ref->referred_type)) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<ReferenceType>(
                        rewritten,
                        ref->reference_kind),
                    quals);
            }
            if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
                auto rewritten_class = self(self, mem_ptr->class_type);
                auto rewritten_member = self(self, mem_ptr->member_type);
                if (rewritten_class.equals_qualified(mem_ptr->class_type) &&
                    rewritten_member.equals_qualified(mem_ptr->member_type)) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<MemberPointerType>(
                        rewritten_class,
                        rewritten_member),
                    quals);
            }
            if (auto block_ptr = dyn_cast_shared<BlockPointerType>(raw)) {
                auto rewritten = self(self, block_ptr->pointed_type);
                if (rewritten.equals_qualified(block_ptr->pointed_type)) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<BlockPointerType>(rewritten),
                    quals);
            }
            if (auto transform =
                    dyn_cast_shared<BuiltinTypeTransformType>(raw)) {
                auto rewritten = self(self, transform->operand_type);
                if (rewritten.equals_qualified(transform->operand_type)) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<BuiltinTypeTransformType>(
                        transform->transform_kind,
                        rewritten),
                    quals);
            }
            if (auto array = dyn_cast_shared<ArrayType>(raw)) {
                auto rewritten = self(self, array->element_type);
                if (rewritten.equals_qualified(array->element_type)) {
                    return current_type;
                }
                if (array->size.has_value()) {
                    return QualType(
                        std::make_shared<ArrayType>(rewritten, array->size),
                        quals);
                }
                auto rebuilt =
                    std::make_shared<ArrayType>(rewritten, array->size_expr);
                rebuilt->size_kind = array->size_kind;
                rebuilt->size = array->size;
                return QualType(rebuilt, quals);
            }
            if (auto function = dyn_cast_shared<FunctionType>(raw)) {
                auto rewritten_ret = self(self, function->ret_type);
                bool changed =
                    !rewritten_ret.equals_qualified(function->ret_type);
                auto rebuilt = std::make_shared<FunctionType>(*function);
                rebuilt->ret_type = rewritten_ret;
                for (size_t index = 0; index < rebuilt->parameters.size(); ++index) {
                    auto rewritten_param = self(self, rebuilt->parameters[index]);
                    changed = changed ||
                        !rewritten_param.equals_qualified(
                            rebuilt->parameters[index]);
                    rebuilt->parameters[index] = rewritten_param;
                }
                if (!changed) {
                    return current_type;
                }
                return QualType(rebuilt, quals);
            }
            if (auto pack_element =
                    dyn_cast_shared<BuiltinTypePackElementType>(raw)) {
                bool changed = false;
                std::vector<TemplateArgument> rewritten_args;
                rewritten_args.reserve(pack_element->arguments.size());
                for (const auto& argument : pack_element->arguments) {
                    auto rewritten_argument = remap_template_argument(argument);
                    changed = changed || !rewritten_argument.equals(argument);
                    rewritten_args.push_back(std::move(rewritten_argument));
                }
                if (!changed) {
                    return current_type;
                }
                return QualType(
                    std::make_shared<BuiltinTypePackElementType>(
                        std::move(rewritten_args)),
                    quals);
            }
            return current_type;
    };

    QualType rewritten = ctx.rewrite_type ? ctx.rewrite_type(type) : type;
    return apply_clone_type_remaps(apply_clone_type_remaps, rewritten);
}

bool clone_attribute_list(const AttributeList& source,
                          AttributeList& destination,
                          ASTCloneContext& ctx,
                          std::string* error_out) {
    destination.attrs.reserve(source.attrs.size());
    for (const auto& attr : source.attrs) {
        ParsedAttribute cloned_attr;
        cloned_attr.ns = attr.ns;
        cloned_attr.name = attr.name;
        cloned_attr.loc = attr.loc;
        cloned_attr.resolved_kind = attr.resolved_kind;
        cloned_attr.args.reserve(attr.args.size());
        for (const auto& arg : attr.args) {
            AttributeArg cloned_arg;
            cloned_arg.kind = arg.kind;
            cloned_arg.str_value = arg.str_value;
            cloned_arg.key = arg.key;
            cloned_arg.int_value = arg.int_value;
            cloned_arg.float_value = arg.float_value;
            cloned_arg.loc = arg.loc;
            if (arg.expr_value) {
                auto cloned_expr = clone_expr_with_substitution(
                    arg.expr_value.get(),
                    ctx,
                    error_out);
                if (!cloned_expr) {
                    return false;
                }
                cloned_arg.expr_value =
                    std::shared_ptr<Expr>(cloned_expr.release());
            }
            cloned_attr.args.push_back(std::move(cloned_arg));
        }
        destination.attrs.push_back(std::move(cloned_attr));
    }
    return true;
}

bool rewrite_attribute_list_in_place(AttributeList& attrs,
                                     ASTCloneContext& ctx,
                                     std::string* error_out) {
    for (auto& attr : attrs.attrs) {
        for (auto& arg : attr.args) {
            if (!arg.expr_value) {
                continue;
            }
            auto rewritten_expr = clone_expr_with_substitution(
                arg.expr_value.get(),
                ctx,
                error_out);
            if (!rewritten_expr) {
                return false;
            }
            arg.expr_value = std::shared_ptr<Expr>(rewritten_expr.release());
        }
    }
    return true;
}

bool copy_decl_side_tables_impl(const Decl* source,
                                Decl* destination,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    if (!source || !destination || !ctx.ast_ctx ||
        !ctx.ast_ctx->has_attrs(source->node_id)) {
        return true;
    }
    AttributeList cloned_attrs;
    if (!clone_attribute_list(
            ctx.ast_ctx->get_attrs(source->node_id),
            cloned_attrs,
            ctx,
            error_out)) {
        return false;
    }
    ctx.ast_ctx->set_attrs(destination->node_id, std::move(cloned_attrs));
    return true;
}

std::vector<TemplateArgument> rewrite_template_arguments(
    const std::vector<TemplateArgument>& arguments,
    ASTCloneContext& ctx,
    std::string* error_out) {
    if (!ctx.rewrite_template_arguments) {
        return arguments;
    }
    return ctx.rewrite_template_arguments(arguments, ctx, error_out);
}

bool rewrite_optional_template_arguments(
    std::optional<std::vector<TemplateArgument>>& arguments,
    ASTCloneContext& ctx,
    std::string* error_out) {
    if (!arguments.has_value()) {
        return true;
    }
    auto rewritten = rewrite_template_arguments(*arguments, ctx, error_out);
    if (rewritten.empty() && !arguments->empty() &&
        error_out && !error_out->empty()) {
        return false;
    }
    arguments = std::move(rewritten);
    return true;
}

std::shared_ptr<Symbol> clone_symbol_shallow(const std::shared_ptr<Symbol>& sym,
                                             QualType cloned_type);
void register_symbol(const std::shared_ptr<Symbol>& sym, ASTCloneContext& ctx);

TemplateParameterList clone_template_parameter_list(
    const TemplateParameterList& parameters,
    ASTCloneContext& ctx,
    std::string* error_out) {
    TemplateParameterList cloned_parameters;
    cloned_parameters.reserve(parameters.size());

    auto clone_default_argument =
        [&](const TemplateParameterDecl* source,
            TemplateParameterDecl* destination) -> bool {
        const auto* default_argument =
            get_template_parameter_default_argument(source);
        if (!default_argument) {
            return true;
        }
        auto rewritten_defaults =
            rewrite_template_arguments({*default_argument}, ctx, error_out);
        if (rewritten_defaults.size() != 1) {
            if (error_out && error_out->empty()) {
                *error_out = "failed to clone template parameter default argument";
            }
            return false;
        }
        set_template_parameter_default_argument(
            destination,
            std::move(rewritten_defaults.front()));
        return true;
    };

    for (const auto& parameter : parameters) {
        if (!parameter) {
            if (error_out && error_out->empty()) {
                *error_out = "missing template parameter";
            }
            return {};
        }

        if (auto* type_parameter =
                dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
            auto cloned_parameter_type =
                std::make_shared<TemplateTypeParmType>(
                    type_parameter->name,
                    type_parameter->depth,
                    type_parameter->index,
                    type_parameter->is_parameter_pack);
            auto cloned_parameter =
                std::make_unique<TemplateTypeParmDecl>(
                    type_parameter->name,
                    type_parameter->depth,
                    type_parameter->index,
                    cloned_parameter_type,
                    type_parameter->is_parameter_pack,
                    type_parameter->location);
            assign_node_id(cloned_parameter.get(), ctx.ast_ctx);
            cloned_parameter_type->parameter_decl = cloned_parameter.get();
            if (type_parameter->type_constraint) {
                cloned_parameter->type_constraint =
                    clone_expr_with_substitution(
                        type_parameter->type_constraint.get(),
                        ctx,
                        error_out);
                if (!cloned_parameter->type_constraint) {
                    return {};
                }
            }
            ctx.template_parameter_remap[type_parameter] =
                cloned_parameter.get();
            if (!clone_default_argument(
                    type_parameter,
                    cloned_parameter.get())) {
                return {};
            }
            cloned_parameters.push_back(std::move(cloned_parameter));
            continue;
        }

        if (auto* non_type_parameter =
                dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
            auto cloned_type = rewrite_type(non_type_parameter->type, ctx);
            std::shared_ptr<Symbol> cloned_symbol = nullptr;
            if (non_type_parameter->sym) {
                cloned_symbol = clone_symbol_shallow(
                    non_type_parameter->sym,
                    rewrite_type(non_type_parameter->sym->type, ctx));
                ctx.symbol_remap[non_type_parameter->sym.get()] =
                    cloned_symbol;
                register_symbol(cloned_symbol, ctx);
            }
            auto cloned_parameter =
                std::make_unique<TemplateNonTypeParmDecl>(
                    non_type_parameter->name,
                    non_type_parameter->depth,
                    non_type_parameter->index,
                    cloned_type,
                    cloned_symbol,
                    non_type_parameter->is_parameter_pack,
                    non_type_parameter->location);
            assign_node_id(cloned_parameter.get(), ctx.ast_ctx);
            ctx.template_parameter_remap[non_type_parameter] =
                cloned_parameter.get();
            if (!clone_default_argument(
                    non_type_parameter,
                    cloned_parameter.get())) {
                return {};
            }
            cloned_parameters.push_back(std::move(cloned_parameter));
            continue;
        }

        if (auto* template_parameter =
                dyn_cast<TemplateTemplateParmDecl>(parameter.get())) {
            auto inner_parameters =
                clone_template_parameter_list(
                    template_parameter->parameters,
                    ctx,
                    error_out);
            if (inner_parameters.size() !=
                template_parameter->parameters.size()) {
                return {};
            }
            auto cloned_parameter =
                std::make_unique<TemplateTemplateParmDecl>(
                    std::move(inner_parameters),
                    template_parameter->name,
                    template_parameter->depth,
                    template_parameter->index,
                    template_parameter->uses_typename_keyword,
                    template_parameter->is_parameter_pack,
                    template_parameter->location);
            assign_node_id(cloned_parameter.get(), ctx.ast_ctx);
            ctx.template_parameter_remap[template_parameter] =
                cloned_parameter.get();
            if (!clone_default_argument(
                    template_parameter,
                    cloned_parameter.get())) {
                return {};
            }
            cloned_parameters.push_back(std::move(cloned_parameter));
            continue;
        }

        if (error_out && error_out->empty()) {
            *error_out =
                "unsupported template parameter clone kind " +
                std::to_string(static_cast<int>(parameter->get_kind()));
        }
        return {};
    }

    return cloned_parameters;
}

std::shared_ptr<Symbol> remap_symbol(const std::shared_ptr<Symbol>& sym,
                                     ASTCloneContext& ctx);
bool rewrite_expr_tree(std::unique_ptr<Expr>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out,
                       bool apply_current_expr_rewrite = true);

bool rewrite_param_decl_in_place(ParamDecl* param,
                                 ASTCloneContext& ctx,
                                 std::string* error_out) {
    if (!param) {
        return true;
    }
    param->type = rewrite_type(param->type, ctx);
    param->original_type =
        rewrite_type(QualType(param->original_type), ctx).get_shared();
    param->sym = remap_symbol(param->sym, ctx);
    if (param->sym) {
        param->sym->type = rewrite_type(param->sym->type, ctx);
    }
    if (const Expr* default_arg = get_param_decl_default_argument(param)) {
        auto cloned_default = clone_expr_with_substitution(
            default_arg,
            ctx,
            error_out);
        if (!cloned_default) {
            return false;
        }
        set_param_decl_default_argument(param, std::move(cloned_default));
    }
    return true;
}

bool rewrite_constraint_requirements_in_place(
    std::vector<ConstraintRequirement>& requirements,
    ASTCloneContext& ctx,
    std::string* error_out) {
    for (auto& requirement : requirements) {
        if (requirement.expr &&
            !rewrite_expr_tree(requirement.expr, ctx, error_out)) {
            return false;
        }
        requirement.type_requirement =
            rewrite_type(requirement.type_requirement, ctx);
        if (requirement.return_type_constraint) {
            requirement.return_type_constraint->template_arguments =
                rewrite_template_arguments(
                    requirement.return_type_constraint->template_arguments,
                    ctx,
                    error_out);
        }
    }
    return true;
}

std::shared_ptr<Symbol> remap_symbol(const std::shared_ptr<Symbol>& sym,
                                     ASTCloneContext& ctx) {
    if (!sym) {
        return nullptr;
    }
    auto it = ctx.symbol_remap.find(sym.get());
    if (it != ctx.symbol_remap.end()) {
        return it->second;
    }
    if (ctx.rewrite_symbol) {
        return ctx.rewrite_symbol(sym);
    }
    return sym;
}

void register_symbol(const std::shared_ptr<Symbol>& sym, ASTCloneContext& ctx) {
    if (sym && ctx.register_symbol) {
        ctx.register_symbol(sym);
    }
}

std::shared_ptr<Scope> clone_scope(const std::shared_ptr<Scope>& scope,
                                   ASTCloneContext& ctx) {
    if (!scope) {
        return nullptr;
    }
    auto it = ctx.scope_remap.find(scope.get());
    if (it != ctx.scope_remap.end()) {
        return it->second;
    }

    auto cloned = std::make_shared<Scope>();
    ctx.scope_remap.emplace(scope.get(), cloned);
    cloned->flags = scope->flags;
    cloned->cxx_namespace_path = scope->cxx_namespace_path;
    cloned->parent = clone_scope(scope->parent, ctx);
    return cloned;
}

bool rewrite_expr_tree(std::unique_ptr<Expr>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out,
                       bool apply_current_expr_rewrite);
bool rewrite_stmt_tree_in_place_impl(std::unique_ptr<Stmt>& stmt,
                                     ASTCloneContext& ctx,
                                     std::string* error_out);
bool rewrite_decl_tree_in_place_impl(std::unique_ptr<Decl>& decl,
                                     ASTCloneContext& ctx,
                                     std::string* error_out);
RecordSemanticState clone_record_semantic_state_for_object_decl(
    const ObjectDecl* source,
    const ObjectDecl* destination,
    const ObjectType& destination_type,
    const std::unordered_map<const FieldDecl*, const FieldDecl*>& field_remap,
    ASTCloneContext& ctx);

template <typename ExprT>
bool rewrite_expr_tree(std::unique_ptr<ExprT>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out) {
    static_assert(std::is_base_of_v<Expr, ExprT>);
    if (!expr) {
        return true;
    }
    std::unique_ptr<Expr> erased(expr.release());
    bool ok = rewrite_expr_tree(erased, ctx, error_out);
    if (!ok) {
        return false;
    }
    expr.reset(static_cast<ExprT*>(erased.release()));
    return true;
}

template <typename ExprPtrVec>
bool rewrite_expr_vector(ExprPtrVec& exprs,
                         ASTCloneContext& ctx,
                         std::string* error_out) {
    ExprPtrVec rewritten_exprs;
    rewritten_exprs.reserve(exprs.size());
    for (auto& expr : exprs) {
        if (!expr) {
            rewritten_exprs.push_back(nullptr);
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(expr.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            std::vector<std::unique_ptr<Expr>> expanded_exprs;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_exprs,
                    error_out)) {
                return false;
            }
            for (auto& expanded_expr : expanded_exprs) {
                rewritten_exprs.push_back(std::move(expanded_expr));
            }
            continue;
        }
        if (!rewrite_expr_tree(expr, ctx, error_out)) {
            return false;
        }
        rewritten_exprs.push_back(std::move(expr));
    }
    exprs = std::move(rewritten_exprs);
    return true;
}

template <typename DeclPtrVec>
bool rewrite_decl_vector(DeclPtrVec& decls,
                         ASTCloneContext& ctx,
                         std::string* error_out) {
    for (auto& decl : decls) {
        if (decl && !rewrite_decl_tree_in_place_impl(decl, ctx, error_out)) {
            return false;
        }
    }
    return true;
}

bool rewrite_call_argument_vector(std::vector<std::unique_ptr<Expr>>& args,
                                  ASTCloneContext& ctx,
                                  std::string* error_out) {
    return rewrite_expr_vector(args, ctx, error_out);
}

bool rewrite_init_element_vector(std::vector<InitElement>& elements,
                                 ASTCloneContext& ctx,
                                 std::string* error_out) {
    std::vector<InitElement> rewritten_elements;
    rewritten_elements.reserve(elements.size());
    for (auto& element : elements) {
        for (auto& designator : element.designators) {
            if ((designator.index &&
                 !rewrite_expr_tree(designator.index, ctx, error_out)) ||
                (designator.range_end &&
                 !rewrite_expr_tree(designator.range_end, ctx, error_out))) {
                return false;
            }
        }
        if (!element.value) {
            rewritten_elements.push_back(std::move(element));
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(element.value.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            if (!element.designators.empty()) {
                return set_expr_error(
                    error_out,
                    "designated initializer pack expansion is not supported");
            }
            std::vector<std::unique_ptr<Expr>> expanded_values;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_values,
                    error_out)) {
                return false;
            }
            for (auto& expanded_value : expanded_values) {
                InitElement expanded_element;
                expanded_element.value = std::move(expanded_value);
                expanded_element.loc = element.loc;
                rewritten_elements.push_back(std::move(expanded_element));
            }
            continue;
        }
        if (!rewrite_expr_tree(element.value, ctx, error_out)) {
            return false;
        }
        rewritten_elements.push_back(std::move(element));
    }
    elements = std::move(rewritten_elements);
    return true;
}

bool rewrite_init_action_vector(std::vector<InitAction>& actions,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::vector<InitAction> rewritten_actions;
    rewritten_actions.reserve(actions.size());
    for (auto& action : actions) {
        if (!action.value) {
            rewritten_actions.push_back(std::move(action));
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(action.value.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            if (action.paths.size() != 1 || action.paths.front().empty()) {
                return set_expr_error(
                    error_out,
                    "processed initializer pack expansion is only supported for single target paths");
            }
            std::vector<std::unique_ptr<Expr>> expanded_values;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_values,
                    error_out)) {
                return false;
            }
            const auto base_path = action.paths.front();
            const size_t start_index = base_path.back();
            for (size_t idx = 0; idx < expanded_values.size(); ++idx) {
                InitAction expanded_action;
                auto path = base_path;
                path.back() = start_index + idx;
                expanded_action.paths.push_back(std::move(path));
                expanded_action.value = std::shared_ptr<Expr>(
                    expanded_values[idx].release());
                expanded_action.loc = action.loc;
                rewritten_actions.push_back(std::move(expanded_action));
            }
            continue;
        }

        auto rewritten_value = clone_expr_with_substitution(
            action.value.get(),
            ctx,
            error_out);
        if (!rewritten_value) {
            return false;
        }
        action.value = std::shared_ptr<Expr>(rewritten_value.release());
        rewritten_actions.push_back(std::move(action));
    }
    actions = std::move(rewritten_actions);
    return true;
}

bool rewrite_init_mapping_map(std::map<size_t, std::shared_ptr<Expr>>& mappings,
                              ASTCloneContext& ctx,
                              std::string* error_out) {
    std::map<size_t, std::shared_ptr<Expr>> rewritten_mappings;
    for (auto& [index, mapped_expr] : mappings) {
        if (!mapped_expr) {
            rewritten_mappings[index] = nullptr;
            continue;
        }
        if (auto* pack = dyn_cast<PackExpansionExpr>(mapped_expr.get())) {
            if (!ctx.expand_pack_expansion) {
                return set_expr_error(
                    error_out,
                    "pack expansion requires template specialization context");
            }
            std::vector<std::unique_ptr<Expr>> expanded_values;
            if (!ctx.expand_pack_expansion(
                    pack->pattern.get(),
                    expanded_values,
                    error_out)) {
                return false;
            }
            for (size_t idx = 0; idx < expanded_values.size(); ++idx) {
                rewritten_mappings[index + idx] =
                    std::shared_ptr<Expr>(expanded_values[idx].release());
            }
            continue;
        }

        auto rewritten_mapping = clone_expr_with_substitution(
            mapped_expr.get(),
            ctx,
            error_out);
        if (!rewritten_mapping) {
            return false;
        }
        rewritten_mappings[index] =
            std::shared_ptr<Expr>(rewritten_mapping.release());
    }
    mappings = std::move(rewritten_mappings);
    return true;
}

bool rewrite_expr_tree(std::unique_ptr<Expr>& expr,
                       ASTCloneContext& ctx,
                       std::string* error_out,
                       bool apply_current_expr_rewrite) {
    if (!expr) {
        return true;
    }
    if (ctx.rewrite_var_ref) {
        if (auto* var_ref = dyn_cast<VarRef>(expr.get())) {
            auto replacement = ctx.rewrite_var_ref(var_ref, error_out);
            if (!replacement && error_out && !error_out->empty()) {
                return false;
            }
            if (replacement) {
                expr = std::move(replacement);
            }
        }
    }

    bool ok = [&]() -> bool {
    switch (expr->get_kind()) {
        case StmtKind::IntegerLiteral: {
            auto* literal = static_cast<IntegerLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::FloatingLiteral: {
            auto* literal = static_cast<FloatingLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::CharacterLiteral: {
            auto* literal = static_cast<CharacterLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::StringLiteral: {
            auto* literal = static_cast<StringLiteral*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            return true;
        }
        case StmtKind::PredefinedExpr: {
            auto* predefined = static_cast<PredefinedExpr*>(expr.get());
            predefined->ctype = rewrite_type(predefined->ctype, ctx);
            return true;
        }
        case StmtKind::CppThisExpr: {
            auto* this_expr = static_cast<CppThisExpr*>(expr.get());
            this_expr->this_type = rewrite_type(this_expr->this_type, ctx);
            return true;
        }
        case StmtKind::VarRef:
        case StmtKind::QualifiedVarRef: {
            auto* var_ref = static_cast<VarRef*>(expr.get());
            var_ref->symref = remap_symbol(var_ref->symref, ctx);
            if (auto* qualified_info = var_ref->get_cpp_qualified_info()) {
                qualified_info->qualifier_type =
                    rewrite_type(qualified_info->qualifier_type, ctx);
            }
            return true;
        }
        case StmtKind::UnresolvedLookupExpr: {
            auto* lookup = static_cast<UnresolvedLookupExpr*>(expr.get());
            lookup->qualifier.qualifier_type =
                rewrite_type(lookup->qualifier.qualifier_type, ctx);
            if (!rewrite_optional_template_arguments(
                    lookup->explicit_template_arguments,
                    ctx,
                    error_out)) {
                return false;
            }
            lookup->ctype = rewrite_type(lookup->ctype, ctx);
            return true;
        }
        case StmtKind::LabelAddressExpr: {
            auto* label = static_cast<LabelAddressExpr*>(expr.get());
            label->ctype = rewrite_type(label->ctype, ctx);
            return true;
        }
        case StmtKind::FuncCall: {
            auto* call = static_cast<FuncCall*>(expr.get());
            if (call->func && !rewrite_expr_tree(call->func, ctx, error_out)) {
                return false;
            }
            if (!rewrite_call_argument_vector(call->args, ctx, error_out)) {
                return false;
            }
            call->ctype = rewrite_type(call->ctype, ctx);
            return true;
        }
        case StmtKind::DependentCallExpr: {
            auto* call = static_cast<DependentCallExpr*>(expr.get());
            if (call->callee &&
                !rewrite_expr_tree(
                    call->callee,
                    ctx,
                    error_out,
                    /*apply_current_expr_rewrite=*/false)) {
                return false;
            }
            if (!rewrite_call_argument_vector(call->args, ctx, error_out)) {
                return false;
            }
            call->ctype = rewrite_type(call->ctype, ctx);
            call->known_function_type =
                rewrite_type(call->known_function_type, ctx);
            return true;
        }
        case StmtKind::DependentArraySubscriptExpr: {
            auto* subscript =
                static_cast<DependentArraySubscriptExpr*>(expr.get());
            if (subscript->array &&
                !rewrite_expr_tree(subscript->array, ctx, error_out)) {
                return false;
            }
            if (subscript->index &&
                !rewrite_expr_tree(subscript->index, ctx, error_out)) {
                return false;
            }
            subscript->ctype = rewrite_type(subscript->ctype, ctx);
            return true;
        }
        case StmtKind::DependentUnaryExpr: {
            auto* unary = static_cast<DependentUnaryExpr*>(expr.get());
            if (unary->operand &&
                !rewrite_expr_tree(unary->operand, ctx, error_out)) {
                return false;
            }
            unary->ctype = rewrite_type(unary->ctype, ctx);
            return true;
        }
        case StmtKind::DependentBinaryExpr: {
            auto* binary = static_cast<DependentBinaryExpr*>(expr.get());
            if (binary->left &&
                !rewrite_expr_tree(binary->left, ctx, error_out)) {
                return false;
            }
            if (binary->right &&
                !rewrite_expr_tree(binary->right, ctx, error_out)) {
                return false;
            }
            binary->ctype = rewrite_type(binary->ctype, ctx);
            return true;
        }
        case StmtKind::DependentMemberPointerAccessExpr: {
            auto* access =
                static_cast<DependentMemberPointerAccessExpr*>(expr.get());
            if (access->base &&
                !rewrite_expr_tree(access->base, ctx, error_out)) {
                return false;
            }
            if (access->member_pointer &&
                !rewrite_expr_tree(access->member_pointer, ctx, error_out)) {
                return false;
            }
            access->ctype = rewrite_type(access->ctype, ctx);
            return true;
        }
        case StmtKind::PackExpansionExpr: {
            auto* pack = static_cast<PackExpansionExpr*>(expr.get());
            if (pack->pattern &&
                !rewrite_expr_tree(pack->pattern, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::FoldExpr: {
            auto* fold = static_cast<FoldExpr*>(expr.get());
            if ((fold->pattern &&
                 !rewrite_expr_tree(fold->pattern, ctx, error_out)) ||
                (fold->init &&
                 !rewrite_expr_tree(fold->init, ctx, error_out))) {
                return false;
            }
            fold->result_type = rewrite_type(fold->result_type, ctx);
            return true;
        }
        case StmtKind::CppMemberCallExpr: {
            auto* member_call = static_cast<CppMemberCallExpr*>(expr.get());
            if (member_call->lowered_call &&
                !rewrite_expr_tree(member_call->lowered_call, ctx, error_out)) {
                return false;
            }
            member_call->ctype = rewrite_type(member_call->ctype, ctx);
            return true;
        }
        case StmtKind::CppConstructExpr: {
            auto* construct = static_cast<CppConstructExpr*>(expr.get());
            if (!rewrite_expr_vector(construct->args, ctx, error_out)) {
                return false;
            }
            construct->ctor_sym = remap_symbol(construct->ctor_sym, ctx);
            construct->ctype = rewrite_type(construct->ctype, ctx);
            return true;
        }
        case StmtKind::CppValueInitExpr: {
            auto* value_init = static_cast<CppValueInitExpr*>(expr.get());
            value_init->ctype = rewrite_type(value_init->ctype, ctx);
            return true;
        }
        case StmtKind::CppFunctionStyleCastExpr: {
            auto* cast = static_cast<CppFunctionStyleCastExpr*>(expr.get());
            if (!rewrite_expr_vector(cast->args, ctx, error_out)) {
                return false;
            }
            cast->target_type = rewrite_type(cast->target_type, ctx);
            return true;
        }
        case StmtKind::CppImmediateInvocationExpr: {
            auto* immediate =
                static_cast<CppImmediateInvocationExpr*>(expr.get());
            if (immediate->invocation &&
                !rewrite_expr_tree(immediate->invocation, ctx, error_out)) {
                return false;
            }
            immediate->ctype = rewrite_type(immediate->ctype, ctx);
            return true;
        }
        case StmtKind::CppThrowExpr: {
            auto* throw_expr = static_cast<CppThrowExpr*>(expr.get());
            if (throw_expr->thrown_expr &&
                !rewrite_expr_tree(throw_expr->thrown_expr, ctx, error_out)) {
                return false;
            }
            throw_expr->ctype = rewrite_type(throw_expr->ctype, ctx);
            return true;
        }
        case StmtKind::CppNewExpr: {
            auto* new_expr = static_cast<CppNewExpr*>(expr.get());
            if (!rewrite_expr_vector(new_expr->placement_args, ctx, error_out)) {
                return false;
            }
            if (new_expr->initializer &&
                !rewrite_expr_tree(new_expr->initializer, ctx, error_out)) {
                return false;
            }
            if (!rewrite_expr_vector(new_expr->constructor_args, ctx, error_out)) {
                return false;
            }
            new_expr->allocated_type = rewrite_type(new_expr->allocated_type, ctx);
            new_expr->result_type = rewrite_type(new_expr->result_type, ctx);
            new_expr->allocator_sym = remap_symbol(new_expr->allocator_sym, ctx);
            new_expr->deallocator_sym = remap_symbol(new_expr->deallocator_sym, ctx);
            new_expr->ctor_sym = remap_symbol(new_expr->ctor_sym, ctx);
            return true;
        }
        case StmtKind::CppDeleteExpr: {
            auto* delete_expr = static_cast<CppDeleteExpr*>(expr.get());
            if (delete_expr->operand &&
                !rewrite_expr_tree(delete_expr->operand, ctx, error_out)) {
                return false;
            }
            delete_expr->ctype = rewrite_type(delete_expr->ctype, ctx);
            delete_expr->destroyed_type =
                rewrite_type(delete_expr->destroyed_type, ctx);
            delete_expr->deallocator_sym =
                remap_symbol(delete_expr->deallocator_sym, ctx);
            delete_expr->destructor_sym =
                remap_symbol(delete_expr->destructor_sym, ctx);
            return true;
        }
        case StmtKind::CppPseudoDestructorExpr: {
            auto* pseudo_dtor =
                static_cast<CppPseudoDestructorExpr*>(expr.get());
            if (pseudo_dtor->base &&
                !rewrite_expr_tree(pseudo_dtor->base, ctx, error_out)) {
                return false;
            }
            pseudo_dtor->destroyed_type =
                rewrite_type(pseudo_dtor->destroyed_type, ctx);
            pseudo_dtor->ctype = rewrite_type(pseudo_dtor->ctype, ctx);
            pseudo_dtor->destructor_sym =
                remap_symbol(pseudo_dtor->destructor_sym, ctx);
            return true;
        }
        case StmtKind::BlockByrefAccessExpr: {
            auto* byref_expr = static_cast<BlockByrefAccessExpr*>(expr.get());
            if (byref_expr->cell_expr &&
                !rewrite_expr_tree(byref_expr->cell_expr, ctx, error_out)) {
                return false;
            }
            byref_expr->symbol = remap_symbol(byref_expr->symbol, ctx);
            byref_expr->ctype = rewrite_type(byref_expr->ctype, ctx);
            return true;
        }
        case StmtKind::BlockExpr: {
            auto* block = static_cast<BlockExpr*>(expr.get());
            block->block_type = rewrite_type(block->block_type, ctx);
            block->explicit_return_type =
                rewrite_type(block->explicit_return_type, ctx);
            if (!rewrite_decl_vector(
                    block->parameters,
                    ctx,
                    error_out)) {
                return false;
            }
            if (block->body) {
                std::unique_ptr<Stmt> body_stmt(block->body.release());
                if (!rewrite_stmt_tree_in_place_impl(
                        body_stmt,
                        ctx,
                        error_out)) {
                    return false;
                }
                block->body.reset(
                    static_cast<CompoundStmt*>(body_stmt.release()));
            }
            if (ctx.finalize_block_expr &&
                !ctx.finalize_block_expr(*block, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::CppLambdaExpr: {
            auto* lambda = static_cast<CppLambdaExpr*>(expr.get());
            lambda->written_call_operator_type =
                rewrite_type(lambda->written_call_operator_type, ctx);
            lambda->explicit_return_type =
                rewrite_type(lambda->explicit_return_type, ctx);
            lambda->semantic_info.lexical_this_context.this_type =
                rewrite_type(
                    lambda->semantic_info.lexical_this_context.this_type,
                    ctx);
            if (lambda->template_requires_clause &&
                !rewrite_expr_tree(
                    lambda->template_requires_clause,
                    ctx,
                    error_out)) {
                return false;
            }
            if (lambda->trailing_requires_clause &&
                !rewrite_expr_tree(
                    lambda->trailing_requires_clause,
                    ctx,
                    error_out)) {
                return false;
            }
            for (auto& capture : lambda->closure_info.captures) {
                capture.symbol = remap_symbol(capture.symbol, ctx);
                if (!capture.initializer) {
                    continue;
                }
                auto rewritten_initializer = clone_expr_with_substitution(
                    capture.initializer.get(),
                    ctx,
                    error_out);
                if (!rewritten_initializer) {
                    return false;
                }
                capture.initializer = std::shared_ptr<Expr>(
                    rewritten_initializer.release());
            }
            if (!rewrite_decl_vector(
                    lambda->parameters,
                    ctx,
                    error_out)) {
                return false;
            }
            if (lambda->body) {
                std::unique_ptr<Stmt> body_stmt(lambda->body.release());
                if (!rewrite_stmt_tree_in_place_impl(
                        body_stmt,
                        ctx,
                        error_out)) {
                    return false;
                }
                lambda->body.reset(
                    static_cast<CompoundStmt*>(body_stmt.release()));
            }
            if (ctx.finalize_lambda_expr &&
                !ctx.finalize_lambda_expr(*lambda, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::CppTypeIdExpr: {
            auto* typeid_expr = static_cast<CppTypeIdExpr*>(expr.get());
            if (typeid_expr->is_type_operand) {
                typeid_expr->type_operand =
                    rewrite_type(typeid_expr->type_operand, ctx);
            } else if (typeid_expr->expr_operand &&
                       !rewrite_expr_tree(typeid_expr->expr_operand, ctx, error_out)) {
                return false;
            }
            typeid_expr->ctype = rewrite_type(typeid_expr->ctype, ctx);
            return true;
        }
        case StmtKind::CppDynamicCastExpr: {
            auto* cast_expr = static_cast<CppDynamicCastExpr*>(expr.get());
            if (cast_expr->expr &&
                !rewrite_expr_tree(cast_expr->expr, ctx, error_out)) {
                return false;
            }
            cast_expr->target_type = rewrite_type(cast_expr->target_type, ctx);
            return true;
        }
        case StmtKind::ParenExpr: {
            auto* paren = static_cast<ParenExpr*>(expr.get());
            return !paren->subexpr ||
                   rewrite_expr_tree(paren->subexpr, ctx, error_out);
        }
        case StmtKind::CondExpr: {
            auto* cond = static_cast<CondExpr*>(expr.get());
            if (cond->condition &&
                !rewrite_expr_tree(cond->condition, ctx, error_out)) {
                return false;
            }
            if (cond->true_expr &&
                !rewrite_expr_tree(cond->true_expr, ctx, error_out)) {
                return false;
            }
            if (cond->false_expr &&
                !rewrite_expr_tree(cond->false_expr, ctx, error_out)) {
                return false;
            }
            cond->type = rewrite_type(cond->type, ctx);
            return true;
        }
        case StmtKind::UnaryOperation: {
            auto* unary = static_cast<UnaryOperation*>(expr.get());
            if (unary->exp && !rewrite_expr_tree(unary->exp, ctx, error_out)) {
                return false;
            }
            unary->ctype = rewrite_type(unary->ctype, ctx);
            return true;
        }
        case StmtKind::BinaryOperation: {
            auto* binary = static_cast<BinaryOperation*>(expr.get());
            if (binary->left &&
                !rewrite_expr_tree(binary->left, ctx, error_out)) {
                return false;
            }
            if (binary->right &&
                !rewrite_expr_tree(binary->right, ctx, error_out)) {
                return false;
            }
            binary->ctype = rewrite_type(binary->ctype, ctx);
            return true;
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            auto* compare =
                static_cast<CppBuiltinThreeWayCompareExpr*>(expr.get());
            if (compare->left &&
                !rewrite_expr_tree(compare->left, ctx, error_out)) {
                return false;
            }
            if (compare->right &&
                !rewrite_expr_tree(compare->right, ctx, error_out)) {
                return false;
            }
            compare->ctype = rewrite_type(compare->ctype, ctx);
            return true;
        }
        case StmtKind::CompoundAssignOperation: {
            auto* compound = static_cast<CompoundAssignOperation*>(expr.get());
            if (compound->left &&
                !rewrite_expr_tree(compound->left, ctx, error_out)) {
                return false;
            }
            if (compound->right &&
                !rewrite_expr_tree(compound->right, ctx, error_out)) {
                return false;
            }
            compound->ctype = rewrite_type(compound->ctype, ctx);
            return true;
        }
        case StmtKind::ImplicitCast: {
            auto* cast = static_cast<ImplicitCast*>(expr.get());
            if (cast->expr && !rewrite_expr_tree(cast->expr, ctx, error_out)) {
                return false;
            }
            cast->ctype = rewrite_type(cast->ctype, ctx);
            return true;
        }
        case StmtKind::ExplicitCast: {
            auto* cast = static_cast<ExplicitCast*>(expr.get());
            if (cast->expr && !rewrite_expr_tree(cast->expr, ctx, error_out)) {
                return false;
            }
            cast->ctype = rewrite_type(cast->ctype, ctx);
            return true;
        }
        case StmtKind::ArraySubscriptExpr: {
            auto* subscript = static_cast<ArraySubscriptExpr*>(expr.get());
            if (subscript->array &&
                !rewrite_expr_tree(subscript->array, ctx, error_out)) {
                return false;
            }
            if (subscript->index &&
                !rewrite_expr_tree(subscript->index, ctx, error_out)) {
                return false;
            }
            subscript->ctype = rewrite_type(subscript->ctype, ctx);
            return true;
        }
        case StmtKind::MemberExpr: {
            auto* member = static_cast<MemberExpr*>(expr.get());
            if (member->base && !rewrite_expr_tree(member->base, ctx, error_out)) {
                return false;
            }
            member->member_type = rewrite_type(member->member_type, ctx);
            member->declared_member_type =
                rewrite_type(member->declared_member_type, ctx);
            if (ctx.rewrite_member_expr &&
                !ctx.rewrite_member_expr(member, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::UnresolvedMemberExpr: {
            auto* member = static_cast<UnresolvedMemberExpr*>(expr.get());
            if (member->base &&
                !rewrite_expr_tree(member->base, ctx, error_out)) {
                return false;
            }
            member->member_type = rewrite_type(member->member_type, ctx);
            member->declared_member_type =
                rewrite_type(member->declared_member_type, ctx);
            if (!rewrite_optional_template_arguments(
                    member->explicit_template_arguments,
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::MemberPointerLiteralExpr: {
            auto* literal = static_cast<MemberPointerLiteralExpr*>(expr.get());
            literal->ctype = rewrite_type(literal->ctype, ctx);
            literal->method_symbol = remap_symbol(literal->method_symbol, ctx);
            return true;
        }
        case StmtKind::MemberPointerAccessExpr: {
            auto* access = static_cast<MemberPointerAccessExpr*>(expr.get());
            if (access->base && !rewrite_expr_tree(access->base, ctx, error_out)) {
                return false;
            }
            if (access->member_pointer &&
                !rewrite_expr_tree(access->member_pointer, ctx, error_out)) {
                return false;
            }
            access->result_type = rewrite_type(access->result_type, ctx);
            return true;
        }
        case StmtKind::InitListExpr: {
            auto* init_list = static_cast<InitListExpr*>(expr.get());
            if (!rewrite_init_element_vector(
                    init_list->elements,
                    ctx,
                    error_out)) {
                return false;
            }
            if (!rewrite_init_action_vector(
                    init_list->actions,
                    ctx,
                    error_out)) {
                return false;
            }
            if (!rewrite_init_mapping_map(
                    init_list->mappings,
                    ctx,
                    error_out)) {
                return false;
            }
            init_list->type = rewrite_type(init_list->type, ctx);
            return true;
        }
        case StmtKind::CompoundLiteralExpr: {
            auto* compound_literal = static_cast<CompoundLiteralExpr*>(expr.get());
            if (compound_literal->init &&
                !rewrite_expr_tree(compound_literal->init, ctx, error_out)) {
                return false;
            }
            compound_literal->type = rewrite_type(compound_literal->type, ctx);
            return true;
        }
        case StmtKind::SizeOfExpr: {
            auto* sizeof_expr = static_cast<SizeOfExpr*>(expr.get());
            if (sizeof_expr->expr_operand &&
                !rewrite_expr_tree(sizeof_expr->expr_operand, ctx, error_out)) {
                return false;
            }
            sizeof_expr->type_operand =
                rewrite_type(sizeof_expr->type_operand, ctx);
            sizeof_expr->result_type =
                rewrite_type(sizeof_expr->result_type, ctx);
            return true;
        }
        case StmtKind::SizeOfPackExpr: {
            auto* sizeof_pack = static_cast<SizeOfPackExpr*>(expr.get());
            if (ctx.lookup_pack_size) {
                auto pack_size = ctx.lookup_pack_size(sizeof_pack, error_out);
                if (error_out && !error_out->empty()) {
                    return false;
                }
                if (pack_size.has_value()) {
                    expr = make_pack_size_integer_literal(
                        *pack_size,
                        ctx.ast_ctx,
                        sizeof_pack->location);
                    return rewrite_expr_tree(expr, ctx, error_out);
                }
            }
            sizeof_pack->result_type =
                rewrite_type(sizeof_pack->result_type, ctx);
            return true;
        }
        case StmtKind::StmtExpr:
            return set_expr_error(
                error_out,
                "statement-expression cloning is not supported");
        case StmtKind::VaArgExpr: {
            auto* va_arg = static_cast<VaArgExpr*>(expr.get());
            if (va_arg->va_list_expr &&
                !rewrite_expr_tree(va_arg->va_list_expr, ctx, error_out)) {
                return false;
            }
            va_arg->arg_type = rewrite_type(va_arg->arg_type, ctx);
            return true;
        }
        case StmtKind::VaStartExpr: {
            auto* va_start = static_cast<VaStartExpr*>(expr.get());
            if (va_start->va_list_expr &&
                !rewrite_expr_tree(va_start->va_list_expr, ctx, error_out)) {
                return false;
            }
            if (va_start->last_param &&
                !rewrite_expr_tree(va_start->last_param, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::VaEndExpr: {
            auto* va_end = static_cast<VaEndExpr*>(expr.get());
            return !va_end->va_list_expr ||
                rewrite_expr_tree(va_end->va_list_expr, ctx, error_out);
        }
        case StmtKind::VaCopyExpr: {
            auto* va_copy = static_cast<VaCopyExpr*>(expr.get());
            if (va_copy->dest &&
                !rewrite_expr_tree(va_copy->dest, ctx, error_out)) {
                return false;
            }
            if (va_copy->src &&
                !rewrite_expr_tree(va_copy->src, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case StmtKind::AlignOfExpr: {
            auto* alignof_expr = static_cast<AlignOfExpr*>(expr.get());
            if (alignof_expr->expr_operand &&
                !rewrite_expr_tree(alignof_expr->expr_operand, ctx, error_out)) {
                return false;
            }
            alignof_expr->type_operand =
                rewrite_type(alignof_expr->type_operand, ctx);
            alignof_expr->result_type =
                rewrite_type(alignof_expr->result_type, ctx);
            return true;
        }
        case StmtKind::CppNoexceptExpr: {
            auto* noexcept_expr = static_cast<CppNoexceptExpr*>(expr.get());
            if (noexcept_expr->operand &&
                !rewrite_expr_tree(noexcept_expr->operand, ctx, error_out)) {
                return false;
            }
            noexcept_expr->ctype = rewrite_type(noexcept_expr->ctype, ctx);
            return true;
        }
        case StmtKind::GenericExpr: {
            auto* generic_expr = static_cast<GenericExpr*>(expr.get());
            if (generic_expr->controlling_expr &&
                !rewrite_expr_tree(generic_expr->controlling_expr, ctx, error_out)) {
                return false;
            }
            for (auto& assoc : generic_expr->associations) {
                assoc.type = rewrite_type(assoc.type, ctx);
                if (assoc.expr &&
                    !rewrite_expr_tree(assoc.expr, ctx, error_out)) {
                    return false;
                }
            }
            generic_expr->result_type =
                rewrite_type(generic_expr->result_type, ctx);
            return true;
        }
        case StmtKind::OffsetOfExpr: {
            auto* offsetof_expr = static_cast<OffsetOfExpr*>(expr.get());
            offsetof_expr->type_operand =
                rewrite_type(offsetof_expr->type_operand, ctx);
            for (auto& component : offsetof_expr->designator_path) {
                if (component.array_index_expr &&
                    !rewrite_expr_tree(
                        component.array_index_expr,
                        ctx,
                        error_out)) {
                    return false;
                }
            }
            offsetof_expr->result_type =
                rewrite_type(offsetof_expr->result_type, ctx);
            return true;
        }
        case StmtKind::BuiltinCallExpr: {
            auto* builtin = static_cast<BuiltinCallExpr*>(expr.get());
            if (!rewrite_expr_vector(builtin->args, ctx, error_out)) {
                return false;
            }
            bool has_type_pack_expansion = false;
            for (const auto& type_arg : builtin->type_args) {
                auto parameter_type = type_arg.as_shared<TemplateTypeParmType>();
                if (parameter_type && parameter_type->is_parameter_pack) {
                    has_type_pack_expansion = true;
                    break;
                }
            }
            if (has_type_pack_expansion && ctx.rewrite_template_arguments) {
                std::vector<TemplateArgument> type_arguments;
                type_arguments.reserve(builtin->type_args.size());
                for (const auto& type_arg : builtin->type_args) {
                    TemplateArgument argument(type_arg);
                    auto parameter_type = type_arg.as_shared<TemplateTypeParmType>();
                    if (parameter_type && parameter_type->is_parameter_pack) {
                        argument = argument.as_pack_expansion();
                    }
                    type_arguments.push_back(std::move(argument));
                }
                auto rewritten_arguments =
                    rewrite_template_arguments(type_arguments, ctx, error_out);
                std::vector<QualType> rewritten_types;
                rewritten_types.reserve(rewritten_arguments.size());
                for (const auto& argument : rewritten_arguments) {
                    if (argument.kind != TemplateArgumentKind::Type) {
                        return set_expr_error(
                            error_out,
                            "builtin type trait pack expansion produced a non-type argument");
                    }
                    rewritten_types.push_back(argument.type);
                }
                builtin->type_args = std::move(rewritten_types);
            } else {
                for (auto& type_arg : builtin->type_args) {
                    type_arg = rewrite_type(type_arg, ctx);
                }
            }
            builtin->result_type = rewrite_type(builtin->result_type, ctx);
            return true;
        }
        case StmtKind::ConceptSpecializationExpr: {
            auto* concept_expr =
                static_cast<ConceptSpecializationExpr*>(expr.get());
            concept_expr->arguments = rewrite_template_arguments(
                concept_expr->arguments,
                ctx,
                error_out);
            concept_expr->result_type =
                rewrite_type(concept_expr->result_type, ctx);
            concept_expr->satisfaction.reset();
            return true;
        }
        case StmtKind::RequiresExpr: {
            auto* requires_expr = static_cast<RequiresExpr*>(expr.get());
            for (auto& parameter : requires_expr->parameters) {
                if (!rewrite_param_decl_in_place(
                        parameter.get(),
                        ctx,
                        error_out)) {
                    return false;
                }
            }
            if (!rewrite_constraint_requirements_in_place(
                    requires_expr->requirements,
                    ctx,
                    error_out)) {
                return false;
            }
            requires_expr->result_type =
                rewrite_type(requires_expr->result_type, ctx);
            requires_expr->satisfaction.reset();
            return true;
        }
        case StmtKind::ErrorExpr:
            return true;
        default:
            return set_expr_error(
                error_out,
                "unsupported expression substitution kind " +
                    std::to_string(static_cast<int>(expr->get_kind())));
    }
    }();
    if (!ok) {
        return false;
    }
    if (apply_current_expr_rewrite &&
        ctx.rewrite_expr &&
        !ctx.rewrite_expr(expr, error_out)) {
        return false;
    }
    return true;
}

bool rewrite_decl_tree_in_place_impl(std::unique_ptr<Decl>& decl,
                                     ASTCloneContext& ctx,
                                     std::string* error_out) {
    if (!decl) {
        return true;
    }

    switch (decl->get_kind()) {
        case DeclKind::NopDecl:
        case DeclKind::CppUsingDeclarationDecl:
        case DeclKind::NamespaceDecl:
        case DeclKind::ErrorDecl:
            return true;
        case DeclKind::FieldDecl: {
            auto* field_decl = static_cast<FieldDecl*>(decl.get());
            field_decl->type = rewrite_type(field_decl->type, ctx);
            if (!rewrite_expr_tree(
                    field_decl->default_member_initializer,
                    ctx,
                    error_out)) {
                return false;
            }
            if (ctx.ast_ctx && ctx.ast_ctx->has_attrs(field_decl->node_id) &&
                !rewrite_attribute_list_in_place(
                    ctx.ast_ctx->get_attrs_mut(field_decl->node_id),
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::CppAccessSpecDecl:
            return true;
        case DeclKind::ObjectDecl: {
            auto* object_decl = static_cast<ObjectDecl*>(decl.get());
            auto record_type = object_decl->get_record_type();
            if (record_type) {
                ctx.record_type_remap.emplace(object_decl, QualType(record_type));
            }
            if (!rewrite_decl_vector(object_decl->fields, ctx, error_out)) {
                return false;
            }
            if (record_type) {
                std::unordered_map<const FieldDecl*, const FieldDecl*> field_remap;
                record_semantics_cache_set(
                    ctx.ast_ctx,
                    object_decl,
                    clone_record_semantic_state_for_object_decl(
                        object_decl,
                        object_decl,
                        *record_type,
                        field_remap,
                        ctx));
            }
            if (ctx.ast_ctx && ctx.ast_ctx->has_attrs(object_decl->node_id) &&
                !rewrite_attribute_list_in_place(
                    ctx.ast_ctx->get_attrs_mut(object_decl->node_id),
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::CppRecordDecl: {
            auto* record_decl = static_cast<CppRecordDecl*>(decl.get());
            for (auto& base : record_decl->bases) {
                base.type = rewrite_type(base.type, ctx);
            }
            if (!rewrite_decl_vector(record_decl->members, ctx, error_out)) {
                return false;
            }
            if (ctx.ast_ctx && ctx.ast_ctx->has_attrs(record_decl->node_id) &&
                !rewrite_attribute_list_in_place(
                    ctx.ast_ctx->get_attrs_mut(record_decl->node_id),
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::TypedefDecl: {
            auto* typedef_decl = static_cast<TypedefDecl*>(decl.get());
            typedef_decl->type = rewrite_type(typedef_decl->type, ctx);
            typedef_decl->sym = remap_symbol(typedef_decl->sym, ctx);
            if (typedef_decl->sym) {
                typedef_decl->sym->type = rewrite_type(typedef_decl->sym->type, ctx);
            }
            return true;
        }
        case DeclKind::VariableDecl: {
            auto* variable = static_cast<VariableDecl*>(decl.get());
            variable->type = rewrite_type(variable->type, ctx);
            variable->original_type = rewrite_type(variable->original_type, ctx);
            variable->sym = remap_symbol(variable->sym, ctx);
            if (variable->sym) {
                variable->sym->type = rewrite_type(variable->sym->type, ctx);
            }
            if (variable->init &&
                !rewrite_expr_tree(variable->init, ctx, error_out)) {
                return false;
            }
            return true;
        }
        case DeclKind::ParamDecl: {
            auto* param = static_cast<ParamDecl*>(decl.get());
            param->type = rewrite_type(param->type, ctx);
            param->sym = remap_symbol(param->sym, ctx);
            if (param->sym) {
                param->sym->type = rewrite_type(param->sym->type, ctx);
            }
            param->original_type =
                rewrite_type(QualType(param->original_type), ctx).get_shared();
            if (const Expr* default_arg = get_param_decl_default_argument(param)) {
                auto rewritten_default = clone_expr_with_substitution(
                    default_arg,
                    ctx,
                    error_out);
                if (!rewritten_default) {
                    return false;
                }
                set_param_decl_default_argument(
                    param,
                    std::move(rewritten_default));
            }
            return true;
        }
        case DeclKind::StaticAssertDecl: {
            auto* static_assert_decl = static_cast<StaticAssertDecl*>(decl.get());
            if (static_assert_decl->condition &&
                !rewrite_expr_tree(
                    static_assert_decl->condition,
                    ctx,
                    error_out)) {
                return false;
            }
            return true;
        }
        default:
            return set_expr_error(
                error_out,
                "unsupported declaration rewrite kind " +
                    std::to_string(static_cast<int>(decl->get_kind())));
    }
}

bool rewrite_stmt_tree_in_place_impl(std::unique_ptr<Stmt>& stmt,
                                     ASTCloneContext& ctx,
                                     std::string* error_out) {
    if (!stmt) {
        return true;
    }

    if (Expr::classof(stmt.get())) {
        std::unique_ptr<Expr> expr(static_cast<Expr*>(stmt.release()));
        if (!rewrite_expr_tree(expr, ctx, error_out)) {
            return false;
        }
        stmt.reset(expr.release());
        return true;
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            auto* compound = static_cast<CompoundStmt*>(stmt.get());
            for (auto& child : compound->statements) {
                if (child &&
                    !rewrite_stmt_tree_in_place_impl(child, ctx, error_out)) {
                    return false;
                }
            }
            return true;
        }
        case StmtKind::Decl2Stmt: {
            auto* decl_stmt = static_cast<Decl2Stmt*>(stmt.get());
            return rewrite_decl_vector(decl_stmt->decls, ctx, error_out);
        }
        case StmtKind::ReturnStmt: {
            auto* ret = static_cast<ReturnStmt*>(stmt.get());
            return !ret->expression ||
                   rewrite_expr_tree(ret->expression, ctx, error_out);
        }
        case StmtKind::IfStmt: {
            auto* if_stmt = static_cast<IfStmt*>(stmt.get());
            if (if_stmt->init_stmt &&
                !rewrite_stmt_tree_in_place_impl(
                    if_stmt->init_stmt,
                    ctx,
                    error_out)) {
                return false;
            }
            if (if_stmt->condition.declaration &&
                !rewrite_stmt_tree_in_place_impl(
                    if_stmt->condition.declaration,
                    ctx,
                    error_out)) {
                return false;
            }
            if (if_stmt->condition.expression &&
                !rewrite_expr_tree(
                    if_stmt->condition.expression,
                    ctx,
                    error_out)) {
                return false;
            }
            if (if_stmt->statement_kind == IfStatementKind::Constexpr &&
                if_stmt->condition.expression) {
                ConstEvalResult eval = evaluate_with_consteval_compat(
                    if_stmt->condition.expression.get(),
                    ConstEvalMode::cpp_core_constant_expression());
                if (eval.status == ConstEvalStatus::Constant &&
                    eval.int_value.has_value()) {
                    if_stmt->constexpr_condition_value = *eval.int_value != 0;
                    auto& selected_stmt = *if_stmt->constexpr_condition_value
                        ? if_stmt->then_stmt
                        : if_stmt->else_stmt;
                    return !selected_stmt ||
                           rewrite_stmt_tree_in_place_impl(
                               selected_stmt,
                               ctx,
                               error_out);
                }
            }
            return (!if_stmt->then_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        if_stmt->then_stmt,
                        ctx,
                        error_out)) &&
                   (!if_stmt->else_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        if_stmt->else_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::CaseStmt: {
            auto* case_stmt = static_cast<CaseStmt*>(stmt.get());
            return (!case_stmt->const_expr ||
                    rewrite_expr_tree(case_stmt->const_expr, ctx, error_out)) &&
                   (!case_stmt->range_end ||
                    rewrite_expr_tree(case_stmt->range_end, ctx, error_out)) &&
                   (!case_stmt->stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        case_stmt->stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::DefaultStmt: {
            auto* default_stmt = static_cast<DefaultStmt*>(stmt.get());
            return !default_stmt->stmt ||
                   rewrite_stmt_tree_in_place_impl(
                       default_stmt->stmt,
                       ctx,
                       error_out);
        }
        case StmtKind::LabeledStmt: {
            auto* labeled = static_cast<LabeledStmt*>(stmt.get());
            return !labeled->stmt ||
                   rewrite_stmt_tree_in_place_impl(
                       labeled->stmt,
                       ctx,
                       error_out);
        }
        case StmtKind::GoToStmt:
        case StmtKind::ContinueStmt:
        case StmtKind::BreakStmt:
        case StmtKind::EmptyStmt:
        case StmtKind::ErrorStmt:
            return true;
        case StmtKind::ComputedGotoStmt: {
            auto* goto_stmt = static_cast<ComputedGotoStmt*>(stmt.get());
            return !goto_stmt->target ||
                   rewrite_expr_tree(goto_stmt->target, ctx, error_out);
        }
        case StmtKind::SwitchStmt: {
            auto* switch_stmt = static_cast<SwitchStmt*>(stmt.get());
            return (!switch_stmt->condition.declaration ||
                    rewrite_stmt_tree_in_place_impl(
                        switch_stmt->condition.declaration,
                        ctx,
                        error_out)) &&
                   (!switch_stmt->condition.expression ||
                    rewrite_expr_tree(
                        switch_stmt->condition.expression,
                        ctx,
                        error_out)) &&
                   (!switch_stmt->stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        switch_stmt->stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::WhileStmt: {
            auto* while_stmt = static_cast<WhileStmt*>(stmt.get());
            return (!while_stmt->condition.declaration ||
                    rewrite_stmt_tree_in_place_impl(
                        while_stmt->condition.declaration,
                        ctx,
                        error_out)) &&
                   (!while_stmt->condition.expression ||
                    rewrite_expr_tree(
                        while_stmt->condition.expression,
                        ctx,
                        error_out)) &&
                   (!while_stmt->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        while_stmt->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::DoWhileStmt: {
            auto* while_stmt = static_cast<DoWhileStmt*>(stmt.get());
            return (!while_stmt->condition ||
                    rewrite_expr_tree(while_stmt->condition, ctx, error_out)) &&
                   (!while_stmt->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        while_stmt->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::ForStmt: {
            auto* for_stmt = static_cast<ForStmt*>(stmt.get());
            return (!for_stmt->init ||
                    rewrite_stmt_tree_in_place_impl(
                        for_stmt->init,
                        ctx,
                        error_out)) &&
                   (!for_stmt->cond.declaration ||
                    rewrite_stmt_tree_in_place_impl(
                        for_stmt->cond.declaration,
                        ctx,
                        error_out)) &&
                   (!for_stmt->cond.expression ||
                    rewrite_expr_tree(for_stmt->cond.expression, ctx, error_out)) &&
                   (!for_stmt->action ||
                    rewrite_expr_tree(for_stmt->action, ctx, error_out)) &&
                   (!for_stmt->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        for_stmt->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::CppRangeForStmt: {
            auto* range_for = static_cast<CppRangeForStmt*>(stmt.get());
            return (!range_for->init_statement ||
                    rewrite_stmt_tree_in_place_impl(
                        range_for->init_statement,
                        ctx,
                        error_out)) &&
                   rewrite_decl_vector(
                       range_for->range_declaration_side_decls,
                       ctx,
                       error_out) &&
                   (!range_for->range_variable ||
                    rewrite_decl_tree_in_place_impl(
                        range_for->range_variable,
                        ctx,
                        error_out)) &&
                   (!range_for->begin_variable ||
                    rewrite_decl_tree_in_place_impl(
                        range_for->begin_variable,
                        ctx,
                        error_out)) &&
                   (!range_for->end_variable ||
                    rewrite_decl_tree_in_place_impl(
                        range_for->end_variable,
                        ctx,
                        error_out)) &&
                   (!range_for->loop_variable ||
                    rewrite_decl_tree_in_place_impl(
                        range_for->loop_variable,
                        ctx,
                        error_out)) &&
                   (!range_for->condition ||
                    rewrite_expr_tree(
                        range_for->condition,
                        ctx,
                        error_out)) &&
                   (!range_for->increment ||
                    rewrite_expr_tree(
                        range_for->increment,
                        ctx,
                        error_out)) &&
                   (!range_for->body_stmt ||
                    rewrite_stmt_tree_in_place_impl(
                        range_for->body_stmt,
                        ctx,
                        error_out));
        }
        case StmtKind::AsmStmt: {
            auto* asm_stmt = static_cast<AsmStmt*>(stmt.get());
            auto rewrite_operand_vec =
                [&](std::vector<AsmOperand>& operands) -> bool {
                    for (auto& operand : operands) {
                        if (operand.expr &&
                            !rewrite_expr_tree(operand.expr, ctx, error_out)) {
                            return false;
                        }
                    }
                    return true;
                };
            return rewrite_operand_vec(asm_stmt->output_operands) &&
                   rewrite_operand_vec(asm_stmt->input_operands);
        }
        case StmtKind::CppTryStmt: {
            auto* try_stmt = static_cast<CppTryStmt*>(stmt.get());
            if (try_stmt->try_block &&
                !rewrite_stmt_tree_in_place_impl(
                    try_stmt->try_block,
                    ctx,
                    error_out)) {
                return false;
            }
            for (auto& handler : try_stmt->handlers) {
                if (handler.handler &&
                    !rewrite_stmt_tree_in_place_impl(
                        handler.handler,
                        ctx,
                        error_out)) {
                    return false;
                }
            }
            return true;
        }
        default:
            return set_expr_error(
                error_out,
                "unsupported statement rewrite kind " +
                    std::to_string(static_cast<int>(stmt->get_kind())));
    }
}

std::unique_ptr<Decl> clone_decl_impl(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out);

std::unique_ptr<Stmt> clone_stmt_impl(const Stmt* stmt,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    if (!stmt) {
        return nullptr;
    }

    if (Expr::classof(stmt)) {
        auto cloned = clone_expr_with_substitution(
            static_cast<const Expr*>(stmt),
            ctx,
            error_out);
        return std::unique_ptr<Stmt>(cloned.release());
    }

    switch (stmt->get_kind()) {
        case StmtKind::CompoundStmt: {
            const auto* compound = static_cast<const CompoundStmt*>(stmt);
            std::vector<std::unique_ptr<Stmt>> cloned_statements;
            cloned_statements.reserve(compound->statements.size());
            for (const auto& child : compound->statements) {
                auto cloned_child = clone_stmt_impl(child.get(), ctx, error_out);
                if (child && !cloned_child) {
                    return nullptr;
                }
                cloned_statements.push_back(std::move(cloned_child));
            }
            auto result = std::make_unique<CompoundStmt>(
                std::move(cloned_statements),
                clone_scope(compound->scope, ctx),
                compound->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::Decl2Stmt: {
            const auto* decl_stmt = static_cast<const Decl2Stmt*>(stmt);
            std::vector<std::unique_ptr<Decl>> cloned_decls;
            cloned_decls.reserve(decl_stmt->decls.size());
            for (const auto& decl : decl_stmt->decls) {
                auto cloned_decl = clone_decl_impl(decl.get(), ctx, error_out);
                if (decl && !cloned_decl) {
                    return nullptr;
                }
                cloned_decls.push_back(std::move(cloned_decl));
            }
            auto result = std::make_unique<Decl2Stmt>(
                std::move(cloned_decls), decl_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ReturnStmt: {
            const auto* ret = static_cast<const ReturnStmt*>(stmt);
            auto expr =
                clone_expr_with_substitution(ret->expression.get(), ctx, error_out);
            if (ret->expression && !expr) {
                return nullptr;
            }
            auto result = std::make_unique<ReturnStmt>(
                std::move(expr), ret->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::IfStmt: {
            const auto* if_stmt = static_cast<const IfStmt*>(stmt);
            auto init_stmt = clone_stmt_impl(
                if_stmt->init_stmt.get(), ctx, error_out);
            auto condition_decl = clone_stmt_impl(
                if_stmt->condition.declaration.get(), ctx, error_out);
            auto condition_expr = clone_expr_with_substitution(
                if_stmt->condition.expression.get(), ctx, error_out);
            auto then_stmt = clone_stmt_impl(if_stmt->then_stmt.get(), ctx, error_out);
            auto else_stmt = clone_stmt_impl(if_stmt->else_stmt.get(), ctx, error_out);
            if ((if_stmt->init_stmt && !init_stmt) ||
                (if_stmt->condition.declaration && !condition_decl) ||
                (if_stmt->condition.expression && !condition_expr) ||
                (if_stmt->then_stmt && !then_stmt) ||
                (if_stmt->else_stmt && !else_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<IfStmt>(
                ControlCondition(
                    std::move(condition_decl),
                    std::move(condition_expr)),
                std::move(then_stmt),
                std::move(else_stmt),
                if_stmt->location,
                if_stmt->statement_kind,
                std::move(init_stmt),
                if_stmt->scope,
                if_stmt->constexpr_condition_value);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::CaseStmt: {
            const auto* case_stmt = static_cast<const CaseStmt*>(stmt);
            auto const_expr = clone_expr_with_substitution(
                case_stmt->const_expr.get(), ctx, error_out);
            auto range_end = clone_expr_with_substitution(
                case_stmt->range_end.get(), ctx, error_out);
            auto nested_stmt = clone_stmt_impl(case_stmt->stmt.get(), ctx, error_out);
            if ((case_stmt->const_expr && !const_expr) ||
                (case_stmt->range_end && !range_end) ||
                (case_stmt->stmt && !nested_stmt)) {
                return nullptr;
            }
            std::unique_ptr<CaseStmt> result;
            if (range_end) {
                result = std::make_unique<CaseStmt>(
                    std::move(const_expr),
                    std::move(range_end),
                    std::move(nested_stmt),
                    case_stmt->location);
            } else {
                result = std::make_unique<CaseStmt>(
                    std::move(const_expr),
                    std::move(nested_stmt),
                    case_stmt->location);
            }
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::DefaultStmt: {
            const auto* default_stmt = static_cast<const DefaultStmt*>(stmt);
            auto nested_stmt =
                clone_stmt_impl(default_stmt->stmt.get(), ctx, error_out);
            if (default_stmt->stmt && !nested_stmt) {
                return nullptr;
            }
            auto result = std::make_unique<DefaultStmt>(
                std::move(nested_stmt),
                default_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::LabeledStmt: {
            const auto* labeled = static_cast<const LabeledStmt*>(stmt);
            auto nested_stmt = clone_stmt_impl(labeled->stmt.get(), ctx, error_out);
            if (labeled->stmt && !nested_stmt) {
                return nullptr;
            }
            auto result = std::make_unique<LabeledStmt>(
                labeled->name,
                std::move(nested_stmt),
                labeled->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::GoToStmt: {
            const auto* goto_stmt = static_cast<const GoToStmt*>(stmt);
            auto result = std::make_unique<GoToStmt>(
                goto_stmt->name,
                goto_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ComputedGotoStmt: {
            const auto* goto_stmt = static_cast<const ComputedGotoStmt*>(stmt);
            auto target = clone_expr_with_substitution(
                goto_stmt->target.get(), ctx, error_out);
            if (goto_stmt->target && !target) {
                return nullptr;
            }
            auto result = std::make_unique<ComputedGotoStmt>(
                std::move(target),
                goto_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::SwitchStmt: {
            const auto* switch_stmt = static_cast<const SwitchStmt*>(stmt);
            auto condition_decl = clone_stmt_impl(
                switch_stmt->condition.declaration.get(), ctx, error_out);
            auto condition_expr = clone_expr_with_substitution(
                switch_stmt->condition.expression.get(), ctx, error_out);
            auto nested_stmt = clone_stmt_impl(switch_stmt->stmt.get(), ctx, error_out);
            if ((switch_stmt->condition.declaration && !condition_decl) ||
                (switch_stmt->condition.expression && !condition_expr) ||
                (switch_stmt->stmt && !nested_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<SwitchStmt>(
                ControlCondition(
                    std::move(condition_decl),
                    std::move(condition_expr)),
                std::move(nested_stmt),
                clone_scope(switch_stmt->scope, ctx),
                switch_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::WhileStmt: {
            const auto* while_stmt = static_cast<const WhileStmt*>(stmt);
            auto condition_decl = clone_stmt_impl(
                while_stmt->condition.declaration.get(), ctx, error_out);
            auto condition_expr = clone_expr_with_substitution(
                while_stmt->condition.expression.get(), ctx, error_out);
            auto body_stmt = clone_stmt_impl(while_stmt->body_stmt.get(), ctx, error_out);
            if ((while_stmt->condition.declaration && !condition_decl) ||
                (while_stmt->condition.expression && !condition_expr) ||
                (while_stmt->body_stmt && !body_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<WhileStmt>(
                ControlCondition(
                    std::move(condition_decl),
                    std::move(condition_expr)),
                std::move(body_stmt),
                clone_scope(while_stmt->scope, ctx),
                while_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::DoWhileStmt: {
            const auto* while_stmt = static_cast<const DoWhileStmt*>(stmt);
            auto condition = clone_expr_with_substitution(
                while_stmt->condition.get(), ctx, error_out);
            auto body_stmt = clone_stmt_impl(while_stmt->body_stmt.get(), ctx, error_out);
            if ((while_stmt->condition && !condition) ||
                (while_stmt->body_stmt && !body_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<DoWhileStmt>(
                std::move(condition),
                std::move(body_stmt),
                while_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ForStmt: {
            const auto* for_stmt = static_cast<const ForStmt*>(stmt);
            auto init = clone_stmt_impl(for_stmt->init.get(), ctx, error_out);
            auto cond_decl = clone_stmt_impl(
                for_stmt->cond.declaration.get(), ctx, error_out);
            auto cond_expr = clone_expr_with_substitution(
                for_stmt->cond.expression.get(), ctx, error_out);
            auto action = clone_expr_with_substitution(
                for_stmt->action.get(), ctx, error_out);
            auto body_stmt = clone_stmt_impl(for_stmt->body_stmt.get(), ctx, error_out);
            if ((for_stmt->init && !init) ||
                (for_stmt->cond.declaration && !cond_decl) ||
                (for_stmt->cond.expression && !cond_expr) ||
                (for_stmt->action && !action) ||
                (for_stmt->body_stmt && !body_stmt)) {
                return nullptr;
            }
            auto result = std::make_unique<ForStmt>(
                std::move(init),
                ControlCondition(
                    std::move(cond_decl),
                    std::move(cond_expr)),
                std::move(action),
                std::move(body_stmt),
                clone_scope(for_stmt->scope, ctx),
                for_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::CppRangeForStmt: {
            const auto* range_for = static_cast<const CppRangeForStmt*>(stmt);
            auto init_statement =
                clone_stmt_impl(range_for->init_statement.get(), ctx, error_out);
            if (range_for->init_statement && !init_statement) {
                return nullptr;
            }

            std::vector<std::unique_ptr<Decl>> side_decls;
            side_decls.reserve(range_for->range_declaration_side_decls.size());
            for (const auto& decl : range_for->range_declaration_side_decls) {
                auto cloned_decl = clone_decl_impl(decl.get(), ctx, error_out);
                if (decl && !cloned_decl) {
                    return nullptr;
                }
                side_decls.push_back(std::move(cloned_decl));
            }

            auto range_variable =
                clone_decl_impl(range_for->range_variable.get(), ctx, error_out);
            auto begin_variable =
                clone_decl_impl(range_for->begin_variable.get(), ctx, error_out);
            auto end_variable =
                clone_decl_impl(range_for->end_variable.get(), ctx, error_out);
            auto loop_variable =
                clone_decl_impl(range_for->loop_variable.get(), ctx, error_out);
            if ((range_for->range_variable && !range_variable) ||
                (range_for->begin_variable && !begin_variable) ||
                (range_for->end_variable && !end_variable) ||
                (range_for->loop_variable && !loop_variable)) {
                return nullptr;
            }

            auto condition = clone_expr_with_substitution(
                range_for->condition.get(), ctx, error_out);
            auto increment = clone_expr_with_substitution(
                range_for->increment.get(), ctx, error_out);
            auto body_stmt =
                clone_stmt_impl(range_for->body_stmt.get(), ctx, error_out);
            if ((range_for->condition && !condition) ||
                (range_for->increment && !increment) ||
                (range_for->body_stmt && !body_stmt)) {
                return nullptr;
            }

            auto result = std::make_unique<CppRangeForStmt>(
                std::move(init_statement),
                std::move(side_decls),
                std::move(range_variable),
                std::move(begin_variable),
                std::move(end_variable),
                std::move(loop_variable),
                std::move(condition),
                std::move(increment),
                std::move(body_stmt),
                clone_scope(range_for->scope, ctx),
                range_for->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ContinueStmt: {
            auto result = std::make_unique<ContinueStmt>(stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::BreakStmt: {
            auto result = std::make_unique<BreakStmt>(stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::EmptyStmt: {
            auto result = std::make_unique<EmptyStmt>(stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::ErrorStmt: {
            const auto* error_stmt = static_cast<const ErrorStmt*>(stmt);
            auto result = std::make_unique<ErrorStmt>(
                error_stmt->error_message,
                error_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            return result;
        }
        case StmtKind::AsmStmt: {
            const auto* asm_stmt = static_cast<const AsmStmt*>(stmt);
            auto result = std::make_unique<AsmStmt>(
                asm_stmt->asm_template,
                asm_stmt->is_volatile != 0,
                asm_stmt->is_inline != 0,
                asm_stmt->is_goto != 0,
                asm_stmt->has_colon_syntax != 0,
                asm_stmt->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            auto clone_operand_vec = [&](const std::vector<AsmOperand>& input,
                                         std::vector<AsmOperand>& output) -> bool {
                output.reserve(input.size());
                for (const auto& operand : input) {
                    AsmOperand cloned_operand;
                    cloned_operand.symbolic_name = operand.symbolic_name;
                    cloned_operand.constraint = operand.constraint;
                    cloned_operand.loc = operand.loc;
                    cloned_operand.expr = clone_expr_with_substitution(
                        operand.expr.get(), ctx, error_out);
                    if (operand.expr && !cloned_operand.expr) {
                        return false;
                    }
                    output.push_back(std::move(cloned_operand));
                }
                return true;
            };
            if (!clone_operand_vec(asm_stmt->output_operands, result->output_operands) ||
                !clone_operand_vec(asm_stmt->input_operands, result->input_operands)) {
                return nullptr;
            }
            result->clobbers = asm_stmt->clobbers;
            result->goto_labels = asm_stmt->goto_labels;
            return result;
        }
        case StmtKind::CppTryStmt:
            return fail_stmt_clone(
                error_out,
                "C++ try/catch statement cloning is not supported");
        default:
            return fail_stmt_clone(
                error_out,
                "unsupported statement clone kind " +
                    std::to_string(static_cast<int>(stmt->get_kind())));
    }
}

std::shared_ptr<Symbol> clone_symbol_shallow(const std::shared_ptr<Symbol>& sym,
                                             QualType cloned_type) {
    if (!sym) {
        return nullptr;
    }
    auto cloned = std::make_shared<Symbol>(
        sym->name,
        sym->kind,
        std::move(cloned_type),
        sym->storage_class,
        sym->linkage,
        sym->is_inline != 0);
    cloned->is_defined = sym->is_defined;
    cloned->is_constexpr = sym->is_constexpr;
    cloned->is_consteval = sym->is_consteval;
    cloned->is_deleted = sym->is_deleted;
    cloned->is_defaulted = sym->is_defaulted;
    cloned->is_hidden_friend = sym->is_hidden_friend;
    cloned->had_non_inline_declaration = sym->had_non_inline_declaration;
    cloned->is_block_byref = sym->is_block_byref;
    cloned->is_deprecated = sym->is_deprecated;
    cloned->deprecated_message = sym->deprecated_message;
    cloned->sym_attrs = sym->sym_attrs;
    cloned->enum_val = sym->enum_val;
    cloned->uid = sym->uid;
    cloned->asm_label = sym->asm_label;
    cloned->friend_access_type = sym->friend_access_type;
    cloned->function_trailing_requires_clause =
        sym->function_trailing_requires_clause;
    cloned->set_language_linkage(sym->get_language_linkage());
    return cloned;
}

const ObjectDecl* remap_record_decl(const ObjectDecl* record_decl,
                                    ASTCloneContext& ctx) {
    if (!record_decl) {
        return nullptr;
    }
    auto it = ctx.record_type_remap.find(record_decl);
    if (it == ctx.record_type_remap.end() || !it->second) {
        return record_decl;
    }
    auto remapped_type = it->second.as_shared<ObjectType>();
    if (!remapped_type) {
        return record_decl;
    }
    if (auto* remapped_decl = dyn_cast<ObjectDecl>(remapped_type->get_decl())) {
        return remapped_decl;
    }
    return record_decl;
}

const TemplateDecl* remap_template_decl(const TemplateDecl* template_decl,
                                        ASTCloneContext& ctx) {
    if (!template_decl) {
        return nullptr;
    }
    auto it = ctx.template_decl_remap.find(template_decl);
    if (it == ctx.template_decl_remap.end() || !it->second) {
        return template_decl;
    }
    return it->second;
}

std::shared_ptr<ObjectType> clone_object_type_for_decl(
    const ObjectDecl* object_decl,
    ASTCloneContext& ctx,
    std::string* error_out) {
    if (!object_decl) {
        return nullptr;
    }

    auto source_type = object_decl->get_record_type();
    auto cloned_type = std::make_shared<ObjectType>(
        object_decl->tag,
        object_decl->is_union != 0);
    if (!source_type) {
        return cloned_type;
    }

    cloned_type->is_packed = source_type->is_packed;
    cloned_type->is_transparent_union = source_type->is_transparent_union;
    cloned_type->requested_alignment = source_type->requested_alignment;
    cloned_type->pack_alignment = source_type->pack_alignment;
    if (source_type->class_template_specialization) {
        auto cloned_info =
            std::make_shared<ObjectType::ClassTemplateSpecializationInfo>(
                *source_type->class_template_specialization);
        cloned_info->primary_template =
            dyn_cast<ClassTemplateDecl>(
                const_cast<TemplateDecl*>(
                    remap_template_decl(
                        cloned_info->primary_template,
                        ctx)));
        auto rewritten_arguments =
            rewrite_template_arguments(cloned_info->arguments, ctx, error_out);
        if (rewritten_arguments.empty() &&
            !cloned_info->arguments.empty() &&
            error_out && !error_out->empty()) {
            return nullptr;
        }
        cloned_info->arguments = std::move(rewritten_arguments);
        cloned_type->class_template_specialization = std::move(cloned_info);
    }
    return cloned_type;
}

std::vector<ObjectType::Field> build_record_fields_from_decl_members(
    const ObjectDecl* record_decl) {
    std::vector<ObjectType::Field> fields;
    if (!record_decl) {
        return fields;
    }
    for (const auto& member : record_decl->fields) {
        auto* field_decl = dyn_cast<FieldDecl>(member.get());
        if (!field_decl) {
            continue;
        }
        if (field_decl->is_bitfield()) {
            fields.emplace_back(
                field_decl->name,
                field_decl->type,
                0,
                0,
                field_decl->bitfield_width,
                0,
                RecordMemberAccess::Public,
                field_decl->is_mutable,
                field_decl);
        } else {
            fields.emplace_back(
                field_decl->name,
                field_decl->type,
                0,
                RecordMemberAccess::Public,
                field_decl->is_mutable,
                field_decl);
        }
    }
    return fields;
}

RecordSemanticState clone_record_semantic_state_for_object_decl(
    const ObjectDecl* source,
    const ObjectDecl* destination,
    const ObjectType& destination_type,
    const std::unordered_map<const FieldDecl*, const FieldDecl*>& field_remap,
    ASTCloneContext& ctx) {
    const RecordSemanticState* source_state =
        record_semantics_cache_lookup(source, ctx.ast_ctx);
    RecordSemanticState state =
        source_state ? *source_state : RecordSemanticState{};
    if (!source_state) {
        state.is_incomplete = destination ? destination->fields.empty() : true;
        state.fields = build_record_fields_from_decl_members(destination);
    }

    auto remap_field_decl = [&](const FieldDecl* field_decl) -> const FieldDecl* {
        if (!field_decl) {
            return nullptr;
        }
        auto it = field_remap.find(field_decl);
        return it != field_remap.end() ? it->second : field_decl;
    };

    for (auto& base : state.bases) {
        base.type = rewrite_type(base.type, ctx);
        base.record_decl = remap_record_decl(base.record_decl, ctx);
    }
    for (auto& field : state.fields) {
        field.type = rewrite_type(field.type, ctx);
        field.decl = remap_field_decl(field.decl);
    }
    for (auto& method : state.methods) {
        method.type = rewrite_type(method.type, ctx);
        method.conversion_target_type =
            rewrite_type(method.conversion_target_type, ctx);
        method.symbol = remap_symbol(method.symbol, ctx);
    }
    for (auto& method_template : state.method_templates) {
        method_template.decl =
            dyn_cast<FunctionTemplateDecl>(
                const_cast<TemplateDecl*>(
                    remap_template_decl(method_template.decl, ctx)));
    }
    for (auto& static_member : state.static_data_members) {
        static_member.type = rewrite_type(static_member.type, ctx);
        static_member.symbol = remap_symbol(static_member.symbol, ctx);
    }
    for (auto& nested_type : state.nested_types) {
        nested_type.type = rewrite_type(nested_type.type, ctx);
        nested_type.symbol = remap_symbol(nested_type.symbol, ctx);
    }
    for (auto& nested_template : state.nested_templates) {
        nested_template.decl = remap_template_decl(nested_template.decl, ctx);
    }
    for (auto& friend_function : state.friend_functions) {
        friend_function.type = rewrite_type(friend_function.type, ctx);
        friend_function.symbol = remap_symbol(friend_function.symbol, ctx);
        friend_function.function_template =
            dyn_cast<FunctionTemplateDecl>(
                const_cast<TemplateDecl*>(
                    remap_template_decl(
                        friend_function.function_template,
                        ctx)));
    }
    for (auto& friend_type : state.friend_types) {
        friend_type.type = rewrite_type(friend_type.type, ctx);
        friend_type.class_template =
            dyn_cast<ClassTemplateDecl>(
                const_cast<TemplateDecl*>(
                    remap_template_decl(
                        friend_type.class_template,
                        ctx)));
    }
    for (auto& constructor : state.constructors) {
        constructor.type = rewrite_type(constructor.type, ctx);
        constructor.symbol = remap_symbol(constructor.symbol, ctx);
        constructor.function_template =
            dyn_cast<FunctionTemplateDecl>(
                const_cast<TemplateDecl*>(
                    remap_template_decl(
                        constructor.function_template,
                        ctx)));
    }
    for (auto& destructor : state.destructors) {
        destructor.type = rewrite_type(destructor.type, ctx);
        destructor.symbol = remap_symbol(destructor.symbol, ctx);
    }
    for (auto& slot : state.virtual_slots) {
        slot.final_symbol = remap_symbol(slot.final_symbol, ctx);
    }
    for (auto& virtual_base : state.virtual_bases) {
        virtual_base.type = rewrite_type(virtual_base.type, ctx);
        virtual_base.record_decl =
            remap_record_decl(virtual_base.record_decl, ctx);
    }
    for (auto& enumerator : state.enumerator_members) {
        enumerator.symbol = remap_symbol(enumerator.symbol, ctx);
    }

    if (state.bases.empty() && state.virtual_bases.empty()) {
        RecordSemanticState layout = compute_record_semantics(
            std::move(state.fields),
            destination_type.is_union,
            destination_type.is_packed,
            destination_type.requested_alignment,
            destination_type.pack_alignment,
            state.is_incomplete,
            ctx.ast_ctx && ctx.ast_ctx->abi_policy
                ? ctx.ast_ctx->abi_policy.get()
                : nullptr);
        state.fields = std::move(layout.fields);
        state.size_bits = layout.size_bits;
        state.alignment = layout.alignment;
        state.non_virtual_size_bits = layout.non_virtual_size_bits;
        state.non_virtual_alignment = layout.non_virtual_alignment;
        state.has_flexible_array_member = layout.has_flexible_array_member;
    }

    return state;
}

std::unique_ptr<Decl> clone_decl_impl(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    if (!decl) {
        return nullptr;
    }

    switch (decl->get_kind()) {
        case DeclKind::NopDecl: {
            auto result = std::make_unique<NopDecl>(decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::CppUsingDeclarationDecl: {
            const auto* using_decl =
                static_cast<const CppUsingDeclarationDecl*>(decl);
            auto result =
                std::make_unique<CppUsingDeclarationDecl>(decl->location);
            result->ordinary_symbols = using_decl->ordinary_symbols;
            result->template_decls = using_decl->template_decls;
            result->tag_decls = using_decl->tag_decls;
            result->replay_targets = using_decl->replay_targets;
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::NamespaceDecl: {
            const auto* namespace_decl = static_cast<const NamespaceDecl*>(decl);
            auto result = std::make_unique<NamespaceDecl>(
                namespace_decl->name,
                std::vector<Decl*>{},
                namespace_decl->semantic_context,
                namespace_decl->is_anonymous,
                namespace_decl->is_inline,
                namespace_decl->location);
            result->canonical_decl = result.get();
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::FieldDecl: {
            const auto* field_decl = static_cast<const FieldDecl*>(decl);
            auto cloned_type = rewrite_type(field_decl->type, ctx);
            std::unique_ptr<FieldDecl> result;
            if (field_decl->is_bitfield()) {
                result = std::make_unique<FieldDecl>(
                    cloned_type,
                    field_decl->name,
                    field_decl->bitfield_width,
                    field_decl->location);
            } else {
                result = std::make_unique<FieldDecl>(
                    cloned_type,
                    field_decl->name,
                    field_decl->location);
            }
            result->is_mutable = field_decl->is_mutable;
            result->default_member_initializer_kind =
                field_decl->default_member_initializer_kind;
            if (field_decl->default_member_initializer) {
                result->default_member_initializer =
                    clone_expr_with_substitution(
                        field_decl->default_member_initializer.get(),
                        ctx,
                        error_out);
                if (!result->default_member_initializer) {
                    return nullptr;
                }
            }
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::CppAccessSpecDecl: {
            const auto* access_spec_decl =
                static_cast<const CppAccessSpecDecl*>(decl);
            auto result = std::make_unique<CppAccessSpecDecl>(
                access_spec_decl->access,
                access_spec_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ObjectDecl: {
            const auto* object_decl = static_cast<const ObjectDecl*>(decl);
            auto cloned_type =
                clone_object_type_for_decl(object_decl, ctx, error_out);
            if (!cloned_type) {
                return nullptr;
            }
            ctx.record_type_remap[object_decl] = QualType(cloned_type);

            std::vector<std::unique_ptr<Decl>> cloned_fields;
            cloned_fields.reserve(object_decl->fields.size());
            std::unordered_map<const FieldDecl*, const FieldDecl*> field_remap;
            for (const auto& field : object_decl->fields) {
                auto cloned_field = clone_decl_impl(field.get(), ctx, error_out);
                if (field && !cloned_field) {
                    return nullptr;
                }
                if (auto* source_field = dyn_cast<FieldDecl>(field.get())) {
                    if (auto* cloned_field_decl =
                            dyn_cast<FieldDecl>(cloned_field.get())) {
                        field_remap[source_field] = cloned_field_decl;
                    }
                }
                cloned_fields.push_back(std::move(cloned_field));
            }

            auto result = std::make_unique<ObjectDecl>(
                object_decl->tag,
                std::move(cloned_fields),
                cloned_type,
                object_decl->is_union != 0,
                object_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            record_semantics_cache_set(
                ctx.ast_ctx,
                result.get(),
                clone_record_semantic_state_for_object_decl(
                    object_decl,
                    result.get(),
                    *cloned_type,
                    field_remap,
                    ctx));
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::CppRecordDecl: {
            const auto* record_decl = static_cast<const CppRecordDecl*>(decl);
            std::vector<CppBaseSpecifier> cloned_bases;
            cloned_bases.reserve(record_decl->bases.size());
            for (const auto& base : record_decl->bases) {
                CppBaseSpecifier cloned_base;
                cloned_base.type_name = base.type_name;
                cloned_base.type = rewrite_type(base.type, ctx);
                cloned_base.access = base.access;
                cloned_base.is_virtual_base = base.is_virtual_base;
                cloned_base.is_pack_expansion = base.is_pack_expansion;
                cloned_base.location = base.location;
                cloned_bases.push_back(std::move(cloned_base));
            }
            std::vector<std::unique_ptr<Decl>> cloned_members;
            cloned_members.reserve(record_decl->members.size());
            for (const auto& member : record_decl->members) {
                auto cloned_member = clone_decl_impl(member.get(), ctx, error_out);
                if (member && !cloned_member) {
                    return nullptr;
                }
                cloned_members.push_back(std::move(cloned_member));
            }
            auto result = std::make_unique<CppRecordDecl>(
                record_decl->record_kind,
                record_decl->name,
                std::move(cloned_bases),
                std::move(cloned_members),
                record_decl->is_definition != 0,
                record_decl->location);
            result->default_access = record_decl->default_access;
            result->definition_data = record_decl->definition_data;
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::TypedefDecl: {
            const auto* typedef_decl = static_cast<const TypedefDecl*>(decl);
            auto cloned_type = rewrite_type(typedef_decl->type, ctx);
            std::shared_ptr<Symbol> cloned_sym = nullptr;
            if (typedef_decl->sym) {
                cloned_sym = clone_symbol_shallow(
                    typedef_decl->sym,
                    rewrite_type(typedef_decl->sym->type, ctx));
                register_symbol(cloned_sym, ctx);
            }
            auto result = std::make_unique<TypedefDecl>(
                typedef_decl->name,
                cloned_type,
                std::move(cloned_sym),
                typedef_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::VariableDecl: {
            const auto* variable = static_cast<const VariableDecl*>(decl);
            auto cloned_type = rewrite_type(variable->type, ctx);
            auto cloned_original_type = rewrite_type(variable->original_type, ctx);
            std::shared_ptr<Symbol> cloned_sym = nullptr;
            if (variable->sym) {
                cloned_sym = clone_symbol_shallow(
                    variable->sym,
                    rewrite_type(variable->sym->type, ctx));
                ctx.symbol_remap[variable->sym.get()] = cloned_sym;
                register_symbol(cloned_sym, ctx);
            }
            auto cloned_init =
                clone_expr_with_substitution(variable->init.get(), ctx, error_out);
            if (variable->init && !cloned_init) {
                return nullptr;
            }
            auto result = std::make_unique<VariableDecl>(
                cloned_type,
                variable->name,
                std::move(cloned_init),
                cloned_sym,
                variable->storage_class,
                variable->is_inline != 0,
                variable->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->is_constexpr = variable->is_constexpr;
            result->is_thread_local = variable->is_thread_local;
            result->is_block_byref = variable->is_block_byref;
            result->original_type = cloned_original_type;
            result->explicit_specialization_arguments =
                rewrite_template_arguments(
                    variable->explicit_specialization_arguments,
                    ctx,
                    error_out);
            result->has_explicit_specialization_argument_list =
                variable->has_explicit_specialization_argument_list;
            result->set_language_linkage(variable->get_language_linkage());
            if (variable->asm_label) {
                result->set_asm_label(*variable->asm_label);
            }
            if (result->sym) {
                result->sym->variable_definition = result.get();
            }
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ParamDecl: {
            const auto* param = static_cast<const ParamDecl*>(decl);
            auto cloned_type = rewrite_type(param->type, ctx);
            std::shared_ptr<Symbol> cloned_sym = nullptr;
            if (param->sym) {
                cloned_sym = clone_symbol_shallow(
                    param->sym,
                    rewrite_type(param->sym->type, ctx));
                ctx.symbol_remap[param->sym.get()] = cloned_sym;
                register_symbol(cloned_sym, ctx);
            }
            auto result = std::make_unique<ParamDecl>(
                cloned_type,
                param->get_name(),
                cloned_sym,
                param->storage_class,
                param->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->is_constexpr = param->is_constexpr;
            result->is_parameter_pack = param->is_parameter_pack;
            result->original_type =
                rewrite_type(QualType(param->original_type), ctx).get_shared();
            if (const Expr* default_arg = get_param_decl_default_argument(param)) {
                auto cloned_default = clone_expr_with_substitution(
                    default_arg,
                    ctx,
                    error_out);
                if (!cloned_default) {
                    return nullptr;
                }
                set_param_decl_default_argument(
                    result.get(),
                    std::move(cloned_default));
            }
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::StaticAssertDecl: {
            const auto* static_assert_decl = static_cast<const StaticAssertDecl*>(decl);
            auto condition = clone_expr_with_substitution(
                static_assert_decl->condition.get(), ctx, error_out);
            if (static_assert_decl->condition && !condition) {
                return nullptr;
            }
            auto result = std::make_unique<StaticAssertDecl>(
                std::move(condition),
                static_assert_decl->message,
                static_assert_decl->has_message != 0,
                static_assert_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ClassTemplateDecl: {
            const auto* class_template =
                static_cast<const ClassTemplateDecl*>(decl);
            auto cloned_parameters =
                clone_template_parameter_list(
                    class_template->parameters,
                    ctx,
                    error_out);
            if (cloned_parameters.size() != class_template->parameters.size()) {
                return nullptr;
            }
            auto cloned_templated_decl =
                clone_decl_impl(
                    class_template->get_templated_decl(),
                    ctx,
                    error_out);
            if (class_template->get_templated_decl() &&
                !cloned_templated_decl) {
                return nullptr;
            }
            auto result = std::make_unique<ClassTemplateDecl>(
                std::move(cloned_parameters),
                std::move(cloned_templated_decl),
                class_template->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->canonical_decl = result.get();
            result->set_pattern_template_decl(
                class_template->get_pattern_template_decl());
            if (class_template->associated_constraint) {
                result->associated_constraint =
                    clone_expr_with_substitution(
                        class_template->associated_constraint.get(),
                        ctx,
                        error_out);
                if (!result->associated_constraint) {
                    return nullptr;
                }
            }
            ctx.template_decl_remap[class_template] = result.get();
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ClassTemplatePartialSpecializationDecl: {
            const auto* partial =
                static_cast<const ClassTemplatePartialSpecializationDecl*>(decl);
            auto cloned_parameters =
                clone_template_parameter_list(
                    partial->parameters,
                    ctx,
                    error_out);
            if (cloned_parameters.size() != partial->parameters.size()) {
                return nullptr;
            }
            auto cloned_arguments =
                rewrite_template_arguments(
                    partial->specialization_arguments,
                    ctx,
                    error_out);
            if (cloned_arguments.empty() &&
                !partial->specialization_arguments.empty() &&
                error_out && !error_out->empty()) {
                return nullptr;
            }
            const ClassTemplateDecl* cloned_primary = partial->primary_template();
            bool cloned_primary_is_remapped = false;
            if (auto it = ctx.template_decl_remap.find(partial->primary_template());
                it != ctx.template_decl_remap.end() && it->second) {
                if (auto* remapped_primary =
                        dyn_cast<ClassTemplateDecl>(it->second)) {
                    cloned_primary = remapped_primary;
                    cloned_primary_is_remapped = true;
                }
            }
            auto cloned_templated_decl =
                clone_decl_impl(partial->get_templated_decl(), ctx, error_out);
            if (partial->get_templated_decl() && !cloned_templated_decl) {
                return nullptr;
            }
            auto result =
                std::make_unique<ClassTemplatePartialSpecializationDecl>(
                    cloned_primary,
                    std::move(cloned_parameters),
                    std::move(cloned_arguments),
                    std::move(cloned_templated_decl),
                    partial->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->canonical_decl = result.get();
            result->set_pattern_template_decl(
                partial->get_pattern_template_decl());
            if (partial->associated_constraint) {
                result->associated_constraint =
                    clone_expr_with_substitution(
                        partial->associated_constraint.get(),
                        ctx,
                        error_out);
                if (!result->associated_constraint) {
                    return nullptr;
                }
            }
            ctx.template_decl_remap[partial] = result.get();
            if (cloned_primary_is_remapped && cloned_primary) {
                auto* mutable_primary =
                    const_cast<ClassTemplateDecl*>(cloned_primary);
                mutable_primary->add_partial_specialization(result.get());
            }
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::AliasTemplateDecl: {
            const auto* alias_template =
                static_cast<const AliasTemplateDecl*>(decl);
            auto cloned_parameters =
                clone_template_parameter_list(
                    alias_template->parameters,
                    ctx,
                    error_out);
            if (cloned_parameters.size() != alias_template->parameters.size()) {
                return nullptr;
            }
            auto cloned_templated_decl =
                clone_decl_impl(
                    alias_template->get_templated_decl(),
                    ctx,
                    error_out);
            if (alias_template->get_templated_decl() && !cloned_templated_decl) {
                return nullptr;
            }
            auto result = std::make_unique<AliasTemplateDecl>(
                std::move(cloned_parameters),
                std::move(cloned_templated_decl),
                alias_template->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->canonical_decl = result.get();
            result->set_pattern_template_decl(
                alias_template->get_pattern_template_decl());
            if (alias_template->associated_constraint) {
                result->associated_constraint =
                    clone_expr_with_substitution(
                        alias_template->associated_constraint.get(),
                        ctx,
                        error_out);
                if (!result->associated_constraint) {
                    return nullptr;
                }
            }
            ctx.template_decl_remap[alias_template] = result.get();
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::VariableTemplateDecl: {
            const auto* variable_template =
                static_cast<const VariableTemplateDecl*>(decl);
            auto cloned_parameters =
                clone_template_parameter_list(
                    variable_template->parameters,
                    ctx,
                    error_out);
            if (cloned_parameters.size() != variable_template->parameters.size()) {
                return nullptr;
            }
            auto cloned_templated_decl =
                clone_decl_impl(
                    variable_template->get_templated_decl(),
                    ctx,
                    error_out);
            if (variable_template->get_templated_decl() &&
                !cloned_templated_decl) {
                return nullptr;
            }
            auto result = std::make_unique<VariableTemplateDecl>(
                std::move(cloned_parameters),
                std::move(cloned_templated_decl),
                variable_template->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            result->canonical_decl = result.get();
            result->is_pattern_complete =
                variable_template->is_pattern_complete;
            result->set_pattern_template_decl(
                variable_template->get_pattern_template_decl());
            if (variable_template->associated_constraint) {
                result->associated_constraint =
                    clone_expr_with_substitution(
                        variable_template->associated_constraint.get(),
                        ctx,
                        error_out);
                if (!result->associated_constraint) {
                    return nullptr;
                }
            }
            ctx.template_decl_remap[variable_template] = result.get();
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        case DeclKind::ErrorDecl: {
            const auto* error_decl = static_cast<const ErrorDecl*>(decl);
            auto result = std::make_unique<ErrorDecl>(
                error_decl->error_message,
                error_decl->location);
            assign_node_id(result.get(), ctx.ast_ctx);
            if (!copy_decl_side_tables_impl(decl, result.get(), ctx, error_out)) {
                return nullptr;
            }
            return result;
        }
        default:
            return fail_decl_clone(
                error_out,
                "unsupported declaration clone kind " +
                    std::to_string(static_cast<int>(decl->get_kind())));
    }
}
} // namespace

bool copy_decl_side_tables(const Decl* source,
                           Decl* destination,
                           ASTCloneContext& ctx,
                           std::string* error_out) {
    return copy_decl_side_tables_impl(source, destination, ctx, error_out);
}

std::unique_ptr<Expr> clone_expr_with_substitution(
    const Expr* expr,
    ASTCloneContext& ctx,
    std::string* error_out) {
    auto cloned = clone_expr_tree(expr, ctx.ast_ctx, error_out);
    if (!cloned) {
        return nullptr;
    }
    if (const auto* original_lambda = dyn_cast<const CppLambdaExpr>(expr)) {
        auto* cloned_lambda = dyn_cast<CppLambdaExpr>(cloned.get());
        const auto* original_owner = original_lambda->semantic_info.semantic_owner();
        QualType cloned_closure_type =
            cloned_lambda ? cloned_lambda->semantic_info.closure_type() : QualType();
        if (original_owner && cloned_closure_type) {
            ctx.record_type_remap[original_owner] = cloned_closure_type;
        }
    }
    auto saved_rewrite_expr = std::move(ctx.rewrite_expr);
    ctx.rewrite_expr = nullptr;
    if (!rewrite_expr_tree(cloned, ctx, error_out)) {
        ctx.rewrite_expr = std::move(saved_rewrite_expr);
        return nullptr;
    }
    ctx.rewrite_expr = std::move(saved_rewrite_expr);
    return cloned;
}

bool rewrite_expr_tree_in_place(std::unique_ptr<Expr>& expr,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return rewrite_expr_tree(expr, ctx, error_out);
}

std::unique_ptr<Stmt> clone_stmt_tree(const Stmt* stmt,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return clone_stmt_impl(stmt, ctx, error_out);
}

bool rewrite_stmt_tree_in_place(std::unique_ptr<Stmt>& stmt,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return rewrite_stmt_tree_in_place_impl(stmt, ctx, error_out);
}

std::unique_ptr<Decl> clone_decl_tree(const Decl* decl,
                                      ASTCloneContext& ctx,
                                      std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return clone_decl_impl(decl, ctx, error_out);
}

bool rewrite_decl_tree_in_place(std::unique_ptr<Decl>& decl,
                                ASTCloneContext& ctx,
                                std::string* error_out) {
    std::string local_error;
    if (!error_out) {
        error_out = &local_error;
    } else {
        error_out->clear();
    }
    return rewrite_decl_tree_in_place_impl(decl, ctx, error_out);
}
