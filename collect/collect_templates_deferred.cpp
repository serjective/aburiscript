#include "collect.h"

namespace {
bool decltype_uses_declared_entity_rule(bool use_declared_type_rule,
                                        const Expr* expr) {
    if (!use_declared_type_rule || !expr) {
        return false;
    }
    auto* stripped = Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    return isa<VarRef>(stripped) ||
           isa<MemberExpr>(stripped) ||
           isa<UnresolvedLookupExpr>(stripped) ||
           isa<UnresolvedMemberExpr>(stripped);
}

bool template_arguments_contain_dependency(
    const std::vector<TemplateArgument>& arguments,
    const ASTContext* ast_ctx) {
    for (const auto& argument : arguments) {
        if (template_argument_depends_on_template_parameters(argument, ast_ctx)) {
            return true;
        }
    }
    return false;
}

bool template_arguments_contain_dependency(
    const std::optional<std::vector<TemplateArgument>>& arguments,
    const ASTContext* ast_ctx) {
    if (!arguments.has_value()) {
        return false;
    }
    return template_arguments_contain_dependency(*arguments, ast_ctx);
}

bool symbol_is_non_type_template_parameter(const Symbol* sym) {
    return sym &&
           isa<TemplateNonTypeParmDecl>(sym->template_parameter_decl);
}

bool variable_template_specialization_depends_on_template_parameters(
    const Symbol* sym,
    const ASTContext* ast_ctx) {
    if (!sym) {
        return false;
    }
    const auto* specialization_info =
        get_symbol_variable_template_specialization(sym);
    if (!specialization_info) {
        return false;
    }
    for (const auto& argument : specialization_info->arguments) {
        if (template_argument_depends_on_template_parameters(
                argument,
                ast_ctx)) {
            return true;
        }
    }
    return false;
}

const VariableDecl* find_template_dependent_variable_definition(
    const Symbol* sym) {
    if (!sym || sym->kind != SymbolKind::VARIABLE) {
        return nullptr;
    }
    if (sym->variable_definition && sym->variable_definition->init) {
        return sym->variable_definition;
    }

    QualType owner_type = get_symbol_owner_record_type(sym);
    auto owner_record = desugar_type(owner_type).as_shared<ObjectType>();
    auto* owner_decl =
        owner_record ? dyn_cast<ObjectDecl>(owner_record->get_decl()) : nullptr;
    if (!owner_decl) {
        return nullptr;
    }

    const RecordSemanticState* state = record_semantics_cache_lookup(owner_decl);
    if (!state) {
        return nullptr;
    }

    for (const auto& static_member : state->static_data_members) {
        if (!static_member.decl || !static_member.decl->init) {
            continue;
        }
        if ((static_member.symbol && static_member.symbol.get() == sym) ||
            (static_member.decl->sym &&
             static_member.decl->sym.get() == sym)) {
            return static_member.decl;
        }
    }

    return nullptr;
}

bool expr_depends_on_template_parameters_impl(
    const Expr* expr,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols);

bool variable_definition_depends_on_template_parameters(
    const Symbol* sym,
    const ASTContext* ast_ctx,
    std::unordered_set<const Symbol*>& active_variable_symbols) {
    if (!sym || sym->kind != SymbolKind::VARIABLE ||
        !active_variable_symbols.insert(sym).second) {
        return false;
    }

    const VariableDecl* definition = find_template_dependent_variable_definition(sym);
    bool depends = false;
    if (definition) {
        depends =
            type_depends_on_template_parameters(definition->type, ast_ctx) ||
            type_depends_on_template_parameters(
                QualType(definition->original_type),
                ast_ctx) ||
            (definition->init &&
             expr_depends_on_template_parameters_impl(
                 definition->init.get(),
                 ast_ctx,
                 active_variable_symbols));
    }

    active_variable_symbols.erase(sym);
    return depends;
}

bool expr_depends_on_template_parameters_impl(const Expr* expr,
                                              const ASTContext* ast_ctx,
                                              std::unordered_set<const Symbol*>&
                                                  active_variable_symbols) {
    if (!expr) {
        return false;
    }

    auto* stripped = Collect::strip_implicit_casts(const_cast<Expr*>(expr));
    if (!stripped) {
        return false;
    }

    if (auto* var_ref = dyn_cast<VarRef>(stripped)) {
        if (symbol_is_non_type_template_parameter(var_ref->symref.get())) {
            return true;
        }
        if (variable_template_specialization_depends_on_template_parameters(
                var_ref->symref.get(),
                ast_ctx)) {
            return true;
        }
        if (variable_definition_depends_on_template_parameters(
                var_ref->symref.get(),
                ast_ctx,
                active_variable_symbols)) {
            return true;
        }
    }

    if (type_depends_on_template_parameters(stripped->get_type(), ast_ctx)) {
        return true;
    }

    switch (stripped->get_kind()) {
        case StmtKind::UnresolvedLookupExpr: {
            const auto* lookup =
                static_cast<const UnresolvedLookupExpr*>(stripped);
            return lookup->is_dependent ||
                   template_arguments_contain_dependency(
                       lookup->explicit_template_arguments,
                       ast_ctx);
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member =
                static_cast<const UnresolvedMemberExpr*>(stripped);
            return member->is_current_instantiation ||
                   member->names_dependent_base ||
                   expr_depends_on_template_parameters_impl(
                       member->base.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   template_arguments_contain_dependency(
                       member->explicit_template_arguments,
                       ast_ctx);
        }
        case StmtKind::DependentCallExpr:
        case StmtKind::DependentArraySubscriptExpr:
        case StmtKind::DependentUnaryExpr:
        case StmtKind::DependentBinaryExpr:
        case StmtKind::DependentMemberPointerAccessExpr:
        case StmtKind::PackExpansionExpr:
        case StmtKind::FoldExpr:
            return true;
        case StmtKind::ConceptSpecializationExpr: {
            const auto* concept_expr =
                static_cast<const ConceptSpecializationExpr*>(stripped);
            for (const auto& argument : concept_expr->arguments) {
                if (template_argument_depends_on_template_parameters(
                        argument,
                        ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::RequiresExpr: {
            const auto* requires_expr =
                static_cast<const RequiresExpr*>(stripped);
            for (const auto& parameter : requires_expr->parameters) {
                if (!parameter) {
                    continue;
                }
                if (type_depends_on_template_parameters(parameter->type, ast_ctx) ||
                    type_depends_on_template_parameters(
                        QualType(parameter->original_type),
                        ast_ctx)) {
                    return true;
                }
                if (const Expr* default_arg =
                        get_param_decl_default_argument(parameter.get())) {
                    if (expr_depends_on_template_parameters_impl(
                            default_arg,
                            ast_ctx,
                            active_variable_symbols)) {
                        return true;
                    }
                }
            }
            for (const auto& requirement : requires_expr->requirements) {
                if (expr_depends_on_template_parameters_impl(
                        requirement.expr.get(),
                        ast_ctx,
                        active_variable_symbols) ||
                    type_depends_on_template_parameters(
                        requirement.type_requirement,
                        ast_ctx) ||
                    (requirement.return_type_constraint.has_value() &&
                     template_arguments_contain_dependency(
                         requirement.return_type_constraint->template_arguments,
                         ast_ctx))) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::UnaryOperation:
            return expr_depends_on_template_parameters_impl(
                static_cast<const UnaryOperation*>(stripped)->exp.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::BinaryOperation: {
            const auto* binary = static_cast<const BinaryOperation*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       binary->left.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       binary->right.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CppBuiltinThreeWayCompareExpr: {
            const auto* compare =
                static_cast<const CppBuiltinThreeWayCompareExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       compare->left.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       compare->right.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CompoundAssignOperation: {
            const auto* binary =
                static_cast<const CompoundAssignOperation*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       binary->left.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       binary->right.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CondExpr: {
            const auto* cond = static_cast<const CondExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       cond->condition.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       cond->true_expr.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       cond->false_expr.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::ExplicitCast:
            return expr_depends_on_template_parameters_impl(
                static_cast<const ExplicitCast*>(stripped)->expr.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::ArraySubscriptExpr: {
            const auto* subscript =
                static_cast<const ArraySubscriptExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       subscript->array.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       subscript->index.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::FuncCall: {
            const auto* call = static_cast<const FuncCall*>(stripped);
            if (expr_depends_on_template_parameters_impl(
                    call->func.get(),
                    ast_ctx,
                    active_variable_symbols)) {
                return true;
            }
            for (const auto& arg : call->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppMemberCallExpr: {
            const auto* call = static_cast<const CppMemberCallExpr*>(stripped);
            return call->lowered_call &&
                   expr_depends_on_template_parameters_impl(
                       call->lowered_call.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::CppConstructExpr: {
            const auto* construct =
                static_cast<const CppConstructExpr*>(stripped);
            for (const auto& arg : construct->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppValueInitExpr:
            return type_depends_on_template_parameters(
                static_cast<const CppValueInitExpr*>(stripped)->ctype,
                ast_ctx);
        case StmtKind::CppFunctionStyleCastExpr: {
            const auto* cast =
                static_cast<const CppFunctionStyleCastExpr*>(stripped);
            if (type_depends_on_template_parameters(
                    cast->target_type,
                    ast_ctx)) {
                return true;
            }
            for (const auto& arg : cast->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::MemberExpr:
            return expr_depends_on_template_parameters_impl(
                static_cast<const MemberExpr*>(stripped)->base.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::MemberPointerAccessExpr: {
            const auto* access =
                static_cast<const MemberPointerAccessExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       access->base.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   expr_depends_on_template_parameters_impl(
                       access->member_pointer.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        case StmtKind::InitListExpr: {
            const auto* init_list = static_cast<const InitListExpr*>(stripped);
            for (const auto& element : init_list->elements) {
                if (expr_depends_on_template_parameters_impl(
                        element.value.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
                for (const auto& designator : element.designators) {
                    if (expr_depends_on_template_parameters_impl(
                            designator.index.get(),
                            ast_ctx,
                            active_variable_symbols) ||
                        expr_depends_on_template_parameters_impl(
                            designator.range_end.get(),
                            ast_ctx,
                            active_variable_symbols)) {
                        return true;
                    }
                }
            }
            return false;
        }
        case StmtKind::CompoundLiteralExpr:
            return expr_depends_on_template_parameters_impl(
                static_cast<const CompoundLiteralExpr*>(stripped)->init.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::SizeOfExpr: {
            const auto* sizeof_expr = static_cast<const SizeOfExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       sizeof_expr->expr_operand.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   type_depends_on_template_parameters(
                       sizeof_expr->type_operand,
                       ast_ctx);
        }
        case StmtKind::SizeOfPackExpr:
            return true;
        case StmtKind::AlignOfExpr: {
            const auto* alignof_expr =
                static_cast<const AlignOfExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       alignof_expr->expr_operand.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   type_depends_on_template_parameters(
                       alignof_expr->type_operand,
                       ast_ctx);
        }
        case StmtKind::CppNoexceptExpr:
            return expr_depends_on_template_parameters_impl(
                static_cast<const CppNoexceptExpr*>(stripped)->operand.get(),
                ast_ctx,
                active_variable_symbols);
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(stripped);
            return expr_depends_on_template_parameters_impl(
                       pseudo_dtor->base.get(),
                       ast_ctx,
                       active_variable_symbols) ||
                   type_depends_on_template_parameters(
                       pseudo_dtor->destroyed_type,
                       ast_ctx);
        }
        case StmtKind::GenericExpr: {
            const auto* generic = static_cast<const GenericExpr*>(stripped);
            if (expr_depends_on_template_parameters_impl(
                    generic->controlling_expr.get(),
                    ast_ctx,
                    active_variable_symbols)) {
                return true;
            }
            for (const auto& assoc : generic->associations) {
                if (expr_depends_on_template_parameters_impl(
                        assoc.expr.get(),
                        ast_ctx,
                        active_variable_symbols) ||
                    type_depends_on_template_parameters(assoc.type, ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::BuiltinCallExpr: {
            const auto* builtin = static_cast<const BuiltinCallExpr*>(stripped);
            for (const auto& arg : builtin->args) {
                if (expr_depends_on_template_parameters_impl(
                        arg.get(),
                        ast_ctx,
                        active_variable_symbols)) {
                    return true;
                }
            }
            for (const auto& type_arg : builtin->type_args) {
                if (type_depends_on_template_parameters(type_arg, ast_ctx)) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::CppTypeIdExpr:
            return type_depends_on_template_parameters(
                       static_cast<const CppTypeIdExpr*>(stripped)->type_operand,
                       ast_ctx) ||
                   expr_depends_on_template_parameters_impl(
                       static_cast<const CppTypeIdExpr*>(stripped)->expr_operand.get(),
                       ast_ctx,
                       active_variable_symbols);
        case StmtKind::CppDynamicCastExpr: {
            const auto* cast = static_cast<const CppDynamicCastExpr*>(stripped);
            return type_depends_on_template_parameters(cast->target_type, ast_ctx) ||
                   expr_depends_on_template_parameters_impl(
                       cast->expr.get(),
                       ast_ctx,
                       active_variable_symbols);
        }
        default:
            return false;
    }
}
} // namespace

bool Collect::contains_deferred_semantic_type(
    const std::shared_ptr<CType>& type) const {
    if (!type) {
        return false;
    }
    if (isa<TypeofExprType>(type.get()) ||
        isa<DecltypeExprType>(type.get()) ||
        isa<BuiltinTypeTransformType>(type.get())) {
        return true;
    }
    if (auto typedef_type = dyn_cast_shared<TypedefType>(type)) {
        return contains_deferred_semantic_type(
            typedef_type->underlying_type.get_shared());
    }
    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(type)) {
        auto resolved_type =
            query_lookup_template_specialization_resolved_type(
                specialization.get());
        if (!resolved_type && !specialization->is_dependent) {
            return true;
        }
        if (resolved_type &&
            contains_deferred_semantic_type(resolved_type.get_shared())) {
            return true;
        }
        for (const auto& argument : specialization->arguments) {
            if (argument.kind == TemplateArgumentKind::Type) {
                if (contains_deferred_semantic_type(argument.type.get_shared())) {
                    return true;
                }
            } else if (contains_deferred_semantic_type(
                           argument.value_type.get_shared())) {
                return true;
            }
        }
        return false;
    }
    if (auto dependent_name = dyn_cast_shared<DependentNameType>(type)) {
        auto resolved_type =
            query_lookup_dependent_name_resolved_type(dependent_name.get());
        if (!resolved_type) {
            return true;
        }
        if (contains_deferred_semantic_type(resolved_type.get_shared())) {
            return true;
        }
        if (contains_deferred_semantic_type(
                dependent_name->qualifier_type.get_shared())) {
            return true;
        }
        for (const auto& argument : dependent_name->template_arguments) {
            if (argument.kind == TemplateArgumentKind::Type) {
                if (contains_deferred_semantic_type(argument.type.get_shared())) {
                    return true;
                }
            } else if (contains_deferred_semantic_type(
                           argument.value_type.get_shared())) {
                return true;
            }
        }
        return false;
    }
    if (auto ptr = dyn_cast_shared<PointerType>(type)) {
        return contains_deferred_semantic_type(ptr->pointed_type.get_shared());
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(type)) {
        return contains_deferred_semantic_type(ref->referred_type.get_shared());
    }
    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(type)) {
        return contains_deferred_semantic_type(mem_ptr->class_type.get_shared()) ||
               contains_deferred_semantic_type(mem_ptr->member_type.get_shared());
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(type)) {
        return contains_deferred_semantic_type(blk->pointed_type.get_shared());
    }
    if (auto arr = dyn_cast_shared<ArrayType>(type)) {
        return contains_deferred_semantic_type(arr->element_type.get_shared());
    }
    if (auto func = dyn_cast_shared<FunctionType>(type)) {
        if (contains_deferred_semantic_type(func->ret_type.get_shared())) {
            return true;
        }
        for (const auto& parameter : func->parameters) {
            if (contains_deferred_semantic_type(parameter.get_shared())) {
                return true;
            }
        }
        return false;
    }
    if (auto vec = dyn_cast_shared<VectorType>(type)) {
        return contains_deferred_semantic_type(vec->element_type.get_shared());
    }
    return false;
}

bool Collect::decltype_expression_requires_deferred_resolution(
    const Expr* expr) const {
    if (!expr) {
        return true;
    }

    auto* stripped = strip_implicit_casts(const_cast<Expr*>(expr));
    if (!stripped) {
        return true;
    }

    if (expression_depends_on_template_parameters(stripped)) {
        return true;
    }

    switch (stripped->get_kind()) {
        case StmtKind::UnresolvedLookupExpr:
            return static_cast<const UnresolvedLookupExpr*>(stripped)
                ->is_dependent;
        case StmtKind::DependentCallExpr:
        case StmtKind::DependentArraySubscriptExpr:
        case StmtKind::DependentUnaryExpr:
        case StmtKind::DependentBinaryExpr:
        case StmtKind::DependentMemberPointerAccessExpr:
        case StmtKind::FoldExpr:
            return true;
        case StmtKind::ConceptSpecializationExpr: {
            const auto* concept_expr =
                static_cast<const ConceptSpecializationExpr*>(stripped);
            for (const auto& argument : concept_expr->arguments) {
                if (template_argument_depends_on_template_parameters(
                        argument,
                        ast_ctx_.get())) {
                    return true;
                }
            }
            return false;
        }
        case StmtKind::RequiresExpr:
            return expression_depends_on_template_parameters(stripped);
        case StmtKind::CppPseudoDestructorExpr: {
            const auto* pseudo_dtor =
                static_cast<const CppPseudoDestructorExpr*>(stripped);
            return (pseudo_dtor->base &&
                    expression_depends_on_template_parameters(
                        pseudo_dtor->base.get())) ||
                   type_depends_on_template_parameters(
                       pseudo_dtor->destroyed_type,
                       ast_ctx_.get());
        }
        case StmtKind::UnresolvedMemberExpr: {
            const auto* member =
                static_cast<const UnresolvedMemberExpr*>(stripped);
            if (member->is_current_instantiation ||
                member->names_dependent_base) {
                return true;
            }
            if (member->base &&
                type_depends_on_template_parameters(
                    member->base->get_type(),
                    ast_ctx_.get())) {
                return true;
            }
            return false;
        }
        default:
            break;
    }

    auto expr_type = stripped->get_type();
    if (!expr_type) {
        return true;
    }

    return type_depends_on_template_parameters(expr_type, ast_ctx_.get());
}

bool Collect::expression_depends_on_template_parameters(
    const Expr* expr) const {
    std::unordered_set<const Symbol*> active_variable_symbols;
    return expr_depends_on_template_parameters_impl(
        expr,
        ast_ctx_.get(),
        active_variable_symbols);
}

QualType Collect::resolve_deferred_decltype_expr_type(
    const DecltypeExprType& decltype_type,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    return resolve_decltype_expression_type(
        decltype_type.expr.get(),
        decltype_type.use_declared_type_rule,
        original_type,
        loc,
        mode);
}

QualType Collect::resolve_decltype_expression_type(
    Expr* expr,
    bool use_declared_type_rule,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    if (!expr) {
        if (mode == DeferredTypeResolutionMode::Finalize) {
            report_error("cannot determine type of expression in decltype", loc);
        }
        return QualType();
    }

    auto* stripped_expr = strip_implicit_casts(expr);
    if (decltype_expression_requires_deferred_resolution(stripped_expr)) {
        return original_type;
    }

    auto expr_type = stripped_expr ? stripped_expr->get_type() : QualType();
    expr_type = resolve_deferred_semantic_type_impl(expr_type, loc, mode);
    if (!expr_type) {
        if (mode == DeferredTypeResolutionMode::Finalize) {
            report_error("cannot determine type of expression in decltype", loc);
        }
        return QualType();
    }

    if (decltype_uses_declared_entity_rule(
            use_declared_type_rule,
            stripped_expr)) {
        return QualType(
            expr_type.get_shared(),
            static_cast<uint8_t>(
                original_type.get_qualifiers() | expr_type.get_qualifiers()));
    }

    switch (classify_value_category(stripped_expr)) {
        case ValueCategory::LValue:
            expr_type = make_reference_type(expr_type, ReferenceKind::LValue);
            break;
        case ValueCategory::XValue:
            expr_type = make_reference_type(expr_type, ReferenceKind::RValue);
            break;
        case ValueCategory::PRValue:
        case ValueCategory::Unknown:
            break;
    }

    return QualType(
        expr_type.get_shared(),
        static_cast<uint8_t>(
            original_type.get_qualifiers() | expr_type.get_qualifiers()));
}

ObjectDecl* Collect::try_instantiate_class_template_specialization(
    const ClassTemplateDecl* class_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!diag_engine_) {
        return instantiate_class_template_specialization(
            class_template,
            arguments,
            loc);
    }
    auto checkpoint = diag_engine_->checkpoint();
    auto* specialization = instantiate_class_template_specialization(
        class_template,
        arguments,
        loc);
    diag_engine_->restore(checkpoint);
    return specialization;
}

QualType Collect::try_instantiate_alias_template_specialization(
    const AliasTemplateDecl* alias_template,
    const std::vector<TemplateArgument>& arguments,
    SrcLoc loc) {
    if (!diag_engine_) {
        return instantiate_alias_template_specialization(
            alias_template,
            arguments,
            loc);
    }
    auto checkpoint = diag_engine_->checkpoint();
    auto specialization =
        instantiate_alias_template_specialization(alias_template, arguments, loc);
    diag_engine_->restore(checkpoint);
    return specialization;
}

void Collect::rewrite_deferred_template_arguments_in_place(
    std::vector<TemplateArgument>& arguments,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    for (auto& argument : arguments) {
        if (argument.kind == TemplateArgumentKind::Type) {
            argument.type = resolve_deferred_semantic_type_impl(
                argument.type,
                loc,
                mode);
        } else {
            argument.value_type = resolve_deferred_semantic_type_impl(
                argument.value_type,
                loc,
                mode);
        }
    }
}

QualType Collect::resolve_deferred_template_specialization_type(
    TemplateSpecializationType& specialization,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    rewrite_deferred_template_arguments_in_place(
        specialization.arguments,
        loc,
        mode);
    query_publish_template_specialization_resolved_type(
        &specialization,
        nullptr);
    specialization.is_dependent = false;
    for (const auto& argument : specialization.arguments) {
        if (template_argument_depends_on_template_parameters(
                argument,
                ast_ctx_.get())) {
            specialization.is_dependent = true;
            break;
        }
    }
    auto resolved_type =
        query_lookup_template_specialization_resolved_type(&specialization);
    if (specialization.is_dependent || resolved_type) {
        return original_type;
    }

    auto* class_template =
        dyn_cast<ClassTemplateDecl>(specialization.primary_template);
    if (class_template) {
        auto* specialization_decl =
            mode == DeferredTypeResolutionMode::Finalize
                ? instantiate_class_template_specialization(
                      class_template,
                      specialization.arguments,
                      loc)
                : try_instantiate_class_template_specialization(
                      class_template,
                      specialization.arguments,
                      loc);
        if (specialization_decl && specialization_decl->get_record_type()) {
            query_publish_template_specialization_resolved_type(
                &specialization,
                QualType(specialization_decl->get_record_type()));
            return original_type;
        }
        return QualType();
    }

    auto* alias_template =
        dyn_cast<AliasTemplateDecl>(specialization.primary_template);
    if (!alias_template) {
        return original_type;
    }

    auto resolved_alias_type =
        mode == DeferredTypeResolutionMode::Finalize
            ? instantiate_alias_template_specialization(
                  alias_template,
                  specialization.arguments,
                  loc)
            : try_instantiate_alias_template_specialization(
                  alias_template,
                  specialization.arguments,
                  loc);
    resolved_alias_type =
        resolve_deferred_semantic_type_impl(resolved_alias_type, loc, mode);
    if (resolved_alias_type) {
        query_publish_template_specialization_resolved_type(
            &specialization,
            resolved_alias_type);
        return original_type;
    }
    return QualType();
}

QualType Collect::lookup_deferred_dependent_name_type(
    const DependentNameType& dependent_name,
    SrcLoc loc,
    bool* matched_nested_template) {
    bool has_template_argument_list =
        dependent_name.requires_template_keyword ||
        !dependent_name.template_arguments.empty();
    if (has_template_argument_list) {
        return collect_lookup_record_nested_template_type(
            dependent_name.qualifier_type,
            dependent_name.member_name,
            dependent_name.template_arguments,
            loc,
            matched_nested_template);
    }
    if (matched_nested_template) {
        *matched_nested_template = false;
    }
    return collect_lookup_record_nested_type(
        dependent_name.qualifier_type,
        dependent_name.member_name);
}

QualType Collect::handle_unresolved_dependent_name_type_lookup(
    const DependentNameType& dependent_name,
    QualType original_type,
    SrcLoc loc,
    bool matched_nested_template,
    DeferredTypeResolutionMode mode) const {
    if (type_depends_on_template_parameters(
            dependent_name.qualifier_type,
            ast_ctx_.get()) ||
        dependent_name.is_current_instantiation) {
        return original_type;
    }
    if (matched_nested_template) {
        return QualType();
    }
    if (mode == DeferredTypeResolutionMode::Finalize) {
        report_error(
            "'" + dependent_name.qualifier_type.to_string() + "::" +
                dependent_name.member_name +
                "' does not name a type",
            loc);
    }
    return QualType();
}

QualType Collect::resolve_deferred_dependent_name_type(
    DependentNameType& dependent_name,
    QualType original_type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    dependent_name.qualifier_type = resolve_deferred_semantic_type_impl(
        dependent_name.qualifier_type,
        loc,
        mode);
    rewrite_deferred_template_arguments_in_place(
        dependent_name.template_arguments,
        loc,
        mode);
    query_publish_dependent_name_resolved_type(&dependent_name, nullptr);
    auto resolved_type =
        query_lookup_dependent_name_resolved_type(&dependent_name);
    if (resolved_type) {
        auto rewritten_resolved_type =
            resolve_deferred_semantic_type_impl(
                resolved_type,
                loc,
                mode);
        query_publish_dependent_name_resolved_type(
            &dependent_name,
            rewritten_resolved_type);
        return original_type;
    }

    bool matched_nested_template = false;
    auto resolved_nested_type = lookup_deferred_dependent_name_type(
        dependent_name,
        loc,
        &matched_nested_template);
    if (!resolved_nested_type) {
        return handle_unresolved_dependent_name_type_lookup(
            dependent_name,
            original_type,
            loc,
            matched_nested_template,
            mode);
    }

    resolved_nested_type = resolve_deferred_semantic_type_impl(
        resolved_nested_type,
        loc,
        mode);
    query_publish_dependent_name_resolved_type(
        &dependent_name,
        resolved_nested_type);
    return original_type;
}

QualType Collect::try_realize_deferred_semantic_type(QualType type) {
    return resolve_deferred_semantic_type_impl(
        type,
        SrcLoc(),
        DeferredTypeResolutionMode::TryRealize);
}

QualType Collect::finalize_deferred_semantic_type(QualType type, SrcLoc loc) {
    return resolve_deferred_semantic_type_impl(
        type,
        loc,
        DeferredTypeResolutionMode::Finalize);
}

QualType Collect::resolve_deferred_semantic_type_impl(
    QualType type,
    SrcLoc loc,
    DeferredTypeResolutionMode mode) {
    if (!type) {
        return type;
    }

    auto raw = type.get_shared();
    if (!raw) {
        return type;
    }

    if (auto typedef_type = dyn_cast_shared<TypedefType>(raw)) {
        typedef_type->underlying_type = resolve_deferred_semantic_type_impl(
            typedef_type->underlying_type,
            loc,
            mode);
        if (!typedef_type->underlying_type) {
            return QualType();
        }
        return type;
    }

    if (auto* typeof_type = dyn_cast<TypeofExprType>(raw.get())) {
        auto expr_type = typeof_type->expr ? typeof_type->expr->get_type() : QualType();
        expr_type = resolve_deferred_semantic_type_impl(expr_type, loc, mode);
        if (!expr_type) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error("cannot determine type of expression in typeof", loc);
            }
            return QualType();
        }
        return QualType(
            expr_type.get_shared(),
            static_cast<uint8_t>(type.get_qualifiers() | expr_type.get_qualifiers()));
    }

    if (auto* decltype_type = dyn_cast<DecltypeExprType>(raw.get())) {
        return resolve_deferred_decltype_expr_type(
            *decltype_type,
            type,
            loc,
            mode);
    }

    if (auto* transform_type = dyn_cast<BuiltinTypeTransformType>(raw.get())) {
        auto operand_type = resolve_deferred_semantic_type_impl(
            transform_type->operand_type,
            loc,
            mode);
        if (!operand_type) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error(
                    "cannot determine operand type of builtin type transform",
                    loc);
            }
            return QualType();
        }

        transform_type->operand_type = operand_type;
        if (type_depends_on_template_parameters(operand_type, ast_ctx_.get())) {
            return type;
        }

        auto transformed =
            apply_builtin_type_transform(
                transform_type->transform_kind,
                operand_type,
                ast_ctx_.get());
        if (!transformed) {
            if (mode == DeferredTypeResolutionMode::Finalize) {
                report_error(
                    "cannot resolve builtin type transform",
                    loc);
            }
            return QualType();
        }
        return QualType(
            transformed.get_shared(),
            static_cast<uint8_t>(
                type.get_qualifiers() | transformed.get_qualifiers()));
    }

    if (auto specialization = dyn_cast_shared<TemplateSpecializationType>(raw)) {
        return resolve_deferred_template_specialization_type(
            *specialization,
            type,
            loc,
            mode);
    }

    if (auto dependent_name = dyn_cast_shared<DependentNameType>(raw)) {
        return resolve_deferred_dependent_name_type(
            *dependent_name,
            type,
            loc,
            mode);
    }

    if (auto ptr = dyn_cast_shared<PointerType>(raw)) {
        ptr->pointed_type = resolve_deferred_semantic_type_impl(
            ptr->pointed_type,
            loc,
            mode);
        return type;
    }
    if (auto ref = dyn_cast_shared<ReferenceType>(raw)) {
        ref->referred_type = resolve_deferred_semantic_type_impl(
            ref->referred_type,
            loc,
            mode);
        return type;
    }
    if (auto mem_ptr = dyn_cast_shared<MemberPointerType>(raw)) {
        mem_ptr->class_type = resolve_deferred_semantic_type_impl(
            mem_ptr->class_type,
            loc,
            mode);
        mem_ptr->member_type = resolve_deferred_semantic_type_impl(
            mem_ptr->member_type,
            loc,
            mode);
        return type;
    }
    if (auto blk = dyn_cast_shared<BlockPointerType>(raw)) {
        blk->pointed_type = resolve_deferred_semantic_type_impl(
            blk->pointed_type,
            loc,
            mode);
        return type;
    }
    if (auto arr = dyn_cast_shared<ArrayType>(raw)) {
        arr->element_type = resolve_deferred_semantic_type_impl(
            arr->element_type,
            loc,
            mode);
        return type;
    }
    if (auto func = dyn_cast_shared<FunctionType>(raw)) {
        func->ret_type = resolve_deferred_semantic_type_impl(
            func->ret_type,
            loc,
            mode);
        for (auto& parameter : func->parameters) {
            parameter = resolve_deferred_semantic_type_impl(parameter, loc, mode);
        }
        return type;
    }
    if (auto vec = dyn_cast_shared<VectorType>(raw)) {
        vec->element_type = resolve_deferred_semantic_type_impl(
            vec->element_type,
            loc,
            mode);
        return type;
    }

    return type;
}
