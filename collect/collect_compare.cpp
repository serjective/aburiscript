#include "collect.h"

#include <algorithm>
#include <string>
#include <utility>

namespace aburi::collect {

std::optional<Session::ComparisonCategory>
Session::resolve_comparison_category(ComparisonCategoryKind kind,
                                     SrcLoc loc,
                                     bool diagnose) {
    auto fail = [&](std::string_view detail)
        -> std::optional<ComparisonCategory> {
        if (diagnose) {
            report_error("built-in '<=>' requires " + std::string(detail) +
                             "; include <compare>",
                         loc);
        }
        return std::nullopt;
    };
    std::string_view category_name = "strong_ordering";
    if (kind == ComparisonCategoryKind::Weak) {
        category_name = "weak_ordering";
    } else if (kind == ComparisonCategoryKind::Partial) {
        category_name = "partial_ordering";
    }

    cir::DeclContextId root = resolve_qualifier_root().context;
    const cir::Binding* std_binding = file_.lookup_namespace_name_binding(
        root, "std", /*include_parents=*/false);
    if (!std_binding || std_binding->entities.empty()) {
        return fail("'std::" + std::string(category_name) + "'");
    }
    cir::EntityId std_namespace = std_binding->entities.back();
    if (!std_namespace.valid() || !file_.valid(std_namespace)) {
        return fail("'std::" + std::string(category_name) + "'");
    }
    cir::DeclContextId std_context =
        file_.entity(std_namespace).semantic_context;
    const cir::Binding* category_binding = file_.lookup_type_name_binding(
        std_context, category_name, /*include_parents=*/false);
    if (!category_binding) {
        category_binding = file_.lookup_tag_binding(
            std_context, category_name, /*include_parents=*/false);
    }
    if (!category_binding || category_binding->entities.empty()) {
        return fail("'std::" + std::string(category_name) + "'");
    }
    cir::EntityId category_entity = category_binding->entities.back();
    if (!category_entity.valid() || !file_.valid(category_entity) ||
        file_.entity(category_entity).kind != cir::EntityKind::Record) {
        return fail("'std::" + std::string(category_name) + "'");
    }
    cir::TypeId category_type =
        file_.resolved_type(file_.entity(category_entity).type);
    const cir::RecordFacts* facts = file_.record_facts(category_entity);
    if (!facts || facts->is_incomplete) {
        return fail("complete 'std::" + std::string(category_name) + "'");
    }

    auto member = [&](std::string_view name) -> cir::EntityId {
        for (const cir::RecordStaticDataMemberFact& candidate :
             facts->static_data_members) {
            if (!candidate.name.valid() || file_.name(candidate.name) != name) {
                continue;
            }
            if (file_.resolved_type(candidate.type.type) != category_type) {
                if (diagnose) {
                    report_error("'std::" + std::string(category_name) +
                                     "::" + std::string(name) +
                                     "' must have type 'std::" +
                                     std::string(category_name) + "'",
                                 loc);
                }
                return {};
            }
            return candidate.entity;
        }
        return {};
    };

    ComparisonCategory result;
    result.kind = kind;
    result.type = category_type;
    result.less = member("less");
    result.greater = member("greater");
    result.equivalent = member(kind == ComparisonCategoryKind::Strong
                                   ? "equal"
                                   : "equivalent");
    if (kind == ComparisonCategoryKind::Strong &&
        !result.equivalent.valid()) {
        result.equivalent = member("equivalent");
    }
    if (kind == ComparisonCategoryKind::Partial) {
        result.unordered = member("unordered");
    }
    if (!result.less.valid() || !result.equivalent.valid() ||
        !result.greater.valid() ||
        (kind == ComparisonCategoryKind::Partial &&
         !result.unordered.valid())) {
        return fail("the standard comparison-category result objects");
    }
    return result;
}

ExprResult Session::collect_builtin_three_way_compare(ExprResult lhs,
                                                       ExprResult rhs,
                                                       SrcLoc loc) {
    auto error = [&](std::string message) {
        report_error(std::move(message), loc);
        ExprResult result;
        result.type = builder_.unknown_type();
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    };
    if (!lang_opts_.is_cxx20_or_later()) {
        return error("operator '<=>' is only available in C++20 or later");
    }

    lhs = require_value(std::move(lhs), UseContext::RValue, loc);
    rhs = require_value(std::move(rhs), UseContext::RValue, loc);
    if (lhs.has_error || rhs.has_error) {
        return error("invalid operands to binary expression");
    }

    ComparisonCategoryKind category_kind = ComparisonCategoryKind::Strong;
    cir::TypeId computation_type{};
    bool lhs_pointer = is_pointer_type(lhs.type);
    bool rhs_pointer = is_pointer_type(rhs.type);
    bool lhs_nullptr = is_nullptr_type(lhs.type);
    bool rhs_nullptr = is_nullptr_type(rhs.type);
    bool lhs_scoped = is_scoped_enum_type(lhs.type);
    bool rhs_scoped = is_scoped_enum_type(rhs.type);

    if (lhs_pointer || rhs_pointer || lhs_nullptr || rhs_nullptr) {
        if (lhs_pointer && rhs_pointer) {
            if (!types_compatible(file_.type_ref(lhs.type),
                                  file_.type_ref(rhs.type))) {
                return error("comparison requires compatible pointer operands");
            }
            computation_type = lhs.type;
        } else if (lhs_pointer && rhs_nullptr) {
            computation_type = lhs.type;
        } else if (rhs_pointer && lhs_nullptr) {
            computation_type = rhs.type;
        } else if (lhs_nullptr && rhs_nullptr) {
            computation_type = lhs.type;
        } else {
            return error("comparison requires a pointer or null pointer operand");
        }
        lhs = convert_to(std::move(lhs), computation_type,
                         UseContext::RValue, loc);
        rhs = convert_to(std::move(rhs), computation_type,
                         UseContext::RValue, loc);
    } else if (lhs_scoped || rhs_scoped) {
        if (!lhs_scoped || !rhs_scoped ||
            file_.resolved_type(lhs.type) != file_.resolved_type(rhs.type)) {
            return error("invalid operands to binary expression involving scoped enum");
        }
        computation_type = lhs.type;
    } else if (is_arithmetic_type(lhs.type) &&
               is_arithmetic_type(rhs.type)) {
        computation_type =
            usual_arithmetic_conversion_type(lhs.type, rhs.type);
        if (!computation_type.valid()) {
            return error("invalid operands to binary expression");
        }
        category_kind = is_floating_type(computation_type)
            ? ComparisonCategoryKind::Partial
            : ComparisonCategoryKind::Strong;
        lhs = convert_to_arithmetic_type(std::move(lhs), computation_type, loc);
        rhs = convert_to_arithmetic_type(std::move(rhs), computation_type, loc);
    } else {
        return error("invalid operands to binary expression");
    }

    std::optional<ComparisonCategory> category =
        resolve_comparison_category(category_kind, loc);
    if (!category) {
        return error("comparison category is unavailable");
    }

    cir::Fragment fragment = chain(std::move(lhs.fragment),
                                   std::move(rhs.fragment), loc);
    fragment = adopt_or_create_fragment_entry(std::move(fragment),
                                              "expr.spaceship.operands");
    cir::BlockId less_check =
        builder_.create_detached_block("expr.spaceship.less");
    cir::BlockId greater_check =
        builder_.create_detached_block("expr.spaceship.greater");
    cir::BlockId equal_check = category_kind == ComparisonCategoryKind::Partial
        ? builder_.create_detached_block("expr.spaceship.equal")
        : cir::BlockId{};
    cir::BlockId less_result =
        builder_.create_detached_block("expr.spaceship.result.less");
    cir::BlockId equal_result =
        builder_.create_detached_block("expr.spaceship.result.equal");
    cir::BlockId greater_result =
        builder_.create_detached_block("expr.spaceship.result.greater");
    cir::BlockId unordered_result =
        category_kind == ComparisonCategoryKind::Partial
            ? builder_.create_detached_block("expr.spaceship.result.unordered")
            : cir::BlockId{};
    cir::BlockId merge =
        builder_.create_detached_block("expr.spaceship.end");
    cir::EntityId result_slot_entity = builder_.add_entity(
        cir::EntityKind::Variable,
        ".spaceship.result.tmp." +
            std::to_string(compound_literal_counter_++),
        category->type, {}, loc, cir::StorageDuration::Temporary);
    file_.entity_mut(result_slot_entity).is_definition = true;
    cir::BlockId slot_previous = builder_.current_block();
    builder_.switch_to_block(fragment.exit);
    cir::InstId result_slot = builder_.local_place(
        result_slot_entity, category->type, loc);
    builder_.switch_to_block(slot_previous);

    builder_.branch_from(fragment.exit, less_check, {}, loc);
    auto append = [&](cir::BlockId block) {
        cir::Fragment part = builder_.block_fragment(block);
        fragment.blocks.insert(fragment.blocks.end(), part.blocks.begin(),
                               part.blocks.end());
    };
    cir::BlockId previous = builder_.current_block();
    builder_.switch_to_block(less_check);
    cir::InstId is_less = builder_.binary(cir::BinaryOpKind::Less,
                                          builder_.bool_type(),
                                          lhs.value, rhs.value, loc);
    builder_.cond_branch_from(less_check, is_less, less_result,
                              greater_check, {}, loc);
    append(less_check);

    builder_.switch_to_block(greater_check);
    cir::InstId is_greater = builder_.binary(cir::BinaryOpKind::Greater,
                                             builder_.bool_type(),
                                             lhs.value, rhs.value, loc);
    builder_.cond_branch_from(
        greater_check, is_greater, greater_result,
        category_kind == ComparisonCategoryKind::Partial
            ? equal_check
            : equal_result,
        {}, loc);
    append(greater_check);

    if (equal_check.valid()) {
        builder_.switch_to_block(equal_check);
        cir::InstId is_equal = builder_.binary(cir::BinaryOpKind::Equal,
                                               builder_.bool_type(),
                                               lhs.value, rhs.value, loc);
        builder_.cond_branch_from(equal_check, is_equal, equal_result,
                                  unordered_result, {}, loc);
        append(equal_check);
    }

    auto emit_result = [&](cir::BlockId block, cir::EntityId entity) {
        builder_.switch_to_block(block);
        cir::InstId place = builder_.global_place(entity, loc);
        cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
        builder_.store(result_slot, value, loc);
        builder_.branch_from(block, merge, {}, loc);
        append(block);
    };
    emit_result(less_result, category->less);
    emit_result(equal_result, category->equivalent);
    emit_result(greater_result, category->greater);
    if (unordered_result.valid()) {
        emit_result(unordered_result, category->unordered);
    }
    builder_.switch_to_block(merge);
    cir::InstId merged = builder_.lvalue_to_rvalue(result_slot, loc);
    append(merge);
    builder_.switch_to_block(previous);
    fragment.exit = merge;
    fragment.falls_through = true;

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = merged;
    result.type = category->type;
    result.category = ValueCategory::PrValue;
    result.references_template_value_parameter =
        lhs.references_template_value_parameter ||
        rhs.references_template_value_parameter;
    result.value_dependent = expr_is_value_dependent(lhs) ||
                             expr_is_value_dependent(rhs);
    result.has_error = lhs.has_error || rhs.has_error;
    return result;
}

ExprResult Session::collect_synthesized_three_way_compare(
    ExprResult lhs,
    ExprResult rhs,
    const ComparisonCategory& result_category,
    bool allow_fallback,
    SrcLoc loc) {
    if (!allow_fallback) {
        ExprResult direct = collect_binary_expr(
            syntax::BinaryOperator::ThreeWay, std::move(lhs),
            std::move(rhs), loc);
        return convert_to(std::move(direct), result_category.type,
                          UseContext::RValue, loc);
    }

    cir::BlockId saved_block = builder_.current_block();
    cir::File::TransactionId direct_trial = file_.begin_transaction();
    ExprResult direct = collect_binary_expr(
        syntax::BinaryOperator::ThreeWay, lhs, rhs, loc);
    direct = convert_to(std::move(direct), result_category.type,
                        UseContext::RValue, loc);
    if (!direct.has_error) {
        file_.commit_transaction(direct_trial);
        return direct;
    }
    file_.rollback_transaction(direct_trial);
    builder_.switch_to_block(saved_block);

    ExprResult equality_lhs = lhs;
    ExprResult equality_rhs = rhs;
    ExprResult equality = collect_binary_expr(
        syntax::BinaryOperator::Equal, std::move(equality_lhs),
        std::move(equality_rhs), loc);
    equality = convert_to_condition(std::move(equality), loc);

    lhs.fragment = {};
    rhs.fragment = {};
    ExprResult less = collect_binary_expr(
        syntax::BinaryOperator::Less, lhs, rhs, loc);
    less = convert_to_condition(std::move(less), loc);
    ExprResult greater;
    if (result_category.kind == ComparisonCategoryKind::Partial) {
        greater = collect_binary_expr(
            syntax::BinaryOperator::Less, rhs, lhs, loc);
        greater = convert_to_condition(std::move(greater), loc);
    }

    cir::Fragment fragment = adopt_or_create_fragment_entry(
        std::move(equality.fragment), "compare.synthesized.equal");
    auto append_fragment = [&](const cir::Fragment& part) {
        fragment.blocks.insert(fragment.blocks.end(), part.blocks.begin(),
                               part.blocks.end());
    };
    less.fragment = adopt_or_create_fragment_entry(
        std::move(less.fragment), "compare.synthesized.less");
    if (result_category.kind == ComparisonCategoryKind::Partial) {
        greater.fragment = adopt_or_create_fragment_entry(
            std::move(greater.fragment), "compare.synthesized.greater");
    }

    cir::BlockId equal_result = builder_.create_detached_block(
        "compare.synthesized.result.equal");
    cir::BlockId less_result = builder_.create_detached_block(
        "compare.synthesized.result.less");
    cir::BlockId greater_result = builder_.create_detached_block(
        "compare.synthesized.result.greater");
    cir::BlockId unordered_result =
        result_category.kind == ComparisonCategoryKind::Partial
            ? builder_.create_detached_block(
                  "compare.synthesized.result.unordered")
            : cir::BlockId{};
    cir::BlockId merge = builder_.create_detached_block(
        "compare.synthesized.end");
    cir::EntityId result_entity = builder_.add_entity(
        cir::EntityKind::Variable,
        ".synthesized.spaceship.result.tmp." +
            std::to_string(compound_literal_counter_++),
        result_category.type, {}, loc, cir::StorageDuration::Temporary);
    file_.entity_mut(result_entity).is_definition = true;
    cir::BlockId slot_previous = builder_.current_block();
    builder_.switch_to_block(fragment.exit);
    cir::InstId result_slot = builder_.local_place(
        result_entity, result_category.type, loc);
    builder_.switch_to_block(slot_previous);

    builder_.cond_branch_from(fragment.exit, equality.value,
                              equal_result, less.fragment.entry, {}, loc);
    append_fragment(less.fragment);
    if (result_category.kind == ComparisonCategoryKind::Partial) {
        builder_.cond_branch_from(less.fragment.exit, less.value,
                                  less_result, greater.fragment.entry, {},
                                  loc);
        append_fragment(greater.fragment);
        builder_.cond_branch_from(greater.fragment.exit, greater.value,
                                  greater_result, unordered_result, {}, loc);
    } else {
        builder_.cond_branch_from(less.fragment.exit, less.value,
                                  less_result, greater_result, {}, loc);
    }

    auto append = [&](cir::BlockId block) {
        append_fragment(builder_.block_fragment(block));
    };
    auto emit_result = [&](cir::BlockId block, cir::EntityId entity) {
        builder_.switch_to_block(block);
        cir::InstId place = builder_.global_place(entity, loc);
        cir::InstId value = builder_.lvalue_to_rvalue(place, loc);
        builder_.store(result_slot, value, loc);
        builder_.branch(merge, {}, loc);
        append(block);
    };
    emit_result(equal_result, result_category.equivalent);
    emit_result(less_result, result_category.less);
    emit_result(greater_result, result_category.greater);
    if (unordered_result.valid()) {
        emit_result(unordered_result, result_category.unordered);
    }
    builder_.switch_to_block(merge);
    cir::InstId result_value =
        builder_.lvalue_to_rvalue(result_slot, loc);
    append(merge);
    builder_.switch_to_block(saved_block);
    fragment.exit = merge;
    fragment.falls_through = true;

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = result_value;
    result.type = result_category.type;
    result.category = ValueCategory::PrValue;
    result.has_error = equality.has_error || less.has_error ||
        greater.has_error;
    return result;
}

ExprResult Session::collect_defaulted_array_equality(cir::InstId lhs_place,
                                                      cir::InstId rhs_place,
                                                      cir::TypeId array_type,
                                                      SrcLoc loc) {
    cir::TypeId current = file_.resolved_type(array_type);
    cir::TypeId leaf{};
    size_t total = 1;
    bool valid_shape = false;
    while (file_.valid(current) &&
           file_.type(current).kind == cir::TypeKind::Array) {
        const auto* payload = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(current));
        if (!payload || !payload->size.has_value() ||
            payload->size_expr_is_dependent) {
            valid_shape = false;
            break;
        }
        valid_shape = true;
        total *= *payload->size;
        current = file_.resolved_type(payload->element_type.type);
    }
    leaf = current;
    if (!valid_shape || !leaf.valid()) {
        report_error("defaulted comparison requires a constant-extent array",
                     loc);
        ExprResult result;
        result.type = builder_.bool_type();
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }
    if (total == 0) {
        return make_boolean_literal(true, "true", loc);
    }

    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved = builder_.current_block();
    cir::BlockId entry =
        builder_.create_detached_block("compare.array.entry");
    cir::BlockId head = builder_.create_detached_block("compare.array.head");
    cir::BlockId body = builder_.create_detached_block("compare.array.body");
    cir::BlockId next = builder_.create_detached_block("compare.array.next");
    cir::BlockId true_block =
        builder_.create_detached_block("compare.array.true");
    cir::BlockId false_block =
        builder_.create_detached_block("compare.array.false");
    cir::BlockId done = builder_.create_detached_block("compare.array.done");
    cir::InstId index =
        builder_.add_block_parameter(head, usize, "compare.index", loc);
    cir::InstId result_value =
        builder_.add_block_parameter(done, builder_.bool_type(),
                                     "compare.array.result", loc);

    builder_.switch_to_block(entry);
    cir::InstId lhs_flat =
        flatten_array_place(lhs_place, array_type, leaf, total, loc);
    cir::InstId rhs_flat =
        flatten_array_place(rhs_place, array_type, leaf, total, loc);
    cir::InstId zero = builder_.integer_literal(0, usize, "0", loc);
    builder_.branch(head, {zero}, loc);

    builder_.switch_to_block(head);
    cir::InstId extent = builder_.integer_literal(
        static_cast<int64_t>(total), usize, std::to_string(total), loc);
    cir::InstId at_end = builder_.binary(cir::BinaryOpKind::Equal,
                                         builder_.bool_type(), index,
                                         extent, loc);
    builder_.cond_branch_from(head, at_end, true_block, body, {}, loc);

    builder_.switch_to_block(body);
    cir::InstId lhs_element =
        builder_.array_element_place(lhs_flat, index, loc);
    cir::InstId rhs_element =
        builder_.array_element_place(rhs_flat, index, loc);
    ExprResult lhs_expr;
    lhs_expr.place = lhs_element;
    lhs_expr.type = leaf;
    lhs_expr.category = ValueCategory::LValue;
    ExprResult rhs_expr;
    rhs_expr.place = rhs_element;
    rhs_expr.type = leaf;
    rhs_expr.category = ValueCategory::LValue;
    ExprResult equal = collect_binary_expr(syntax::BinaryOperator::Equal,
                                           std::move(lhs_expr),
                                           std::move(rhs_expr), loc);
    equal = convert_to_condition(std::move(equal), loc);
    if (equal.fragment.empty()) {
        builder_.cond_branch_from(body, equal.value, next, false_block, {},
                                  loc);
    } else {
        builder_.branch_from(body, equal.fragment.entry, {}, loc);
        builder_.cond_branch_from(equal.fragment.exit, equal.value, next,
                                  false_block, {}, loc);
    }

    builder_.switch_to_block(next);
    cir::InstId one = builder_.integer_literal(1, usize, "1", loc);
    cir::InstId advanced = builder_.binary(cir::BinaryOpKind::Add, usize,
                                           index, one, loc);
    builder_.branch(head, {advanced}, loc);

    builder_.switch_to_block(true_block);
    cir::InstId yes = builder_.boolean_literal(true, "true", loc);
    builder_.branch(done, {yes}, loc);
    builder_.switch_to_block(false_block);
    cir::InstId no = builder_.boolean_literal(false, "false", loc);
    builder_.branch(done, {no}, loc);

    cir::Fragment fragment;
    fragment.blocks = {entry, head, body};
    fragment.blocks.insert(fragment.blocks.end(), equal.fragment.blocks.begin(),
                           equal.fragment.blocks.end());
    fragment.blocks.push_back(next);
    fragment.blocks.push_back(true_block);
    fragment.blocks.push_back(false_block);
    fragment.blocks.push_back(done);
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;
    builder_.switch_to_block(saved);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = result_value;
    result.type = builder_.bool_type();
    result.category = ValueCategory::PrValue;
    result.has_error = equal.has_error;
    return result;
}

ExprResult Session::collect_defaulted_array_three_way(
    cir::InstId lhs_place,
    cir::InstId rhs_place,
    cir::TypeId array_type,
    const ComparisonCategory& result_category,
    bool allow_fallback,
    SrcLoc loc) {
    cir::TypeId current = file_.resolved_type(array_type);
    cir::TypeId leaf{};
    size_t total = 1;
    bool valid_shape = false;
    while (file_.valid(current) &&
           file_.type(current).kind == cir::TypeKind::Array) {
        const auto* payload = std::get_if<cir::ArrayTypePayload>(
            &file_.type_payload(current));
        if (!payload || !payload->size.has_value() ||
            payload->size_expr_is_dependent) {
            valid_shape = false;
            break;
        }
        valid_shape = true;
        total *= *payload->size;
        current = file_.resolved_type(payload->element_type.type);
    }
    leaf = current;
    if (!valid_shape || !leaf.valid()) {
        report_error("defaulted comparison requires a constant-extent array",
                     loc);
        ExprResult result;
        result.type = result_category.type;
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }

    cir::TypeId usize = builder_.usize_type();
    cir::BlockId saved = builder_.current_block();
    cir::BlockId entry =
        builder_.create_detached_block("compare.array.three_way.entry");
    cir::BlockId head =
        builder_.create_detached_block("compare.array.three_way.head");
    cir::BlockId body =
        builder_.create_detached_block("compare.array.three_way.body");
    cir::BlockId next =
        builder_.create_detached_block("compare.array.three_way.next");
    cir::BlockId nonzero =
        builder_.create_detached_block("compare.array.three_way.nonzero");
    cir::BlockId equivalent =
        builder_.create_detached_block("compare.array.three_way.equivalent");
    cir::BlockId done =
        builder_.create_detached_block("compare.array.three_way.done");
    cir::InstId index = builder_.add_block_parameter(
        head, usize, "compare.index", loc);

    builder_.switch_to_block(entry);
    cir::EntityId result_slot_entity = builder_.add_entity(
        cir::EntityKind::Variable,
        ".array.spaceship.result.tmp." +
            std::to_string(compound_literal_counter_++),
        result_category.type, {}, loc, cir::StorageDuration::Temporary);
    file_.entity_mut(result_slot_entity).is_definition = true;
    cir::InstId result_slot = builder_.local_place(
        result_slot_entity, result_category.type, loc);
    cir::InstId lhs_flat =
        flatten_array_place(lhs_place, array_type, leaf, total, loc);
    cir::InstId rhs_flat =
        flatten_array_place(rhs_place, array_type, leaf, total, loc);
    cir::InstId zero_index = builder_.integer_literal(0, usize, "0", loc);
    builder_.branch(head, {zero_index}, loc);

    builder_.switch_to_block(head);
    cir::InstId extent = builder_.integer_literal(
        static_cast<int64_t>(total), usize, std::to_string(total), loc);
    cir::InstId at_end = builder_.binary(cir::BinaryOpKind::Equal,
                                         builder_.bool_type(), index,
                                         extent, loc);
    builder_.cond_branch_from(head, at_end, equivalent, body, {}, loc);

    builder_.switch_to_block(body);
    cir::InstId lhs_element =
        builder_.array_element_place(lhs_flat, index, loc);
    cir::InstId rhs_element =
        builder_.array_element_place(rhs_flat, index, loc);
    ExprResult lhs_expr;
    lhs_expr.place = lhs_element;
    lhs_expr.type = leaf;
    lhs_expr.category = ValueCategory::LValue;
    ExprResult rhs_expr;
    rhs_expr.place = rhs_element;
    rhs_expr.type = leaf;
    rhs_expr.category = ValueCategory::LValue;
    ExprResult compared = collect_synthesized_three_way_compare(
        std::move(lhs_expr), std::move(rhs_expr), result_category,
        allow_fallback, loc);
    cir::InstId compared_value = compared.value;
    ExprResult zero = make_integer_literal(0, "0", loc);
    ExprResult is_nonzero = collect_binary_expr(
        syntax::BinaryOperator::NotEqual, std::move(compared),
        std::move(zero), loc);
    is_nonzero = convert_to_condition(std::move(is_nonzero), loc);
    if (is_nonzero.fragment.empty()) {
        builder_.cond_branch_from(body, is_nonzero.value, nonzero, next, {},
                                  loc);
    } else {
        builder_.branch_from(body, is_nonzero.fragment.entry, {}, loc);
        builder_.cond_branch_from(is_nonzero.fragment.exit, is_nonzero.value,
                                  nonzero, next, {}, loc);
    }

    builder_.switch_to_block(next);
    cir::InstId one = builder_.integer_literal(1, usize, "1", loc);
    cir::InstId advanced = builder_.binary(cir::BinaryOpKind::Add, usize,
                                           index, one, loc);
    builder_.branch(head, {advanced}, loc);

    builder_.switch_to_block(nonzero);
    builder_.store(result_slot, compared_value, loc);
    builder_.branch(done, {}, loc);
    builder_.switch_to_block(equivalent);
    cir::InstId equivalent_place =
        builder_.global_place(result_category.equivalent, loc);
    cir::InstId equivalent_value =
        builder_.lvalue_to_rvalue(equivalent_place, loc);
    builder_.store(result_slot, equivalent_value, loc);
    builder_.branch(done, {}, loc);

    builder_.switch_to_block(done);
    cir::InstId result_value =
        builder_.lvalue_to_rvalue(result_slot, loc);

    cir::Fragment fragment;
    fragment.blocks = {entry, head, body};
    fragment.blocks.insert(fragment.blocks.end(),
                           is_nonzero.fragment.blocks.begin(),
                           is_nonzero.fragment.blocks.end());
    fragment.blocks.push_back(next);
    fragment.blocks.push_back(nonzero);
    fragment.blocks.push_back(equivalent);
    fragment.blocks.push_back(done);
    fragment.entry = entry;
    fragment.exit = done;
    fragment.falls_through = true;
    builder_.switch_to_block(saved);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = result_value;
    result.type = result_category.type;
    result.category = ValueCategory::PrValue;
    result.has_error = compared.has_error || is_nonzero.has_error;
    return result;
}

bool Session::defaulted_comparison_function_potentially_throws(
    cir::FunctionId function) {
    if (!function.valid() || !file_.valid(function)) {
        return true;
    }
    ExprResult implicit_definition;
    implicit_definition.fragment.blocks = file_.function(function).blocks;
    return expression_potentially_throws(implicit_definition);
}

void Session::publish_defaulted_comparison_properties(
    cir::EntityId function,
    bool implicitly_constexpr,
    bool compute_implicit_exception_spec,
    bool potentially_throwing) {
    if (!function.valid() || !file_.valid(function)) {
        return;
    }

    if (implicitly_constexpr) {
        file_.entity_mut(function).decl_flags.is_constexpr = true;
        if (cir::RecordMethodFact* method =
                file_.method_fact_mut(function)) {
            method->is_constexpr = true;
        }
    }

    if (compute_implicit_exception_spec) {
        cir::FunctionExceptionSpec specification(
            potentially_throwing
                ? cir::FunctionExceptionSpecKind::PotentiallyThrowing
                : cir::FunctionExceptionSpecKind::NonThrowing);
        if (file_.method_fact(function)) {
            resolve_record_method_noexcept(function, specification);
            if (cir::RecordMethodFact* method =
                    file_.method_fact_mut(function)) {
                method->has_computed_exception_spec = true;
            }
        } else {
            const auto* old_type = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(
                    file_.resolved_type(file_.entity(function).type)));
            if (old_type) {
                cir::FunctionTypePayload rebuilt = *old_type;
                rebuilt.exception_spec = specification;
                file_.entity_mut(function).type = function_type(
                    rebuilt.return_type, rebuilt.parameters,
                    rebuilt.is_variadic, rebuilt.has_prototype,
                    rebuilt.member_is_const, rebuilt.exception_spec,
                    rebuilt.parameter_pack_flags,
                    rebuilt.member_ref_qualifier,
                    rebuilt.member_is_volatile);
            }
        }
    }

    if (cir::DefaultedComparisonFact* plan =
            file_.defaulted_comparison_fact_mut(function)) {
        plan->is_constexpr = file_.entity(function).decl_flags.is_constexpr;
        if (compute_implicit_exception_spec) {
            plan->is_noexcept = !potentially_throwing;
        }
    }
    for (cir::FunctionId function_id : file_.function_ids()) {
        if (file_.function(function_id).entity == function) {
            file_.function_mut(function_id).type =
                file_.entity(function).type;
        }
    }
}

void Session::plan_and_synthesize_defaulted_comparisons(
    cir::EntityId record,
    bool synthesize_bodies,
    SrcLoc loc) {
    const cir::RecordFacts* facts = file_.record_facts(record);
    if (!facts) {
        return;
    }
    std::vector<cir::RecordMethodFact> methods = facts->methods;
    for (const cir::RecordMethodFact& method : methods) {
        if (!method.is_defaulted || !method.name.valid() ||
            !method.entity.valid()) {
            continue;
        }
        std::string_view name = file_.name(method.name);
        cir::DefaultedComparisonKind kind;
        if (name == "operator==") {
            kind = cir::DefaultedComparisonKind::Equal;
        } else if (name == "operator!=") {
            kind = cir::DefaultedComparisonKind::NotEqual;
        } else if (name == "operator<") {
            kind = cir::DefaultedComparisonKind::Less;
        } else if (name == "operator<=") {
            kind = cir::DefaultedComparisonKind::LessEqual;
        } else if (name == "operator>") {
            kind = cir::DefaultedComparisonKind::Greater;
        } else if (name == "operator>=") {
            kind = cir::DefaultedComparisonKind::GreaterEqual;
        } else if (name == "operator<=>") {
            kind = cir::DefaultedComparisonKind::ThreeWay;
        } else {
            continue;
        }

        cir::DefaultedComparisonFact plan;
        plan.function = method.entity;
        plan.owner_record = record;
        plan.kind = kind;
        plan.is_deleted = method.is_deleted;
        plan.is_constexpr = method.is_constexpr;
        plan.is_implicit_equality = method.is_implicitly_declared;
        plan.implicit_equality_origin = method.implicit_equality_origin;
        plan.is_dependent = !synthesize_bodies;
        const auto* function = std::get_if<cir::FunctionTypePayload>(
            &file_.type_payload(file_.resolved_type(method.type.type)));
        if (function) {
            plan.result_type = function->return_type;
            plan.is_noexcept = function->exception_spec.kind ==
                cir::FunctionExceptionSpecKind::NonThrowing;
        }

        std::vector<cir::EntityId> used_base_fields;
        std::vector<const cir::RecordBaseFact*> direct_bases;
        for (const cir::RecordBaseFact& base : facts->bases) {
            direct_bases.push_back(&base);
        }
        std::stable_sort(
            direct_bases.begin(), direct_bases.end(),
            [](const cir::RecordBaseFact* lhs,
               const cir::RecordBaseFact* rhs) {
                return lhs->declaration_index < rhs->declaration_index;
            });
        for (const cir::RecordBaseFact* base : direct_bases) {
            cir::EntityId storage{};
            if (base->is_virtual) {
                for (const cir::RecordFacts::VirtualBase& candidate :
                     facts->virtual_bases) {
                    if (candidate.record_entity == base->record_entity) {
                        storage = candidate.storage_field;
                        break;
                    }
                }
            } else {
                for (const cir::RecordFieldFact& candidate : facts->fields) {
                    if (candidate.is_base_subobject &&
                        !candidate.is_virtual_base_storage &&
                        file_.resolved_type(candidate.type.type) ==
                            file_.resolved_type(base->type.type) &&
                        std::find(used_base_fields.begin(),
                                  used_base_fields.end(), candidate.entity) ==
                            used_base_fields.end()) {
                        storage = candidate.entity;
                        break;
                    }
                }
            }
            if (!storage.valid()) {
                plan.is_deleted = true;
                plan.deletion_reason =
                    "comparison base subobject storage is unavailable";
                continue;
            }
            used_base_fields.push_back(storage);
            cir::ComparisonSubobjectFact subobject;
            subobject.kind = cir::ComparisonSubobjectKind::DirectBase;
            subobject.entity = storage;
            subobject.type = base->type;
            plan.subobjects.push_back(std::move(subobject));
        }
        for (const cir::RecordFieldFact& field : facts->fields) {
            if (field.is_base_subobject ||
                (field.name.valid() && file_.name(field.name) == ".vptr")) {
                continue;
            }
            cir::ComparisonSubobjectFact subobject;
            subobject.kind = cir::ComparisonSubobjectKind::Field;
            subobject.entity = field.entity;
            subobject.type = field.type;
            cir::TypeId current = file_.resolved_type(field.type.type);
            size_t total = 1;
            while (file_.valid(current) &&
                   file_.type(current).kind == cir::TypeKind::Array) {
                const auto* array = std::get_if<cir::ArrayTypePayload>(
                    &file_.type_payload(current));
                if (!array || !array->size.has_value() ||
                    array->size_expr_is_dependent) {
                    plan.is_dependent = true;
                    break;
                }
                subobject.array_extents.push_back(*array->size);
                total *= *array->size;
                current = file_.resolved_type(array->element_type.type);
            }
            if (!subobject.array_extents.empty()) {
                subobject.array_leaf_type = file_.type_ref(current);
                subobject.array_element_count = total;
            }
            plan.subobjects.push_back(std::move(subobject));
        }

        std::optional<ComparisonCategory> three_way_category;
        bool three_way_result_was_deduced = false;
        if (kind == cir::DefaultedComparisonKind::ThreeWay && function) {
            const bool deduced_result =
                function_has_placeholder_return(method.type.type);
            three_way_result_was_deduced = deduced_result;
            if (deduced_result && !synthesize_bodies) {
                plan.is_dependent = true;
                file_.set_defaulted_comparison_fact(method.entity,
                                                     std::move(plan));
                publish_defaulted_comparison_properties(
                    method.entity, !method.is_user_provided,
                    /*compute_implicit_exception_spec=*/false,
                    /*potentially_throwing=*/true);
                continue;
            }
            std::vector<cir::TypeId> component_results;
            bool probe_failed = false;

            if (deduced_result && !plan.subobjects.empty() &&
                synthesize_bodies) {
                cir::File::TransactionId probe = file_.begin_transaction();
                std::unique_ptr<BlockContextState> saved =
                    save_function_context();
                ParamInput other;
                other.name = ".comparison.other";
                other.type = function->parameters.front();
                other.loc = loc;
                FunctionDeclStart start = begin_member_function(
                    method.entity, {other}, loc, true);
                probe_failed = start.decl.has_error ||
                    start.function.parameters.size() < 2;
                std::optional<ExprResult> first_result;
                if (!probe_failed) {
                    cir::BlockId function_block = builder_.current_block();
                    cir::BlockId object_block =
                        begin_fragment_block("compare.defaulted.probe.objects");
                    cir::InstId this_pointer =
                        builder_.lvalue_to_rvalue(current_this_place_, loc);
                    cir::InstId lhs_object = builder_.deref(this_pointer, loc);
                    cir::InstId rhs_object = builder_.deref(
                        start.function.parameters[1].value.inst, loc);
                    cir::Fragment object_fragment = finish_fragment_block(
                        object_block, function_block);

                    for (const cir::ComparisonSubobjectFact& subobject :
                         plan.subobjects) {
                        if (!subobject.array_extents.empty() &&
                            subobject.array_element_count == 0) {
                            continue;
                        }
                        cir::BlockId address_block = begin_fragment_block(
                            "compare.defaulted.probe.subobject");
                        cir::InstId lhs_place = builder_.field_addr(
                            lhs_object, subobject.entity,
                            subobject.type.type, loc);
                        cir::InstId rhs_place = builder_.field_addr(
                            rhs_object, subobject.entity,
                            subobject.type.type, loc);
                        cir::TypeId operand_type = subobject.type.type;
                        if (!subobject.array_extents.empty()) {
                            cir::TypeId leaf =
                                subobject.array_leaf_type.type;
                            lhs_place = builder_.array_element_place(
                                flatten_array_place(
                                    lhs_place, subobject.type.type, leaf,
                                    subobject.array_element_count, loc),
                                builder_.integer_literal(
                                    0, builder_.usize_type(), "0", loc),
                                loc);
                            rhs_place = builder_.array_element_place(
                                flatten_array_place(
                                    rhs_place, subobject.type.type, leaf,
                                    subobject.array_element_count, loc),
                                builder_.integer_literal(
                                    0, builder_.usize_type(), "0", loc),
                                loc);
                            operand_type = leaf;
                        }
                        cir::Fragment address_fragment =
                            finish_fragment_block(address_block,
                                                  function_block);
                        ExprResult lhs_expr;
                        lhs_expr.fragment = std::move(address_fragment);
                        lhs_expr.place = lhs_place;
                        lhs_expr.type = operand_type;
                        lhs_expr.category = ValueCategory::LValue;
                        ExprResult rhs_expr;
                        rhs_expr.place = rhs_place;
                        rhs_expr.type = operand_type;
                        rhs_expr.category = ValueCategory::LValue;
                        ExprResult compared = collect_binary_expr(
                            syntax::BinaryOperator::ThreeWay,
                            std::move(lhs_expr), std::move(rhs_expr), loc);
                        probe_failed = probe_failed || compared.has_error ||
                            !compared.type.valid();
                        component_results.push_back(
                            file_.resolved_type(compared.type));
                        if (!first_result.has_value()) {
                            compared.fragment = chain(
                                std::move(object_fragment),
                                std::move(compared.fragment), loc);
                            first_result = std::move(compared);
                        }
                    }
                    StmtResult terminal;
                    if (first_result.has_value()) {
                        terminal = collect_return_stmt(
                            std::move(*first_result), loc);
                    }
                    finish_member_function(std::move(terminal), loc);
                }
                restore_function_context(std::move(saved));
                file_.rollback_transaction(probe);
            }

            std::optional<ComparisonCategory> strong =
                resolve_comparison_category(
                    ComparisonCategoryKind::Strong, loc,
                    /*diagnose=*/false);
            std::optional<ComparisonCategory> weak =
                resolve_comparison_category(
                    ComparisonCategoryKind::Weak, loc,
                    /*diagnose=*/false);
            std::optional<ComparisonCategory> partial =
                resolve_comparison_category(
                    ComparisonCategoryKind::Partial, loc,
                    /*diagnose=*/false);
            auto category_for_type = [&](cir::TypeId type)
                -> std::optional<ComparisonCategory> {
                type = file_.resolved_type(type);
                if (strong && file_.resolved_type(strong->type) == type) {
                    return strong;
                }
                if (weak && file_.resolved_type(weak->type) == type) {
                    return weak;
                }
                if (partial && file_.resolved_type(partial->type) == type) {
                    return partial;
                }
                return std::nullopt;
            };

            if (deduced_result) {
                ComparisonCategoryKind common =
                    ComparisonCategoryKind::Strong;
                for (cir::TypeId component : component_results) {
                    std::optional<ComparisonCategory> category =
                        category_for_type(component);
                    if (!category) {
                        probe_failed = true;
                        break;
                    }
                    if (category->kind == ComparisonCategoryKind::Partial) {
                        common = ComparisonCategoryKind::Partial;
                    } else if (category->kind ==
                                   ComparisonCategoryKind::Weak &&
                               common == ComparisonCategoryKind::Strong) {
                        common = ComparisonCategoryKind::Weak;
                    }
                }
                if (!probe_failed) {
                    if (common == ComparisonCategoryKind::Strong) {
                        three_way_category = strong;
                    } else if (common == ComparisonCategoryKind::Weak) {
                        three_way_category = weak;
                    } else {
                        three_way_category = partial;
                    }
                }
                if (three_way_category) {
                    cir::PlaceholderResultFactId placeholder =
                        file_.entity(method.entity).placeholder_result;
                    publish_placeholder_result(
                        placeholder,
                        file_.type_ref(three_way_category->type), loc,
                        /*final=*/true);
                    plan.result_type =
                        file_.type_ref(three_way_category->type);
                }
            } else {
                three_way_category = category_for_type(
                    function->return_type.type);
            }
            if (!three_way_category) {
                plan.is_deleted = true;
                plan.deletion_reason = deduced_result
                    ? "expanded subobject comparisons do not have a common "
                      "comparison category"
                    : "the declared result is not a standard comparison "
                      "category type";
            }
        }
        file_.set_defaulted_comparison_fact(method.entity, plan);
        const bool implicitly_constexpr = !method.is_user_provided;
        publish_defaulted_comparison_properties(
            method.entity, implicitly_constexpr,
            /*compute_implicit_exception_spec=*/false,
            /*potentially_throwing=*/true);
        if (plan.is_deleted) {
            if (cir::RecordMethodFact* mutable_method =
                    file_.method_fact_mut(method.entity)) {
                mutable_method->is_deleted = true;
            }
            continue;
        }

        const cir::RecordMethodFact* published_method =
            file_.method_fact(method.entity);
        if (published_method) {
            function = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(
                    file_.resolved_type(published_method->type.type)));
        }
        if (synthesize_bodies &&
            kind == cir::DefaultedComparisonKind::ThreeWay && function &&
            !function->parameters.empty() && three_way_category) {
            size_t errors_before = file_.errors().size();
            cir::File::TransactionId transaction = file_.begin_transaction();
            std::unique_ptr<BlockContextState> saved = save_function_context();
            ParamInput other;
            other.name = ".comparison.other";
            other.type = function->parameters.front();
            other.loc = loc;
            FunctionDeclStart start =
                begin_member_function(method.entity, {other}, loc, true);
            bool failed = start.decl.has_error ||
                start.function.parameters.size() < 2;
            if (!failed) {
                cir::BlockId function_block = builder_.current_block();
                cir::BlockId object_block =
                    begin_fragment_block("compare.defaulted.objects");
                cir::InstId this_pointer =
                    builder_.lvalue_to_rvalue(current_this_place_, loc);
                cir::InstId lhs_object = builder_.deref(this_pointer, loc);
                cir::InstId rhs_object = builder_.deref(
                    start.function.parameters[1].value.inst, loc);
                cir::Fragment object_fragment = finish_fragment_block(
                    object_block, function_block);

                struct ComparisonStep {
                    ExprResult nonzero;
                    StmtResult returned;
                };
                std::vector<ComparisonStep> steps;
                for (const cir::ComparisonSubobjectFact& subobject :
                     plan.subobjects) {
                    if (!subobject.array_extents.empty() &&
                        subobject.array_element_count == 0) {
                        continue;
                    }
                    cir::BlockId address_block = begin_fragment_block(
                        "compare.defaulted.subobject");
                    cir::InstId lhs_subobject = builder_.field_addr(
                        lhs_object, subobject.entity,
                        subobject.type.type, loc);
                    cir::InstId rhs_subobject = builder_.field_addr(
                        rhs_object, subobject.entity,
                        subobject.type.type, loc);
                    cir::Fragment address_fragment = finish_fragment_block(
                        address_block, function_block);
                    ExprResult compared;
                    if (!subobject.array_extents.empty()) {
                        compared = collect_defaulted_array_three_way(
                            lhs_subobject, rhs_subobject,
                            subobject.type.type, *three_way_category,
                            !three_way_result_was_deduced, loc);
                        compared.fragment = chain(
                            std::move(address_fragment),
                            std::move(compared.fragment), loc);
                    } else {
                        ExprResult lhs_expr;
                        lhs_expr.fragment = std::move(address_fragment);
                        lhs_expr.place = lhs_subobject;
                        lhs_expr.entity = subobject.entity;
                        lhs_expr.type = subobject.type.type;
                        lhs_expr.category = ValueCategory::LValue;
                        ExprResult rhs_expr;
                        rhs_expr.place = rhs_subobject;
                        rhs_expr.entity = subobject.entity;
                        rhs_expr.type = subobject.type.type;
                        rhs_expr.category = ValueCategory::LValue;
                        if (const cir::RecordFieldFact* field =
                                file_.field_fact(subobject.entity)) {
                            lhs_expr.designates_bitfield = field->is_bitfield;
                            rhs_expr.designates_bitfield = field->is_bitfield;
                        }
                        compared = collect_synthesized_three_way_compare(
                            std::move(lhs_expr), std::move(rhs_expr),
                            *three_way_category,
                            !three_way_result_was_deduced, loc);
                    }
                    failed = failed || compared.has_error;
                    ExprResult returned_value = compared;
                    returned_value.fragment = {};
                    returned_value.materialized_lifetimes.clear();
                    ExprResult zero = make_integer_literal(0, "0", loc);
                    ExprResult nonzero = collect_binary_expr(
                        syntax::BinaryOperator::NotEqual,
                        std::move(compared), std::move(zero), loc);
                    nonzero = convert_to_condition(std::move(nonzero), loc);
                    StmtResult returned = collect_return_stmt(
                        std::move(returned_value), loc);
                    failed = failed || nonzero.has_error ||
                        returned.has_error;
                    steps.push_back(ComparisonStep{
                        std::move(nonzero), std::move(returned)});
                }

                cir::BlockId equivalent_block = begin_fragment_block(
                    "compare.defaulted.equivalent");
                ExprResult equivalent;
                equivalent.place = builder_.global_place(
                    three_way_category->equivalent, loc);
                equivalent.type = three_way_category->type;
                equivalent.category = ValueCategory::LValue;
                equivalent.fragment = finish_fragment_block(
                    equivalent_block, function_block);
                StmtResult body = collect_return_stmt(
                    std::move(equivalent), loc);
                for (size_t i = steps.size(); i-- > 0;) {
                    body = collect_if_stmt(
                        std::move(steps[i].nonzero),
                        std::move(steps[i].returned),
                        std::optional<StmtResult>(std::move(body)), loc,
                        LifetimeBoundary{});
                }
                body.fragment = chain(std::move(object_fragment),
                                      std::move(body.fragment), loc);
                failed = failed || body.has_error;
                finish_member_function(std::move(body), loc);
            }
            restore_function_context(std::move(saved));
            failed = failed || file_.errors().size() != errors_before;
            if (failed) {
                file_.rollback_transaction(transaction);
                if (cir::RecordMethodFact* mutable_method =
                        file_.method_fact_mut(method.entity)) {
                    mutable_method->is_deleted = true;
                }
                if (cir::DefaultedComparisonFact* mutable_plan =
                        file_.defaulted_comparison_fact_mut(method.entity)) {
                    mutable_plan->is_deleted = true;
                    mutable_plan->deletion_reason =
                        "a selected subobject three-way comparison is not "
                        "usable";
                }
            } else {
                const bool potentially_throwing =
                    defaulted_comparison_function_potentially_throws(
                        start.function.function);
                publish_defaulted_comparison_properties(
                    method.entity, implicitly_constexpr,
                    !method.has_explicit_exception_spec &&
                        !method.is_user_provided,
                    potentially_throwing);
                file_.commit_transaction(transaction);
                file_.entity_mut(method.entity).linkage =
                    cir::LinkageKind::LinkOnceODR;
            }
            continue;
        }

        const bool secondary =
            kind == cir::DefaultedComparisonKind::NotEqual ||
            kind == cir::DefaultedComparisonKind::Less ||
            kind == cir::DefaultedComparisonKind::LessEqual ||
            kind == cir::DefaultedComparisonKind::Greater ||
            kind == cir::DefaultedComparisonKind::GreaterEqual;
        if (synthesize_bodies && secondary && function &&
            !function->parameters.empty()) {
            syntax::BinaryOperator binary = syntax::BinaryOperator::NotEqual;
            if (kind == cir::DefaultedComparisonKind::Less) {
                binary = syntax::BinaryOperator::Less;
            } else if (kind == cir::DefaultedComparisonKind::LessEqual) {
                binary = syntax::BinaryOperator::LessEqual;
            } else if (kind == cir::DefaultedComparisonKind::Greater) {
                binary = syntax::BinaryOperator::Greater;
            } else if (kind == cir::DefaultedComparisonKind::GreaterEqual) {
                binary = syntax::BinaryOperator::GreaterEqual;
            }
            size_t errors_before = file_.errors().size();
            cir::File::TransactionId transaction = file_.begin_transaction();
            std::unique_ptr<BlockContextState> saved = save_function_context();
            ParamInput other;
            other.name = ".comparison.other";
            other.type = function->parameters.front();
            other.loc = loc;
            FunctionDeclStart start =
                begin_member_function(method.entity, {other}, loc, true);
            bool failed = start.decl.has_error ||
                start.function.parameters.size() < 2;
            if (!failed) {
                cir::BlockId function_block = builder_.current_block();
                cir::BlockId object_block = begin_fragment_block(
                    "compare.defaulted.secondary.objects");
                cir::InstId this_pointer =
                    builder_.lvalue_to_rvalue(current_this_place_, loc);
                ExprResult lhs_expr;
                lhs_expr.place = builder_.deref(this_pointer, loc);
                lhs_expr.type = file_.entity(record).type;
                lhs_expr.category = ValueCategory::LValue;
                lhs_expr.fragment = finish_fragment_block(
                    object_block, function_block);
                ExprResult rhs_expr;
                rhs_expr.place = builder_.deref(
                    start.function.parameters[1].value.inst, loc);
                rhs_expr.type = file_.entity(record).type;
                rhs_expr.category = ValueCategory::LValue;
                ExprResult yielded = collect_binary_expr(
                    binary, std::move(lhs_expr), std::move(rhs_expr), loc);
                yielded = convert_to_condition(std::move(yielded), loc);
                StmtResult returned = collect_return_stmt(
                    std::move(yielded), loc);
                failed = failed || returned.has_error;
                finish_member_function(std::move(returned), loc);
            }
            restore_function_context(std::move(saved));
            failed = failed || file_.errors().size() != errors_before;
            if (failed) {
                file_.rollback_transaction(transaction);
                if (cir::RecordMethodFact* mutable_method =
                        file_.method_fact_mut(method.entity)) {
                    mutable_method->is_deleted = true;
                }
                if (cir::DefaultedComparisonFact* mutable_plan =
                        file_.defaulted_comparison_fact_mut(method.entity)) {
                    mutable_plan->is_deleted = true;
                    mutable_plan->deletion_reason =
                        "the rewritten secondary comparison is not usable";
                }
            } else {
                const bool potentially_throwing =
                    defaulted_comparison_function_potentially_throws(
                        start.function.function);
                publish_defaulted_comparison_properties(
                    method.entity, implicitly_constexpr,
                    !method.has_explicit_exception_spec &&
                        !method.is_user_provided,
                    potentially_throwing);
                file_.commit_transaction(transaction);
                file_.entity_mut(method.entity).linkage =
                    cir::LinkageKind::LinkOnceODR;
            }
            continue;
        }
        if (!synthesize_bodies || kind != cir::DefaultedComparisonKind::Equal ||
            !function || function->parameters.empty()) {
            continue;
        }

        size_t errors_before = file_.errors().size();
        cir::File::TransactionId transaction = file_.begin_transaction();
        std::unique_ptr<BlockContextState> saved = save_function_context();
        ParamInput other;
        other.name = ".comparison.other";
        other.type = function->parameters.front();
        other.loc = loc;
        FunctionDeclStart start =
            begin_member_function(method.entity, {other}, loc, true);
        bool failed = start.decl.has_error ||
            start.function.parameters.size() < 2;
        if (!failed) {
            cir::BlockId function_block = builder_.current_block();
            cir::BlockId object_block =
                begin_fragment_block("compare.defaulted.objects");
            cir::InstId this_pointer =
                builder_.lvalue_to_rvalue(current_this_place_, loc);
            cir::InstId lhs_object = builder_.deref(this_pointer, loc);
            cir::InstId rhs_object = builder_.deref(
                start.function.parameters[1].value.inst, loc);
            cir::Fragment object_fragment =
                finish_fragment_block(object_block, function_block);

            ExprResult accumulated;
            bool have_accumulated = false;
            for (const cir::ComparisonSubobjectFact& subobject :
                 plan.subobjects) {
                cir::BlockId address_block =
                    begin_fragment_block("compare.defaulted.subobject");
                cir::InstId lhs_subobject = builder_.field_addr(
                    lhs_object, subobject.entity, subobject.type.type, loc);
                cir::InstId rhs_subobject = builder_.field_addr(
                    rhs_object, subobject.entity, subobject.type.type, loc);
                cir::Fragment address_fragment =
                    finish_fragment_block(address_block, function_block);
                ExprResult equal;
                if (!subobject.array_extents.empty()) {
                    equal = collect_defaulted_array_equality(
                        lhs_subobject, rhs_subobject, subobject.type.type, loc);
                    equal.fragment = chain(std::move(address_fragment),
                                           std::move(equal.fragment), loc);
                } else {
                    ExprResult lhs_expr;
                    lhs_expr.fragment = std::move(address_fragment);
                    lhs_expr.place = lhs_subobject;
                    lhs_expr.entity = subobject.entity;
                    lhs_expr.type = subobject.type.type;
                    lhs_expr.category = ValueCategory::LValue;
                    ExprResult rhs_expr;
                    rhs_expr.place = rhs_subobject;
                    rhs_expr.entity = subobject.entity;
                    rhs_expr.type = subobject.type.type;
                    rhs_expr.category = ValueCategory::LValue;
                    if (const cir::RecordFieldFact* field =
                            file_.field_fact(subobject.entity)) {
                        lhs_expr.designates_bitfield = field->is_bitfield;
                        rhs_expr.designates_bitfield = field->is_bitfield;
                    }
                    equal = collect_binary_expr(
                        syntax::BinaryOperator::Equal, std::move(lhs_expr),
                        std::move(rhs_expr), loc);
                    equal = convert_to_condition(std::move(equal), loc);
                }
                failed = failed || equal.has_error;
                if (!have_accumulated) {
                    accumulated = std::move(equal);
                    accumulated.fragment = chain(
                        std::move(object_fragment),
                        std::move(accumulated.fragment), loc);
                    have_accumulated = true;
                } else {
                    accumulated = collect_binary_expr_builtin(
                        syntax::BinaryOperator::LogicalAnd,
                        std::move(accumulated), std::move(equal), loc);
                }
            }
            if (!have_accumulated) {
                accumulated = make_boolean_literal(true, "true", loc);
                accumulated.fragment = chain(std::move(object_fragment),
                                               std::move(accumulated.fragment),
                                               loc);
            }
            StmtResult returned =
                collect_return_stmt(std::move(accumulated), loc);
            failed = failed || returned.has_error;
            finish_member_function(std::move(returned), loc);
        }
        restore_function_context(std::move(saved));
        failed = failed || file_.errors().size() != errors_before;
        if (failed) {
            file_.rollback_transaction(transaction);
            if (cir::RecordMethodFact* mutable_method =
                    file_.method_fact_mut(method.entity)) {
                mutable_method->is_deleted = true;
            }
            if (cir::DefaultedComparisonFact* mutable_plan =
                    file_.defaulted_comparison_fact_mut(method.entity)) {
                mutable_plan->is_deleted = true;
                mutable_plan->deletion_reason =
                    "a selected subobject equality comparison is not usable";
            }
        } else {
            const bool potentially_throwing =
                defaulted_comparison_function_potentially_throws(
                    start.function.function);
            publish_defaulted_comparison_properties(
                method.entity, implicitly_constexpr,
                !method.has_explicit_exception_spec &&
                    !method.is_user_provided,
                potentially_throwing);
            file_.commit_transaction(transaction);
            file_.entity_mut(method.entity).linkage =
                cir::LinkageKind::LinkOnceODR;
        }
    }
}

void Session::synthesize_defaulted_friend_comparison(cir::EntityId function,
                                                      cir::EntityId record,
                                                      bool has_explicit_exception_spec,
                                                      SrcLoc loc) {
    if (!function.valid() || !file_.valid(function) || !record.valid() ||
        !file_.valid(record)) {
        return;
    }
    const cir::RecordFacts* facts = file_.record_facts(record);
    const cir::Entity& declaration = file_.entity(function);
    const auto* function_type = std::get_if<cir::FunctionTypePayload>(
        &file_.type_payload(file_.resolved_type(declaration.type)));
    if (!facts || !function_type || function_type->parameters.size() != 2 ||
        !declaration.name.valid()) {
        return;
    }

    std::string_view name = file_.name(declaration.name);
    cir::DefaultedComparisonKind kind;
    syntax::BinaryOperator secondary_op = syntax::BinaryOperator::Invalid;
    if (name == "operator==") {
        kind = cir::DefaultedComparisonKind::Equal;
    } else if (name == "operator!=") {
        kind = cir::DefaultedComparisonKind::NotEqual;
        secondary_op = syntax::BinaryOperator::NotEqual;
    } else if (name == "operator<") {
        kind = cir::DefaultedComparisonKind::Less;
        secondary_op = syntax::BinaryOperator::Less;
    } else if (name == "operator<=") {
        kind = cir::DefaultedComparisonKind::LessEqual;
        secondary_op = syntax::BinaryOperator::LessEqual;
    } else if (name == "operator>") {
        kind = cir::DefaultedComparisonKind::Greater;
        secondary_op = syntax::BinaryOperator::Greater;
    } else if (name == "operator>=") {
        kind = cir::DefaultedComparisonKind::GreaterEqual;
        secondary_op = syntax::BinaryOperator::GreaterEqual;
    } else if (name == "operator<=>") {
        kind = cir::DefaultedComparisonKind::ThreeWay;
    } else {
        return;
    }

    cir::DefaultedComparisonFact plan;
    plan.function = function;
    plan.owner_record = record;
    plan.kind = kind;
    plan.is_friend = true;
    plan.result_type = function_type->return_type;
    plan.is_constexpr = declaration.decl_flags.is_constexpr;
    plan.is_noexcept = function_type->exception_spec.kind ==
        cir::FunctionExceptionSpecKind::NonThrowing;
    auto is_const_self_lvalue_reference = [&](cir::TypeRef parameter) {
        cir::TypeId type = file_.resolved_type(parameter.type);
        if (!file_.valid(type) ||
            file_.type(type).kind != cir::TypeKind::LValueReference) {
            return false;
        }
        cir::TypeRef referred = file_.reference_referred_ref(type);
        return file_.resolved_type(referred.type) ==
                   file_.resolved_type(file_.entity(record).type) &&
               referred.qualifiers == cir::QualConst;
    };
    auto is_self_value = [&](cir::TypeRef parameter) {
        cir::TypeId type = file_.resolved_type(parameter.type);
        return type == file_.resolved_type(file_.entity(record).type) &&
               file_.valid(type) &&
               file_.type(type).kind == cir::TypeKind::Record;
    };
    const bool parameters_are_references =
        is_const_self_lvalue_reference(function_type->parameters[0]) &&
        is_const_self_lvalue_reference(function_type->parameters[1]);
    const bool parameters_are_values =
        is_self_value(function_type->parameters[0]) &&
        is_self_value(function_type->parameters[1]);
    if (!parameters_are_references && !parameters_are_values) {
        report_error(
            "defaulted comparison operator parameters must both have type 'const " +
                file_.format_type(file_.entity(record).type) +
                "&' or both have the record type by value",
            loc);
        plan.is_deleted = true;
        plan.deletion_reason =
            "the two parameters do not have the required const record reference type";
        file_.set_defaulted_comparison_fact(function, std::move(plan));
        return;
    }
    if (kind == cir::DefaultedComparisonKind::Equal ||
        kind == cir::DefaultedComparisonKind::ThreeWay) {
        bool has_reference_member = std::any_of(
            facts->fields.begin(), facts->fields.end(),
            [&](const cir::RecordFieldFact& field) {
                return !field.is_base_subobject &&
                       is_reference_type(field.type.type);
            });
        bool has_variant_member = facts->kind == cir::RecordKind::Union &&
            std::any_of(facts->fields.begin(), facts->fields.end(),
                        [](const cir::RecordFieldFact& field) {
                            return !field.is_base_subobject;
                        });
        if (has_reference_member || has_variant_member) {
            plan.is_deleted = true;
            plan.deletion_reason = has_reference_member
                ? "the record has a reference data member"
                : "the union has variant members";
        }
    }

    std::vector<cir::EntityId> used_base_fields;
    std::vector<const cir::RecordBaseFact*> direct_bases;
    for (const cir::RecordBaseFact& base : facts->bases) {
        direct_bases.push_back(&base);
    }
    std::stable_sort(
        direct_bases.begin(), direct_bases.end(),
        [](const cir::RecordBaseFact* lhs,
           const cir::RecordBaseFact* rhs) {
            return lhs->declaration_index < rhs->declaration_index;
        });
    for (const cir::RecordBaseFact* base : direct_bases) {
        cir::EntityId storage{};
        for (const cir::RecordFieldFact& candidate : facts->fields) {
            if (candidate.is_base_subobject &&
                file_.resolved_type(candidate.type.type) ==
                    file_.resolved_type(base->type.type) &&
                std::find(used_base_fields.begin(), used_base_fields.end(),
                          candidate.entity) == used_base_fields.end()) {
                storage = candidate.entity;
                break;
            }
        }
        if (!storage.valid()) {
            plan.is_deleted = true;
            plan.deletion_reason =
                "comparison base subobject storage is unavailable";
            continue;
        }
        used_base_fields.push_back(storage);
        cir::ComparisonSubobjectFact subobject;
        subobject.kind = cir::ComparisonSubobjectKind::DirectBase;
        subobject.entity = storage;
        subobject.type = base->type;
        plan.subobjects.push_back(std::move(subobject));
    }
    for (const cir::RecordFieldFact& field : facts->fields) {
        if (field.is_base_subobject ||
            (field.name.valid() && file_.name(field.name) == ".vptr")) {
            continue;
        }
        cir::ComparisonSubobjectFact subobject;
        subobject.kind = cir::ComparisonSubobjectKind::Field;
        subobject.entity = field.entity;
        subobject.type = field.type;
        cir::TypeId current = file_.resolved_type(field.type.type);
        size_t total = 1;
        while (file_.valid(current) &&
               file_.type(current).kind == cir::TypeKind::Array) {
            const auto* array = std::get_if<cir::ArrayTypePayload>(
                &file_.type_payload(current));
            if (!array || !array->size.has_value() ||
                array->size_expr_is_dependent) {
                plan.is_dependent = true;
                break;
            }
            subobject.array_extents.push_back(*array->size);
            total *= *array->size;
            current = file_.resolved_type(array->element_type.type);
        }
        if (!subobject.array_extents.empty()) {
            subobject.array_leaf_type = file_.type_ref(current);
            subobject.array_element_count = total;
        }
        plan.subobjects.push_back(std::move(subobject));
    }

    std::optional<ComparisonCategory> three_way_category;
    bool three_way_result_was_deduced = false;
    if (kind == cir::DefaultedComparisonKind::ThreeWay) {
        std::optional<ComparisonCategory> strong =
            resolve_comparison_category(ComparisonCategoryKind::Strong, loc,
                                        /*diagnose=*/false);
        std::optional<ComparisonCategory> weak =
            resolve_comparison_category(ComparisonCategoryKind::Weak, loc,
                                        /*diagnose=*/false);
        std::optional<ComparisonCategory> partial =
            resolve_comparison_category(ComparisonCategoryKind::Partial, loc,
                                        /*diagnose=*/false);
        auto category_for_type = [&](cir::TypeId type)
            -> std::optional<ComparisonCategory> {
            type = file_.resolved_type(type);
            if (strong && file_.resolved_type(strong->type) == type) {
                return strong;
            }
            if (weak && file_.resolved_type(weak->type) == type) {
                return weak;
            }
            if (partial && file_.resolved_type(partial->type) == type) {
                return partial;
            }
            return std::nullopt;
        };
        bool deduced_result = function_has_placeholder_return(
            declaration.type);
        three_way_result_was_deduced = deduced_result;
        if (deduced_result) {
            ComparisonCategoryKind common = ComparisonCategoryKind::Strong;
            bool valid_common = true;
            for (const cir::ComparisonSubobjectFact& subobject :
                 plan.subobjects) {
                cir::TypeId operand = !subobject.array_extents.empty()
                    ? subobject.array_leaf_type.type
                    : subobject.type.type;
                operand = file_.resolved_type(operand);
                std::optional<ComparisonCategory> component;
                if (is_floating_type(operand)) {
                    component = partial;
                } else if (is_arithmetic_type(operand) ||
                           is_pointer_type(operand) ||
                           is_scoped_enum_type(operand)) {
                    component = strong;
                } else if (const cir::RecordFacts* operand_facts =
                               file_.record_facts_for_type(operand)) {
                    for (const cir::RecordMethodFact& candidate :
                         operand_facts->methods) {
                        if (!candidate.name.valid() ||
                            file_.name(candidate.name) != "operator<=>") {
                            continue;
                        }
                        const auto* candidate_type =
                            std::get_if<cir::FunctionTypePayload>(
                                &file_.type_payload(file_.resolved_type(
                                    candidate.type.type)));
                        if (candidate_type) {
                            component = category_for_type(
                                candidate_type->return_type.type);
                            if (component) {
                                break;
                            }
                        }
                    }
                }
                if (!component) {
                    valid_common = false;
                    break;
                }
                if (component->kind == ComparisonCategoryKind::Partial) {
                    common = ComparisonCategoryKind::Partial;
                } else if (component->kind ==
                               ComparisonCategoryKind::Weak &&
                           common == ComparisonCategoryKind::Strong) {
                    common = ComparisonCategoryKind::Weak;
                }
            }
            if (valid_common) {
                if (common == ComparisonCategoryKind::Strong) {
                    three_way_category = strong;
                } else if (common == ComparisonCategoryKind::Weak) {
                    three_way_category = weak;
                } else {
                    three_way_category = partial;
                }
            }
            if (three_way_category) {
                cir::PlaceholderResultFactId placeholder =
                    register_placeholder_result(
                        function, declaration.type, nullptr, loc);
                publish_placeholder_result(
                    placeholder, file_.type_ref(three_way_category->type),
                    loc, /*final=*/true);
                plan.result_type =
                    file_.type_ref(three_way_category->type);
                function_type = std::get_if<cir::FunctionTypePayload>(
                    &file_.type_payload(file_.resolved_type(
                        file_.entity(function).type)));
            }
        } else {
            three_way_category = category_for_type(
                function_type->return_type.type);
        }
        if (!three_way_category) {
            plan.is_deleted = true;
            plan.deletion_reason =
                "expanded subobject comparisons do not have a common comparison category";
        }
    } else if (file_.resolved_type(function_type->return_type.type) !=
        file_.resolved_type(builder_.bool_type())) {
        plan.is_deleted = true;
        plan.deletion_reason =
            "a defaulted equality or secondary comparison must return bool";
        file_.set_defaulted_comparison_fact(function, std::move(plan));
        return;
    }
    file_.set_defaulted_comparison_fact(function, plan);
    if (plan.is_deleted) {
        return;
    }
    publish_defaulted_comparison_properties(
        function, /*implicitly_constexpr=*/true,
        /*compute_implicit_exception_spec=*/false,
        /*potentially_throwing=*/true);

    size_t errors_before = file_.errors().size();
    cir::File::TransactionId transaction = file_.begin_transaction();
    std::unique_ptr<BlockContextState> saved = save_function_context();
    ParamInput lhs_parameter;
    lhs_parameter.name = ".comparison.lhs";
    lhs_parameter.type = function_type->parameters[0];
    lhs_parameter.loc = loc;
    ParamInput rhs_parameter;
    rhs_parameter.name = ".comparison.rhs";
    rhs_parameter.type = function_type->parameters[1];
    rhs_parameter.loc = loc;
    DeclFlags flags;
    flags.is_inline = true;
    flags.is_constexpr = true;
    flags.is_consteval = declaration.decl_flags.is_consteval;
    FunctionDeclStart start = begin_function_type_on_entity(
        function, name, declaration.type, function_type->return_type,
        {lhs_parameter, rhs_parameter}, loc, flags);
    bool failed = start.decl.has_error || start.function.parameters.size() < 2;
    if (!failed) {
        cir::BlockId function_block = builder_.current_block();
        cir::BlockId object_block =
            begin_fragment_block("compare.defaulted.friend.objects");
        cir::InstId lhs_object;
        cir::InstId rhs_object;
        if (parameters_are_values) {
            const cir::Binding* lhs_binding =
                lookup_ordinary_binding(".comparison.lhs", false);
            const cir::Binding* rhs_binding =
                lookup_ordinary_binding(".comparison.rhs", false);
            lhs_object = lhs_binding ? lhs_binding->place : cir::InstId{};
            rhs_object = rhs_binding ? rhs_binding->place : cir::InstId{};
            failed = failed || !lhs_object.valid() || !rhs_object.valid();
        } else {
            lhs_object = builder_.deref(
                start.function.parameters[0].value.inst, loc);
            rhs_object = builder_.deref(
                start.function.parameters[1].value.inst, loc);
        }
        cir::Fragment object_fragment =
            finish_fragment_block(object_block, function_block);

        if (kind == cir::DefaultedComparisonKind::ThreeWay &&
            three_way_category) {
            struct ComparisonStep {
                ExprResult nonzero;
                StmtResult returned;
            };
            std::vector<ComparisonStep> steps;
            for (const cir::ComparisonSubobjectFact& subobject :
                 plan.subobjects) {
                if (!subobject.array_extents.empty() &&
                    subobject.array_element_count == 0) {
                    continue;
                }
                cir::BlockId address_block = begin_fragment_block(
                    "compare.defaulted.friend.subobject");
                cir::InstId lhs_subobject = builder_.field_addr(
                    lhs_object, subobject.entity, subobject.type.type, loc);
                cir::InstId rhs_subobject = builder_.field_addr(
                    rhs_object, subobject.entity, subobject.type.type, loc);
                cir::Fragment address_fragment = finish_fragment_block(
                    address_block, function_block);
                ExprResult compared;
                if (!subobject.array_extents.empty()) {
                    compared = collect_defaulted_array_three_way(
                        lhs_subobject, rhs_subobject,
                        subobject.type.type, *three_way_category,
                        !three_way_result_was_deduced, loc);
                    compared.fragment = chain(std::move(address_fragment),
                                               std::move(compared.fragment),
                                               loc);
                } else {
                    ExprResult lhs_expr;
                    lhs_expr.fragment = std::move(address_fragment);
                    lhs_expr.place = lhs_subobject;
                    lhs_expr.type = subobject.type.type;
                    lhs_expr.category = ValueCategory::LValue;
                    ExprResult rhs_expr;
                    rhs_expr.place = rhs_subobject;
                    rhs_expr.type = subobject.type.type;
                    rhs_expr.category = ValueCategory::LValue;
                    compared = collect_synthesized_three_way_compare(
                        std::move(lhs_expr), std::move(rhs_expr),
                        *three_way_category,
                        !three_way_result_was_deduced, loc);
                }
                failed = failed || compared.has_error;
                ExprResult returned_value = compared;
                returned_value.fragment = {};
                returned_value.materialized_lifetimes.clear();
                ExprResult zero = make_integer_literal(0, "0", loc);
                ExprResult nonzero = collect_binary_expr(
                    syntax::BinaryOperator::NotEqual,
                    std::move(compared), std::move(zero), loc);
                nonzero = convert_to_condition(std::move(nonzero), loc);
                StmtResult returned = collect_return_stmt(
                    std::move(returned_value), loc);
                failed = failed || nonzero.has_error || returned.has_error;
                steps.push_back(ComparisonStep{
                    std::move(nonzero), std::move(returned)});
            }
            cir::BlockId equivalent_block = begin_fragment_block(
                "compare.defaulted.friend.equivalent");
            ExprResult equivalent;
            equivalent.place = builder_.global_place(
                three_way_category->equivalent, loc);
            equivalent.type = three_way_category->type;
            equivalent.category = ValueCategory::LValue;
            equivalent.fragment = finish_fragment_block(
                equivalent_block, function_block);
            StmtResult body = collect_return_stmt(
                std::move(equivalent), loc);
            for (size_t i = steps.size(); i-- > 0;) {
                body = collect_if_stmt(
                    std::move(steps[i].nonzero),
                    std::move(steps[i].returned),
                    std::optional<StmtResult>(std::move(body)), loc,
                    LifetimeBoundary{});
            }
            body.fragment = chain(std::move(object_fragment),
                                  std::move(body.fragment), loc);
            failed = failed || body.has_error;
            finish_function(std::move(body), loc);
        } else {
            ExprResult result;
            if (kind == cir::DefaultedComparisonKind::Equal) {
                bool have_result = false;
                for (const cir::ComparisonSubobjectFact& subobject :
                     plan.subobjects) {
                    cir::BlockId address_block = begin_fragment_block(
                        "compare.defaulted.friend.subobject");
                    cir::InstId lhs_subobject = builder_.field_addr(
                        lhs_object, subobject.entity,
                        subobject.type.type, loc);
                    cir::InstId rhs_subobject = builder_.field_addr(
                        rhs_object, subobject.entity,
                        subobject.type.type, loc);
                    cir::Fragment address_fragment = finish_fragment_block(
                        address_block, function_block);
                    ExprResult equal;
                    if (!subobject.array_extents.empty()) {
                        equal = collect_defaulted_array_equality(
                            lhs_subobject, rhs_subobject,
                            subobject.type.type, loc);
                        equal.fragment = chain(
                            std::move(address_fragment),
                            std::move(equal.fragment), loc);
                    } else {
                        ExprResult lhs_expr;
                        lhs_expr.fragment = std::move(address_fragment);
                        lhs_expr.place = lhs_subobject;
                        lhs_expr.type = subobject.type.type;
                        lhs_expr.category = ValueCategory::LValue;
                        ExprResult rhs_expr;
                        rhs_expr.place = rhs_subobject;
                        rhs_expr.type = subobject.type.type;
                        rhs_expr.category = ValueCategory::LValue;
                        equal = collect_binary_expr(
                            syntax::BinaryOperator::Equal,
                            std::move(lhs_expr), std::move(rhs_expr), loc);
                        equal = convert_to_condition(std::move(equal), loc);
                    }
                    failed = failed || equal.has_error;
                    if (!have_result) {
                        result = std::move(equal);
                        result.fragment = chain(
                            std::move(object_fragment),
                            std::move(result.fragment), loc);
                        have_result = true;
                    } else {
                        result = collect_binary_expr_builtin(
                            syntax::BinaryOperator::LogicalAnd,
                            std::move(result), std::move(equal), loc);
                    }
                }
                if (!have_result) {
                    result = make_boolean_literal(true, "true", loc);
                    result.fragment = chain(std::move(object_fragment),
                                            std::move(result.fragment), loc);
                }
            } else {
                ExprResult lhs_expr;
                lhs_expr.fragment = std::move(object_fragment);
                lhs_expr.place = lhs_object;
                lhs_expr.type = file_.entity(record).type;
                lhs_expr.category = ValueCategory::LValue;
                ExprResult rhs_expr;
                rhs_expr.place = rhs_object;
                rhs_expr.type = file_.entity(record).type;
                rhs_expr.category = ValueCategory::LValue;
                result = collect_binary_expr(secondary_op,
                                             std::move(lhs_expr),
                                             std::move(rhs_expr), loc);
                result = convert_to_condition(std::move(result), loc);
            }
            StmtResult returned = collect_return_stmt(std::move(result), loc);
            failed = failed || returned.has_error;
            finish_function(std::move(returned), loc);
        }
    }
    restore_function_context(std::move(saved));
    failed = failed || file_.errors().size() != errors_before;
    if (failed) {
        file_.rollback_transaction(transaction);
        if (cir::DefaultedComparisonFact* mutable_plan =
                file_.defaulted_comparison_fact_mut(function)) {
            mutable_plan->is_deleted = true;
            mutable_plan->deletion_reason =
                "a selected comparison expression is not usable";
        }
    } else {
        const bool potentially_throwing =
            defaulted_comparison_function_potentially_throws(
                start.function.function);
        publish_defaulted_comparison_properties(
            function, /*implicitly_constexpr=*/true,
            !has_explicit_exception_spec,
            potentially_throwing);
        file_.commit_transaction(transaction);
        file_.entity_mut(function).linkage = cir::LinkageKind::LinkOnceODR;
    }
}

} // namespace aburi::collect
