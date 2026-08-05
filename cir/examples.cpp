#include "examples.h"

#include "builder.h"

namespace aburi::cir {
namespace {

File build_c_sizeof_call() {
    File file;
    Builder b(file);
    TypeId i32 = b.int_type();
    auto fn = b.begin_function("f", i32, {{"x", i32}});
    EntityId g = b.add_entity(EntityKind::Function, "g",
        b.function_type(i32, {i32}));

    InstId size = b.sizeof_type(i32);
    InstId call = b.call(g, i32, {fn.parameters[0].value.inst});
    InstId size_i32 = b.cast(i32, size, "integer");
    InstId sum = b.binary(BinaryOpKind::Add, i32, size_i32, call);
    b.return_value(sum);
    return file;
}

File build_c_places_branch() {
    File file;
    Builder b(file);
    TypeId i32 = b.int_type();
    auto fn = b.begin_function("choose", i32,
        {{"a", i32}, {"b", i32}, {"cond", i32}});

    EntityId result_entity = b.add_entity(EntityKind::Variable, "result", i32, fn.entity);
    InstId result_place = b.local_place(result_entity, i32);

    BlockId then_block = b.create_block("then");
    BlockId else_block = b.create_block("else");
    BlockId merge_block = b.create_block("merge");

    b.cond_branch(fn.parameters[2].value.inst, then_block, else_block);

    b.switch_to_block(then_block);
    b.store(result_place, fn.parameters[0].value.inst);
    b.branch(merge_block);

    b.switch_to_block(else_block);
    b.store(result_place, fn.parameters[1].value.inst);
    b.branch(merge_block);

    b.switch_to_block(merge_block);
    InstId result = b.load(result_place);
    b.return_value(result);
    return file;
}

File build_cxx_member() {
    File file;
    Builder b(file);
    TypeId i32 = b.int_type();

    EntityId vec_entity = b.add_entity(EntityKind::Record, "Vec");
    TypeId vec_type = b.record_type(vec_entity, "Vec");
    EntityId x_field = b.add_entity(EntityKind::Field, "Vec::x", i32, vec_entity);
    EntityId y_field = b.add_entity(EntityKind::Field, "Vec::y", i32, vec_entity);

    TypeId this_type = b.pointer_type(vec_type);
    EntityId len_entity = b.add_entity(EntityKind::Method, "Vec::len",
        b.function_type(i32, {this_type}), vec_entity);
    auto fn = b.begin_function(len_entity, i32, {{b.add_entity(EntityKind::Parameter, "this", this_type, len_entity), this_type}});

    InstId self_place = b.deref(fn.parameters[0].value.inst);
    InstId x_place_1 = b.field_addr(self_place, x_field, i32);
    InstId x_1 = b.load(x_place_1);
    InstId x_place_2 = b.field_addr(self_place, x_field, i32);
    InstId x_2 = b.load(x_place_2);
    InstId xx = b.binary(BinaryOpKind::Mul, i32, x_1, x_2);
    InstId y_place_1 = b.field_addr(self_place, y_field, i32);
    InstId y_1 = b.load(y_place_1);
    InstId y_place_2 = b.field_addr(self_place, y_field, i32);
    InstId y_2 = b.load(y_place_2);
    InstId yy = b.binary(BinaryOpKind::Mul, i32, y_1, y_2);
    InstId sum = b.binary(BinaryOpKind::Add, i32, xx, yy);
    b.return_value(sum);
    return file;
}

File build_generic_dependent_call() {
    File file;
    Builder b(file);
    TypeId i32 = b.int_type();

    EntityId t_entity = b.add_entity(EntityKind::TemplateParam, "T");
    TypeId t_type = b.type_param_type(t_entity, "T");
    auto fn = b.begin_function("h<T>", i32, {{"x", t_type}});
    file.entity_mut(fn.entity).is_template_pattern = true;
    file.add_generic(Generic{fn.entity, SrcLoc(), {t_entity}, fn.function});

    InstId size = b.sizeof_type(t_type);
    InstId call =
        b.dependent_call("f", b.dependent_type("decltype(f(x))"), {fn.parameters[0].value.inst});
    InstId size_i32 = b.cast(i32, size, "dependent-integer");
    InstId call_i32 = b.cast(i32, call, "dependent-value");
    InstId sum = b.binary(BinaryOpKind::Add, i32, size_i32, call_i32);
    b.return_value(sum);
    return file;
}

} // namespace

std::vector<std::string> example_names() {
    return {
        "c-sizeof-call",
        "c-places-branch",
        "cxx-member",
        "generic-dependent-call"
    };
}

std::optional<File> build_example(std::string_view name) {
    if (name == "c-sizeof-call") return build_c_sizeof_call();
    if (name == "c-places-branch") return build_c_places_branch();
    if (name == "cxx-member") return build_cxx_member();
    if (name == "generic-dependent-call") return build_generic_dependent_call();
    return std::nullopt;
}

} // namespace aburi::cir
