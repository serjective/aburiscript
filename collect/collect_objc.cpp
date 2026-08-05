

#include "collect.h"

#include <algorithm>

namespace aburi::collect {

namespace {

void append_fragment_blocks(cir::Fragment& target,
                            const cir::Fragment& source) {
    if (source.empty()) {
        return;
    }
    if (target.empty()) {
        target.entry = source.entry;
    }
    target.blocks.insert(target.blocks.end(), source.blocks.begin(),
                         source.blocks.end());
    target.exit = source.exit;
}

cir::ObjCMethodFamily infer_method_family(std::string_view selector) {
    size_t start = selector.find_first_not_of('_');
    if (start == std::string_view::npos) {
        return cir::ObjCMethodFamily::None;
    }
    std::string_view body = selector.substr(start);
    auto matches = [&](std::string_view word) {
        if (body.size() < word.size() || body.substr(0, word.size()) != word) {
            return false;
        }
        if (body.size() == word.size()) {
            return true;
        }
        char next = body[word.size()];
        return !(next >= 'a' && next <= 'z');
    };
    if (matches("alloc")) return cir::ObjCMethodFamily::Alloc;
    if (matches("mutableCopy")) return cir::ObjCMethodFamily::MutableCopy;
    if (matches("copy")) return cir::ObjCMethodFamily::Copy;
    if (matches("init")) return cir::ObjCMethodFamily::Init;
    if (matches("new")) return cir::ObjCMethodFamily::New;
    if (matches("retain")) return cir::ObjCMethodFamily::Retain;
    if (matches("release")) return cir::ObjCMethodFamily::Release;
    if (matches("autorelease")) return cir::ObjCMethodFamily::Autorelease;
    if (matches("dealloc")) return cir::ObjCMethodFamily::Dealloc;
    return cir::ObjCMethodFamily::None;
}

std::string objc_method_symbol(std::string_view class_name,
                               std::string_view selector,
                               bool is_class_method) {
    std::string symbol;
    symbol += is_class_method ? '+' : '-';
    symbol += '[';
    symbol += class_name;
    symbol += ' ';
    symbol += selector;
    symbol += ']';
    return symbol;
}

} // namespace

void Session::initialize_objc_mode() {
    if (objc_.initialized) {
        return;
    }
    objc_.initialized = true;

    objc_.object_record_type =
        declare_record_tag(cir::RecordKind::Struct, "objc_object").type;
    objc_.class_record_type =
        declare_record_tag(cir::RecordKind::Struct, "objc_class").type;
    objc_.selector_record_type =
        declare_record_tag(cir::RecordKind::Struct, "objc_selector").type;
    objc_.id_type = pointer_type(type_ref(objc_.object_record_type));
    objc_.class_type = pointer_type(type_ref(objc_.class_record_type));
    objc_.sel_type = pointer_type(type_ref(objc_.selector_record_type));
    (void)declare_typedef("id", objc_.id_type, SrcLoc());
    (void)declare_typedef("Class", objc_.class_type, SrcLoc());
    (void)declare_typedef("SEL", objc_.sel_type, SrcLoc());
}

bool Session::is_objc_class_name(std::string_view name) const {
    return objc_.classes.find(std::string(name)) != objc_.classes.end();
}

cir::TypeId Session::objc_class_object_type(std::string_view name) const {
    auto found = objc_.classes.find(std::string(name));
    if (found == objc_.classes.end()) {
        return {};
    }
    const cir::ObjCInterfaceFacts* facts =
        file_.objc_interface_facts(found->second);
    return facts ? facts->object_type : cir::TypeId{};
}

cir::TypeId Session::objc_object_pointer_type(cir::EntityId interface) {
    const cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts(interface);
    if (!facts || !facts->object_type.valid()) {
        return objc_.id_type;
    }
    return pointer_type(type_ref(facts->object_type));
}

ObjCInterfaceDeclResult Session::declare_objc_class_forward(
    std::string_view name, SrcLoc loc) {
    ObjCInterfaceDeclResult result;
    auto found = objc_.classes.find(std::string(name));
    if (found != objc_.classes.end()) {
        result.entity = found->second;
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(result.entity);
        result.object_type = facts ? facts->object_type : cir::TypeId{};
        return result;
    }
    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::ObjCInterface, name, {}, {}, loc);

    cir::EntityId object_record = builder_.add_entity(
        cir::EntityKind::Record, name, {}, entity, loc);
    cir::TypeId object_type = builder_.record_type(object_record, name);

    cir::ObjCInterfaceFacts facts;
    facts.name = file_.intern_name(name);
    facts.object_type = object_type;
    facts.is_forward_only = true;
    facts.loc = loc;
    file_.set_objc_interface_facts(entity, std::move(facts));

    objc_.classes.emplace(std::string(name), entity);
    result.entity = entity;
    result.object_type = object_type;
    return result;
}

ObjCInterfaceDeclResult Session::begin_objc_interface(
    std::string_view name,
    std::string_view super_name,
    const AttributeList& attrs,
    SrcLoc loc) {
    ObjCInterfaceDeclResult result = declare_objc_class_forward(name, loc);
    cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts_mut(result.entity);
    if (!facts) {
        result.has_error = true;
        return result;
    }
    if (facts->is_defined) {
        report_error("duplicate interface definition for '" +
                         std::string(name) + "'",
                     loc);
        result.has_error = true;
        return result;
    }
    facts->is_forward_only = false;
    facts->is_defined = true;
    facts->attributes.insert(facts->attributes.end(), attrs.attrs.begin(),
                             attrs.attrs.end());
    facts->loc = loc;
    if (!super_name.empty()) {
        auto super_found = objc_.classes.find(std::string(super_name));
        if (super_found == objc_.classes.end()) {
            report_error("cannot find interface declaration for '" +
                             std::string(super_name) + "', superclass of '" +
                             std::string(name) + "'",
                         loc);
            result.has_error = true;
        } else {
            facts->super_class = super_found->second;
        }
    }
    return result;
}

void Session::collect_objc_ivars(cir::EntityId interface,
                                 std::vector<ObjCIvarInput> ivars,
                                 SrcLoc loc) {
    cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts_mut(interface);
    if (!facts) {
        return;
    }
    for (ObjCIvarInput& input : ivars) {
        cir::ObjCIvarFact fact;
        fact.entity = builder_.add_entity(cir::EntityKind::ObjCIvar,
                                          input.name,
                                          input.type.type,
                                          interface,
                                          input.loc);
        fact.name = file_.intern_name(input.name);
        fact.type = input.type;
        fact.access = input.access;
        fact.is_bitfield = input.is_bitfield;
        fact.bit_width = input.bit_width;
        fact.attributes = std::move(input.attrs.attrs);
        fact.loc = input.loc;
        bool duplicate = std::any_of(
            facts->ivars.begin(), facts->ivars.end(),
            [&](const cir::ObjCIvarFact& existing) {
                return existing.name == fact.name;
            });
        if (duplicate) {
            report_error("duplicate instance variable '" + input.name + "'",
                         input.loc);
            continue;
        }
        facts->ivars.push_back(std::move(fact));
    }
    (void)loc;
}

cir::ObjCMethodFact Session::build_objc_method_fact(cir::EntityId interface,
                                                    ObjCMethodInput& method,
                                                    cir::EntityId method_entity) {
    cir::ObjCMethodFact fact;
    fact.entity = method_entity;
    fact.selector = file_.intern_selector(method.selector);
    cir::TypeRef return_ref = method.return_type;
    if (!return_ref.type.valid()) {
        return_ref = type_ref(method.returns_instancetype
                                  ? objc_object_pointer_type(interface)
                                  : objc_.id_type);
    }
    fact.return_type = return_ref;
    fact.is_class_method = method.is_class_method;
    fact.is_variadic = method.is_variadic;
    fact.returns_instancetype = method.returns_instancetype;
    fact.family = infer_method_family(method.selector);
    fact.is_optional = method.is_optional;
    fact.attributes = method.attrs.attrs;
    fact.loc = method.loc;

    std::vector<cir::TypeRef> param_types;
    param_types.push_back(type_ref(method.is_class_method
                                       ? objc_.class_type
                                       : objc_object_pointer_type(interface)));
    param_types.push_back(type_ref(objc_.sel_type));
    for (const ParamInput& param : method.params) {
        param_types.push_back(param.type);
    }
    fact.function_type = function_type(return_ref, param_types,
                                       method.is_variadic);
    return fact;
}

cir::EntityId Session::declare_objc_method(cir::EntityId interface,
                                           ObjCMethodInput& method) {
    cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts_mut(interface);
    if (!facts) {
        return {};
    }
    cir::SelectorId selector = file_.intern_selector(method.selector);
    if (const cir::ObjCMethodFact* existing =
            find_objc_method(interface, selector, method.is_class_method);
        existing && existing->entity.valid() &&
        file_.entity(existing->entity).parent == interface) {

        return existing->entity;
    }
    cir::EntityId entity = builder_.add_entity(cir::EntityKind::ObjCMethod,
                                               method.selector,
                                               {},
                                               interface,
                                               method.loc);
    cir::ObjCMethodFact fact = build_objc_method_fact(interface, method, entity);
    file_.entity_mut(entity).type = fact.function_type;
    std::vector<cir::ObjCMethodFact>& list = method.is_class_method
                                                 ? facts->class_methods
                                                 : facts->instance_methods;
    list.push_back(std::move(fact));

    objc_.method_pool[selector.index].push_back(
        {interface, method.is_class_method});
    return entity;
}

void Session::finish_objc_interface(cir::EntityId interface, SrcLoc loc) {
    (void)interface;
    (void)loc;
}

cir::EntityId Session::begin_objc_implementation(std::string_view name,
                                                 SrcLoc loc) {
    auto found = objc_.classes.find(std::string(name));
    if (found == objc_.classes.end()) {
        report_error("cannot find interface declaration for '" +
                         std::string(name) + "'",
                     loc);

        ObjCInterfaceDeclResult recovered = declare_objc_class_forward(name, loc);
        if (cir::ObjCInterfaceFacts* facts =
                file_.objc_interface_facts_mut(recovered.entity)) {
            facts->is_forward_only = false;
            facts->is_defined = true;
        }
        found = objc_.classes.find(std::string(name));
    }
    cir::EntityId interface = found->second;
    cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts_mut(interface);
    if (facts) {
        if (facts->implementation.valid()) {
            report_error("reimplementation of class '" + std::string(name) +
                             "'",
                         loc);
        } else {
            facts->implementation = builder_.add_entity(
                cir::EntityKind::ObjCImplementation, name, {}, interface, loc);
        }
    }
    objc_.current_interface = interface;
    return interface;
}

FunctionDeclStart Session::begin_objc_method_definition(
    cir::EntityId interface, ObjCMethodInput& method, SrcLoc loc) {
    cir::SelectorId selector = file_.intern_selector(method.selector);
    cir::ObjCMethodFact* fact =
        find_objc_method_mut(interface, selector, method.is_class_method);
    if (!fact || !fact->entity.valid() ||
        file_.entity(fact->entity).parent != interface) {

        (void)declare_objc_method(interface, method);
        fact = find_objc_method_mut(interface, selector,
                                    method.is_class_method);
    }
    FunctionDeclStart start;
    if (!fact) {
        return start;
    }

    const cir::ObjCInterfaceFacts* facts =
        file_.objc_interface_facts(interface);
    std::string class_name =
        facts ? std::string(file_.name(facts->name)) : std::string("?");
    std::string symbol =
        objc_method_symbol(class_name, method.selector, method.is_class_method);

    std::vector<ParamInput> params;
    ParamInput self_param;
    self_param.name = "self";
    self_param.type = type_ref(method.is_class_method
                                   ? objc_.class_type
                                   : objc_object_pointer_type(interface));
    self_param.loc = loc;

    if (fact->family == cir::ObjCMethodFamily::Init) {
        self_param.arc_consumed = true;
    } else {
        self_param.arc_unretained = true;
    }
    params.push_back(std::move(self_param));
    ParamInput cmd_param;
    cmd_param.name = "_cmd";
    cmd_param.type = type_ref(objc_.sel_type);
    cmd_param.loc = loc;
    cmd_param.arc_unretained = true;
    params.push_back(std::move(cmd_param));
    for (ParamInput& param : method.params) {
        params.push_back(param);
    }

    DeclFlags flags;
    flags.is_static = true;
    flags.suppress_name_binding = true;
    flags.asm_label = symbol;
    objc_.in_class_method = method.is_class_method;
    objc_.current_method_family = fact->family;
    start = begin_function_type(symbol,
                                fact->function_type,
                                fact->return_type,
                                params,
                                loc,
                                flags);
    fact->definition = start.decl.entity;
    return start;
}

void Session::finish_objc_implementation(cir::EntityId interface, SrcLoc loc) {
    (void)interface;
    (void)loc;
    objc_.current_interface = {};
    objc_.in_class_method = false;
    objc_.current_method_family = cir::ObjCMethodFamily::None;
}

const cir::ObjCMethodFact* Session::find_objc_method(
    cir::EntityId interface, cir::SelectorId selector,
    bool class_method) const {
    cir::EntityId current = interface;
    bool wants_class = class_method;

    std::vector<uint32_t> visited;
    auto search_protocols = [&](auto&& self, const cir::ObjCInterfaceFacts& facts)
        -> const cir::ObjCMethodFact* {
        for (cir::EntityId protocol : facts.protocols) {
            if (std::find(visited.begin(), visited.end(), protocol.index) !=
                visited.end()) {
                continue;
            }
            visited.push_back(protocol.index);
            const cir::ObjCInterfaceFacts* protocol_facts =
                file_.objc_interface_facts(protocol);
            if (!protocol_facts) {
                continue;
            }
            const std::vector<cir::ObjCMethodFact>& list =
                wants_class ? protocol_facts->class_methods
                            : protocol_facts->instance_methods;
            for (const cir::ObjCMethodFact& fact : list) {
                if (fact.selector == selector) {
                    return &fact;
                }
            }
            if (const cir::ObjCMethodFact* found =
                    self(self, *protocol_facts)) {
                return found;
            }
        }
        return nullptr;
    };
    while (current.valid()) {
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(current);
        if (!facts) {
            break;
        }
        const std::vector<cir::ObjCMethodFact>& list =
            wants_class ? facts->class_methods : facts->instance_methods;
        for (const cir::ObjCMethodFact& fact : list) {
            if (fact.selector == selector) {
                return &fact;
            }
        }
        if (const cir::ObjCMethodFact* found =
                search_protocols(search_protocols, *facts)) {
            return found;
        }
        if (!facts->super_class.valid()) {

            if (wants_class) {
                for (const cir::ObjCMethodFact& fact :
                     facts->instance_methods) {
                    if (fact.selector == selector) {
                        return &fact;
                    }
                }
            }
            break;
        }
        current = facts->super_class;
    }
    return nullptr;
}

cir::ObjCMethodFact* Session::find_objc_method_mut(cir::EntityId interface,
                                                   cir::SelectorId selector,
                                                   bool class_method) {
    const cir::ObjCMethodFact* found =
        find_objc_method(interface, selector, class_method);
    if (!found) {
        return nullptr;
    }
    cir::EntityId owner = file_.entity(found->entity).parent;
    cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts_mut(owner);
    if (!facts) {
        return nullptr;
    }
    std::vector<cir::ObjCMethodFact>& list =
        found->is_class_method ? facts->class_methods
                               : facts->instance_methods;
    for (cir::ObjCMethodFact& fact : list) {
        if (fact.selector == selector) {
            return &fact;
        }
    }
    return nullptr;
}

ExprResult Session::collect_objc_message_send(ObjCMessageSendInput&& input) {
    ExprResult result;
    if (arc_enabled() && !input.internal &&
        (input.selector == "retain" || input.selector == "release" ||
         input.selector == "autorelease" || input.selector == "retainCount" ||
         input.selector == "dealloc")) {
        report_error("ARC forbids explicit message send of '" +
                         input.selector + "'",
                     input.loc);
        result.has_error = true;
    }
    cir::SelectorId selector = file_.intern_selector(input.selector);

    cir::ObjCMessageSendPayload payload;
    payload.selector = selector;

    const cir::ObjCMethodFact* fact = nullptr;
    bool receiver_is_id = false;
    if (arc_enabled() && input.receiver_class.valid()) {
        const cir::ObjCInterfaceFacts* class_facts =
            file_.objc_interface_facts(input.receiver_class);
        if (class_facts && class_facts->name.valid() &&
            file_.name(class_facts->name) == "NSAutoreleasePool") {
            report_error("'NSAutoreleasePool' is unavailable: not available "
                         "in automatic reference counting mode (use "
                         "@autoreleasepool)", input.loc);
            result.has_error = true;
        }
    }
    if (input.receiver_class.valid()) {
        payload.receiver_kind = input.is_super
                                    ? cir::ObjCReceiverKind::SuperClass
                                    : cir::ObjCReceiverKind::Class;
        payload.interface_context = input.receiver_class;
        fact = find_objc_method(input.receiver_class, selector,
                                /*class_method=*/true);
        if (!fact) {
            const cir::ObjCInterfaceFacts* class_facts =
                file_.objc_interface_facts(input.receiver_class);
            std::string class_name =
                class_facts ? std::string(file_.name(class_facts->name))
                            : std::string("<class>");
            report_warning("class '" + class_name +
                               "' may not respond to '+" + input.selector +
                               "'",
                           input.loc);
        }
    } else if (input.receiver.has_value()) {
        payload.receiver_kind =
            input.is_super
                ? (objc_.in_class_method ? cir::ObjCReceiverKind::SuperClass
                                         : cir::ObjCReceiverKind::Super)
                : cir::ObjCReceiverKind::Instance;
        if (input.is_super) {
            cir::EntityId current = objc_.current_interface;
            payload.interface_context = current;
            const cir::ObjCInterfaceFacts* facts =
                current.valid() ? file_.objc_interface_facts(current) : nullptr;
            cir::EntityId super =
                facts ? facts->super_class : cir::EntityId{};
            if (!super.valid()) {
                report_error("no superclass to message from here", input.loc);
            } else {
                fact = find_objc_method(super, selector,
                                        objc_.in_class_method);
            }
        } else {

            cir::TypeId receiver_type = input.receiver->type;
            cir::EntityId receiver_interface{};
            if (receiver_type.valid()) {
                cir::TypeId resolved = file_.resolved_type(receiver_type);
                if (file_.valid(resolved) &&
                    file_.type(resolved).kind == cir::TypeKind::Pointer) {
                    const auto* pointer = std::get_if<cir::PointerTypePayload>(
                        &file_.type_payload(resolved));
                    if (pointer) {
                        cir::TypeId pointee =
                            file_.resolved_type(pointer->pointee.type);
                        cir::EntityId record = file_.record_entity(pointee);
                        if (record.valid()) {
                            for (const auto& [name, entity] : objc_.classes) {
                                const cir::ObjCInterfaceFacts* facts =
                                    file_.objc_interface_facts(entity);
                                if (facts &&
                                    file_.resolved_type(facts->object_type) ==
                                        pointee) {
                                    receiver_interface = entity;
                                    break;
                                }
                            }
                            receiver_is_id = !receiver_interface.valid() &&
                                             pointee ==
                                                 file_.resolved_type(
                                                     objc_.object_record_type);
                        } else {
                            receiver_is_id =
                                pointee == file_.resolved_type(
                                               objc_.object_record_type);
                        }
                    }
                }
            }
            if (receiver_interface.valid()) {
                payload.interface_context = receiver_interface;
                fact = find_objc_method(receiver_interface, selector,
                                        /*class_method=*/false);
                if (!fact) {
                    report_warning("instance method '-" + input.selector +
                                       "' not found; return type defaults "
                                       "to 'id'",
                                   input.loc);
                }
            } else {

                auto pool = objc_.method_pool.find(selector.index);
                if (pool != objc_.method_pool.end()) {
                    for (const ObjCState::PoolEntry& entry : pool->second) {
                        if (!entry.is_class_method) {
                            fact = find_objc_method(entry.interface, selector,
                                                    false);
                            if (fact) {
                                break;
                            }
                        }
                    }
                }
                receiver_is_id = true;
            }
        }
    }
    payload.method_declaration = fact ? fact->entity : cir::EntityId{};

    cir::TypeId result_type = objc_.id_type;
    if (fact) {
        if (fact->returns_instancetype) {
            if (payload.receiver_kind == cir::ObjCReceiverKind::Class &&
                payload.interface_context.valid()) {
                result_type = objc_object_pointer_type(payload.interface_context);
            } else if (!receiver_is_id && input.receiver.has_value() &&
                       input.receiver->type.valid()) {
                result_type = input.receiver->type;
            }
        } else if (fact->return_type.type.valid()) {
            result_type = fact->return_type.type;
        }
    }

    cir::Fragment fragment;
    std::vector<cir::InstId> values;
    std::vector<ArcWriteback> arc_writebacks;
    cir::ObjCMethodFamily send_family =
        fact ? fact->family : infer_method_family(input.selector);
    if (input.receiver.has_value()) {
        bool receiver_is_self = expr_reads_objc_self(*input.receiver);
        ExprResult receiver = require_value(std::move(*input.receiver),
                                            UseContext::RValue, input.loc);

        if (arc_enabled() &&
            send_family == cir::ObjCMethodFamily::Init) {
            if (!receiver.arc_plus_one &&
                !(receiver_is_self &&
                  objc_.current_method_family ==
                      cir::ObjCMethodFamily::Init)) {
                receiver = arc_retain_value(std::move(receiver), input.loc);
            }
            arc_claim_plus_one(receiver);
        }
        fragment = std::move(receiver.fragment);
        values.push_back(receiver.value);
        result.has_error = result.has_error || receiver.has_error;
    }
    const cir::FunctionTypePayload* signature =
        fact && fact->function_type.valid()
            ? std::get_if<cir::FunctionTypePayload>(
                  &file_.type_payload(fact->function_type))
            : nullptr;
    size_t fixed_params =
        signature && signature->parameters.size() >= 2
            ? signature->parameters.size() - 2
            : 0;
    size_t index = 0;
    for (ExprResult& arg : input.args) {
        ExprResult converted;
        if (signature && index < fixed_params) {
            cir::TypeId param_type = signature->parameters[index + 2].type;
            converted = convert_to(std::move(arg), param_type,
                                   UseContext::RValue, input.loc);
        } else {
            converted = require_value(std::move(arg), UseContext::RValue,
                                      input.loc);
        }
        if (arc_enabled()) {
            (void)arc_prepare_writeback_argument(converted, arc_writebacks,
                                                 input.loc);
        }
        fragment = chain(std::move(fragment), std::move(converted.fragment),
                         input.loc);
        values.push_back(converted.value);
        result.has_error = result.has_error || converted.has_error;
        ++index;
    }
    if (signature && index < fixed_params) {
        report_error("too few arguments to message send '" + input.selector +
                         "'",
                     input.loc);
        result.has_error = true;
    }

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.msg");
    cir::InstId inst =
        builder_.objc_message_send(payload, values, result_type, input.loc);
    arc_emit_writebacks(arc_writebacks, input.loc);
    cir::Fragment send_fragment = finish_fragment_block(block, previous);
    result.fragment = chain(std::move(fragment), std::move(send_fragment),
                            input.loc);
    result.value = inst;
    result.type = result_type;
    result.category = ValueCategory::PrValue;
    if (arc_enabled() && arc_retainable_type(result_type)) {
        result.arc_plus_one =
            send_family == cir::ObjCMethodFamily::Alloc ||
            send_family == cir::ObjCMethodFamily::New ||
            send_family == cir::ObjCMethodFamily::Copy ||
            send_family == cir::ObjCMethodFamily::MutableCopy ||
            send_family == cir::ObjCMethodFamily::Init;
        result.arc_fresh_call = !result.arc_plus_one;
        if (result.arc_plus_one) {
            arc_schedule_pending_release(result);
        }
    }
    return result;
}

ExprResult Session::collect_objc_selector_expr(std::string_view selector,
                                               SrcLoc loc) {
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.selector");
    cir::InstId inst = builder_.objc_selector_literal(
        file_.intern_selector(selector), objc_.sel_type, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = objc_.sel_type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::collect_objc_string_literal(std::string bytes,
                                                std::string spelling,
                                                SrcLoc loc) {

    cir::TypeId result_type = objc_.id_type;
    if (cir::TypeId nsstring = objc_class_object_type("NSString");
        nsstring.valid()) {
        result_type = pointer_type(type_ref(nsstring));
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.string");
    cir::InstId inst = builder_.objc_string_literal(
        std::move(bytes), std::move(spelling), result_type, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = inst;
    result.type = result_type;
    result.category = ValueCategory::PrValue;
    return result;
}

cir::EntityId Session::objc_interface_for_object_type(
    cir::TypeId object_type) const {
    if (!objc_.initialized || !object_type.valid()) {
        return {};
    }
    cir::TypeId resolved = file_.resolved_type(object_type);
    for (const auto& [name, entity] : objc_.classes) {
        (void)name;
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(entity);
        if (facts && file_.resolved_type(facts->object_type) == resolved) {
            return entity;
        }
    }
    return {};
}

ExprResult Session::collect_objc_ivar_access(ExprResult base,
                                             cir::EntityId interface,
                                             std::string_view ivar_name,
                                             SrcLoc loc) {
    ExprResult result;
    cir::NameId name = file_.intern_name(ivar_name);
    const cir::ObjCIvarFact* found = nullptr;
    cir::EntityId owner{};
    for (cir::EntityId current = interface; current.valid();) {
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(current);
        if (!facts) {
            break;
        }
        for (const cir::ObjCIvarFact& ivar : facts->ivars) {
            if (ivar.name == name) {
                found = &ivar;
                owner = current;
                break;
            }
        }
        if (found) {
            break;
        }
        current = facts->super_class;
    }
    if (!found) {
        report_error("no instance variable '" + std::string(ivar_name) +
                         "' in the receiver's class",
                     loc);
        result.has_error = true;
        result.type = file_.unknown_type();
        result.fragment = std::move(base.fragment);
        result.category = ValueCategory::PrValue;
        return result;
    }

    if (found->access == cir::ObjCIvarAccess::Private ||
        found->access == cir::ObjCIvarAccess::Protected) {
        bool allowed = false;
        for (cir::EntityId current = objc_.current_interface;
             current.valid();) {
            if (current == owner) {
                allowed = true;
                break;
            }
            if (found->access == cir::ObjCIvarAccess::Private) {
                break;
            }
            const cir::ObjCInterfaceFacts* facts =
                file_.objc_interface_facts(current);
            current = facts ? facts->super_class : cir::EntityId{};
        }
        if (!allowed) {
            report_error("instance variable '" + std::string(ivar_name) +
                             "' is " +
                             (found->access == cir::ObjCIvarAccess::Private
                                  ? "private"
                                  : "protected"),
                         loc);
            result.has_error = true;
        }
    }

    base = require_value(std::move(base), UseContext::RValue, loc);
    cir::Fragment fragment = std::move(base.fragment);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.ivar");
    cir::InstId inst = builder_.objc_ivar_addr(
        base.value, found->entity, builder_.place_type(found->type), loc);
    cir::Fragment ivar_fragment = finish_fragment_block(block, previous);
    result.fragment = chain(std::move(fragment), std::move(ivar_fragment),
                            loc);
    result.place = inst;
    result.type = found->type.type;
    result.category = ValueCategory::LValue;
    return result;
}

ObjCInterfaceDeclResult Session::declare_objc_protocol_forward(
    std::string_view name, SrcLoc loc) {
    ObjCInterfaceDeclResult result;
    auto found = objc_.protocols.find(std::string(name));
    if (found != objc_.protocols.end()) {
        result.entity = found->second;
        return result;
    }
    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::ObjCProtocol, name, {}, {}, loc);
    cir::ObjCInterfaceFacts facts;
    facts.name = file_.intern_name(name);
    facts.is_forward_only = true;
    facts.loc = loc;
    file_.set_objc_interface_facts(entity, std::move(facts));
    objc_.protocols.emplace(std::string(name), entity);
    result.entity = entity;
    return result;
}

ObjCInterfaceDeclResult Session::begin_objc_protocol(
    std::string_view name,
    const std::vector<std::string>& inherited,
    SrcLoc loc) {
    ObjCInterfaceDeclResult result = declare_objc_protocol_forward(name, loc);
    cir::ObjCInterfaceFacts* facts =
        file_.objc_interface_facts_mut(result.entity);
    if (!facts) {
        result.has_error = true;
        return result;
    }

    facts->is_forward_only = false;
    facts->is_defined = true;
    facts->loc = loc;
    for (const std::string& base : inherited) {
        ObjCInterfaceDeclResult inherited_protocol =
            declare_objc_protocol_forward(base, loc);
        facts = file_.objc_interface_facts_mut(result.entity);
        if (std::find(facts->protocols.begin(), facts->protocols.end(),
                      inherited_protocol.entity) == facts->protocols.end()) {
            facts->protocols.push_back(inherited_protocol.entity);
        }
    }
    return result;
}

void Session::finish_objc_protocol(cir::EntityId protocol, SrcLoc loc) {
    (void)protocol;
    (void)loc;
}

cir::EntityId Session::begin_objc_category(std::string_view class_name,
                                           std::string_view category_name,
                                           SrcLoc loc) {
    (void)category_name;

    auto found = objc_.classes.find(std::string(class_name));
    if (found == objc_.classes.end()) {

        return declare_objc_class_forward(class_name, loc).entity;
    }
    return found->second;
}

void Session::set_objc_container_protocols(
    cir::EntityId container,
    const std::vector<std::string>& protocol_names,
    SrcLoc loc) {
    for (const std::string& name : protocol_names) {
        ObjCInterfaceDeclResult protocol =
            declare_objc_protocol_forward(name, loc);
        cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts_mut(container);
        if (!facts) {
            return;
        }
        if (std::find(facts->protocols.begin(), facts->protocols.end(),
                      protocol.entity) == facts->protocols.end()) {
            facts->protocols.push_back(protocol.entity);
        }
    }
}

bool Session::is_objc_protocol_name(std::string_view name) const {
    return objc_.protocols.find(std::string(name)) != objc_.protocols.end();
}

cir::EntityId Session::declare_objc_property(cir::EntityId container,
                                             ObjCPropertyInput& property) {
    cir::ObjCInterfaceFacts* facts =
        file_.objc_interface_facts_mut(container);
    if (!facts) {
        return {};
    }
    cir::ObjCPropertyFact fact;
    fact.entity = builder_.add_entity(cir::EntityKind::ObjCProperty,
                                      property.name,
                                      property.type.type,
                                      container,
                                      property.loc);
    fact.name = file_.intern_name(property.name);
    fact.type = property.type;
    fact.ownership = property.ownership;
    fact.is_readonly = property.is_readonly;
    fact.is_class_property = property.is_class_property;
    fact.is_nonatomic = property.is_nonatomic;
    fact.attributes = property.attrs.attrs;
    fact.loc = property.loc;

    std::string getter_name =
        property.getter.empty() ? property.name : property.getter;
    std::string setter_name = property.setter;
    if (setter_name.empty() && !property.is_readonly) {
        setter_name = "set" + property.name + ":";
        if (setter_name.size() > 4 && setter_name[3] >= 'a' &&
            setter_name[3] <= 'z') {
            setter_name[3] =
                static_cast<char>(setter_name[3] - 'a' + 'A');
        }
    }
    fact.getter = file_.intern_selector(getter_name);
    if (!setter_name.empty()) {
        fact.setter = file_.intern_selector(setter_name);
    }

    ObjCMethodInput getter_method;
    getter_method.selector = getter_name;
    getter_method.is_class_method = property.is_class_property;
    getter_method.return_type = property.type;
    getter_method.loc = property.loc;
    fact.getter_method = declare_objc_method(container, getter_method);
    if (const cir::ObjCMethodFact* accessor = find_objc_method(
            container, fact.getter, property.is_class_property)) {
        const_cast<cir::ObjCMethodFact*>(accessor)->is_property_accessor =
            true;
    }
    if (!setter_name.empty()) {
        ObjCMethodInput setter_method;
        setter_method.selector = setter_name;
        setter_method.is_class_method = property.is_class_property;
        setter_method.return_type =
            type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void));
        ParamInput value_param;
        value_param.name = property.name;
        value_param.type = property.type;
        value_param.loc = property.loc;
        setter_method.params.push_back(std::move(value_param));
        setter_method.loc = property.loc;
        fact.setter_method = declare_objc_method(container, setter_method);
    }

    facts = file_.objc_interface_facts_mut(container);
    cir::EntityId entity = fact.entity;
    facts->properties.push_back(std::move(fact));
    return entity;
}

void Session::push_objc_type_parameters(std::vector<std::string> names) {
    objc_.type_param_stack.push_back(std::move(names));
}

void Session::pop_objc_type_parameters() {
    if (!objc_.type_param_stack.empty()) {
        objc_.type_param_stack.pop_back();
    }
}

bool Session::objc_type_accepts_angle_suffix(std::string_view name) const {
    if (!objc_.initialized) {
        return false;
    }
    if (name == "id" || name == "Class") {
        return true;
    }
    if (is_objc_class_name(name)) {
        return true;
    }
    for (const std::vector<std::string>& frame : objc_.type_param_stack) {
        for (const std::string& parameter : frame) {
            if (parameter == name) {
                return true;
            }
        }
    }
    return false;
}

ExprResult Session::collect_objc_property_reference(ExprResult base,
                                                    cir::EntityId interface,
                                                    std::string_view name,
                                                    SrcLoc loc) {

    const cir::ObjCPropertyFact* property = nullptr;
    for (cir::EntityId current = interface; current.valid();) {
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(current);
        if (!facts) {
            break;
        }
        cir::NameId name_id = file_.intern_name(name);
        for (const cir::ObjCPropertyFact& candidate : facts->properties) {
            if (candidate.name == name_id) {
                property = &candidate;
                break;
            }
        }
        if (property) {
            break;
        }
        for (cir::EntityId protocol : facts->protocols) {
            const cir::ObjCInterfaceFacts* protocol_facts =
                file_.objc_interface_facts(protocol);
            if (!protocol_facts) {
                continue;
            }
            for (const cir::ObjCPropertyFact& candidate :
                 protocol_facts->properties) {
                if (candidate.name == name_id) {
                    property = &candidate;
                    break;
                }
            }
            if (property) {
                break;
            }
        }
        if (property) {
            break;
        }
        current = facts->super_class;
    }

    auto reference = std::make_shared<ObjCPropertyReference>();
    reference->interface = interface;
    if (property) {
        reference->getter = std::string(file_.selector_spelling(property->getter));
        if (property->setter.valid()) {
            reference->setter =
                std::string(file_.selector_spelling(property->setter));
        }
        reference->type = property->type.type;
    } else {

        cir::SelectorId getter_selector = file_.intern_selector(name);
        const cir::ObjCMethodFact* getter =
            find_objc_method(interface, getter_selector, false);
        if (!getter) {
            report_error("no property or getter '" + std::string(name) +
                             "' on the receiver's class",
                         loc);
            ExprResult result;
            result.fragment = std::move(base.fragment);
            result.type = file_.unknown_type();
            result.category = ValueCategory::PrValue;
            result.has_error = true;
            return result;
        }
        reference->getter = std::string(name);
        std::string setter = "set" + std::string(name) + ":";
        if (setter.size() > 4 && setter[3] >= 'a' && setter[3] <= 'z') {
            setter[3] = static_cast<char>(setter[3] - 'a' + 'A');
        }
        if (find_objc_method(interface, file_.intern_selector(setter),
                             false)) {
            reference->setter = setter;
        }
        reference->type = getter->return_type.type.valid()
                              ? getter->return_type.type
                              : objc_.id_type;
    }

    ExprResult result;
    result.objc_property = std::move(reference);
    result.objc_property->receiver =
        std::make_shared<ExprResult>(std::move(base));
    result.type = result.objc_property->type;
    result.category = ValueCategory::PrValue;
    return result;
}

ExprResult Session::resolve_objc_property_load(ExprResult expr, SrcLoc loc) {
    std::shared_ptr<ObjCPropertyReference> reference =
        std::move(expr.objc_property);
    expr.objc_property.reset();
    ObjCMessageSendInput send;
    send.receiver = std::move(*reference->receiver);
    send.selector = reference->getter;
    if (reference->subscript_index) {
        send.args.push_back(std::move(*reference->subscript_index));
    }
    send.loc = loc;
    ExprResult sent = collect_objc_message_send(std::move(send));
    sent.fragment = chain(std::move(expr.fragment), std::move(sent.fragment),
                          loc);
    sent.has_error = sent.has_error || expr.has_error;
    return sent;
}

void Session::collect_objc_synthesize(cir::EntityId interface,
                                      std::string_view property_name,
                                      std::string_view backing_name,
                                      bool is_dynamic,
                                      SrcLoc loc) {
    cir::NameId name = file_.intern_name(property_name);
    for (cir::EntityId current = interface; current.valid();) {
        cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts_mut(current);
        if (!facts) {
            break;
        }
        for (cir::ObjCPropertyFact& property : facts->properties) {
            if (property.name == name) {
                property.is_dynamic = is_dynamic;
                if (!backing_name.empty()) {
                    property.spelled_backing_name =
                        file_.intern_name(backing_name);
                } else if (!is_dynamic) {
                    property.spelled_backing_name =
                        file_.intern_name(property_name);
                }
                return;
            }
        }
        current = facts->super_class;
    }
    report_error("@synthesize names an unknown property '" +
                     std::string(property_name) + "'",
                 loc);
}

ExprResult Session::collect_objc_protocol_expr(std::string_view name,
                                               SrcLoc loc) {
    ObjCInterfaceDeclResult protocol = declare_objc_protocol_forward(name, loc);
    cir::ObjCInterfaceFacts* facts =
        file_.objc_interface_facts_mut(protocol.entity);
    if (!facts->protocol_reference.valid()) {

        cir::EntityId slot = builder_.add_entity(
            cir::EntityKind::Variable,
            "_OBJC_PROTOCOL_REFERENCE_$_" + std::string(name),
            pointer_type(type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void))),
            protocol.entity,
            loc,
            cir::StorageDuration::Static,
            cir::MemorySpace::Default,
            {});
        file_.entity_mut(slot).is_definition = true;
        file_.entity_mut(slot).linkage = cir::LinkageKind::Internal;
        facts = file_.objc_interface_facts_mut(protocol.entity);
        facts->protocol_reference = slot;
    }
    cir::EntityId slot = facts->protocol_reference;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.protocol");
    cir::InstId place = builder_.global_place(slot, loc);
    cir::InstId value = builder_.load(place, loc);
    cir::Fragment fragment = finish_fragment_block(block, previous);

    ExprResult result;
    result.fragment = std::move(fragment);
    result.value = value;
    result.type = objc_.id_type;
    result.category = ValueCategory::PrValue;
    return result;
}

StmtResult Session::collect_objc_throw_stmt(std::optional<ExprResult> operand,
                                            SrcLoc loc) {
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_ptr = pointer_type(type_ref(void_type));
    StmtResult result;
    cir::Fragment fragment;
    cir::InstId value{};
    if (operand.has_value()) {
        ExprResult thrown = require_value(std::move(*operand),
                                          UseContext::RValue, loc);
        fragment = std::move(thrown.fragment);
        value = thrown.value;
        result.has_error = thrown.has_error;
    }
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.throw");
    if (operand.has_value()) {
        cir::EntityId callee = extern_runtime_function(
            "objc_exception_throw",
            file_.function_type(void_type, {void_ptr}), loc);
        cir::InstId cast_value =
            builder_.cast(void_ptr, value, "arith", loc);
        (void)builder_.call(callee, void_type, {cast_value}, loc);
    } else {
        cir::EntityId callee = extern_runtime_function(
            "objc_exception_rethrow", file_.function_type(void_type, {}),
            loc);
        (void)builder_.call(callee, void_type, {}, loc);
    }
    builder_.unreachable(loc);
    cir::Fragment throw_fragment = finish_fragment_block(block, previous);
    throw_fragment.falls_through = false;
    result.fragment = chain(std::move(fragment), std::move(throw_fragment),
                            loc);
    result.fragment.falls_through = false;
    result.falls_through = false;
    return result;
}

StmtResult Session::collect_objc_autoreleasepool(StmtResult body, SrcLoc loc) {
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_ptr = pointer_type(type_ref(void_type));
    cir::EntityId push = extern_runtime_function(
        "objc_autoreleasePoolPush", file_.function_type(void_ptr, {}), loc);
    cir::EntityId pop = extern_runtime_function(
        "objc_autoreleasePoolPop",
        file_.function_type(void_type, {void_ptr}), loc);

    cir::BlockId previous = builder_.current_block();
    cir::BlockId push_block = begin_fragment_block("objc.pool.push");
    cir::InstId token = builder_.call(push, void_ptr, {}, loc);
    cir::Fragment push_fragment = finish_fragment_block(push_block, previous);

    StmtResult result;
    result.fragment = chain(std::move(push_fragment),
                            std::move(body.fragment), loc);
    if (body.falls_through) {
        cir::BlockId pop_previous = builder_.current_block();
        cir::BlockId pop_block = begin_fragment_block("objc.pool.pop");
        (void)builder_.call(pop, void_type, {token}, loc);
        cir::Fragment pop_fragment =
            finish_fragment_block(pop_block, pop_previous);
        result.fragment = chain(std::move(result.fragment),
                                std::move(pop_fragment), loc);
    }
    result.falls_through = body.falls_through;
    result.has_error = body.has_error;
    result.break_exits = std::move(body.break_exits);
    result.continue_exits = std::move(body.continue_exits);
    return result;
}

cir::EntityId Session::objc_ehtype_entity(cir::EntityId interface,
                                          SrcLoc loc) {
    cir::ObjCInterfaceFacts* facts = file_.objc_interface_facts_mut(interface);
    if (!facts) {
        return {};
    }
    if (facts->ehtype.valid()) {
        return facts->ehtype;
    }
    std::string symbol =
        "OBJC_EHTYPE_$_" + std::string(file_.name(facts->name));
    cir::EntityId entity = builder_.add_entity(
        cir::EntityKind::Variable, symbol,
        pointer_type(type_ref(file_.builtin_type(cir::BuiltinTypeKind::Void))),
        interface, loc, cir::StorageDuration::Static,
        cir::MemorySpace::Default, {});
    file_.entity_mut(entity).is_definition = false;
    file_.entity_mut(entity).linkage = cir::LinkageKind::External;
    facts = file_.objc_interface_facts_mut(interface);
    facts->ehtype = entity;
    return entity;
}

namespace {

std::string number_selector_for(const cir::File& file, cir::TypeId type) {
    cir::TypeId resolved = file.resolved_type(type);
    if (!file.valid(resolved) ||
        file.type(resolved).kind != cir::TypeKind::Builtin) {
        return "numberWithInt:";
    }
    const auto* payload =
        std::get_if<cir::BuiltinTypePayload>(&file.type_payload(resolved));
    if (!payload) {
        return "numberWithInt:";
    }
    switch (payload->kind) {
        case cir::BuiltinTypeKind::Bool: return "numberWithBool:";
        case cir::BuiltinTypeKind::Char:
        case cir::BuiltinTypeKind::SChar: return "numberWithChar:";
        case cir::BuiltinTypeKind::UChar: return "numberWithUnsignedChar:";
        case cir::BuiltinTypeKind::Char8: return "numberWithUnsignedChar:";
        case cir::BuiltinTypeKind::Short: return "numberWithShort:";
        case cir::BuiltinTypeKind::UShort: return "numberWithUnsignedShort:";
        case cir::BuiltinTypeKind::Int: return "numberWithInt:";
        case cir::BuiltinTypeKind::UInt: return "numberWithUnsignedInt:";
        case cir::BuiltinTypeKind::Long: return "numberWithLong:";
        case cir::BuiltinTypeKind::ULong: return "numberWithUnsignedLong:";
        case cir::BuiltinTypeKind::LongLong: return "numberWithLongLong:";
        case cir::BuiltinTypeKind::ULongLong:
            return "numberWithUnsignedLongLong:";
        case cir::BuiltinTypeKind::Float: return "numberWithFloat:";
        case cir::BuiltinTypeKind::Double:
        case cir::BuiltinTypeKind::LongDouble: return "numberWithDouble:";
        default: return "numberWithInt:";
    }
}

} // namespace

ExprResult Session::collect_objc_box_expr(ExprResult value, SrcLoc loc) {
    cir::TypeId resolved = file_.resolved_type(value.type);

    bool is_char_pointer = false;
    if (file_.valid(resolved) &&
        file_.type(resolved).kind == cir::TypeKind::Pointer) {
        cir::TypeId pointee =
            file_.resolved_type(file_.pointer_pointee_ref(resolved).type);
        if (file_.valid(pointee) &&
            file_.type(pointee).kind == cir::TypeKind::Builtin) {
            const auto* payload = std::get_if<cir::BuiltinTypePayload>(
                &file_.type_payload(pointee));
            is_char_pointer = payload &&
                (payload->kind == cir::BuiltinTypeKind::Char ||
                 payload->kind == cir::BuiltinTypeKind::SChar ||
                 payload->kind == cir::BuiltinTypeKind::UChar);
        }
    }
    std::string class_name = is_char_pointer ? "NSString" : "NSNumber";
    if (!objc_class_entity(class_name).valid()) {
        report_error("@-boxing requires '" + class_name +
                         "' to be declared", loc);
        value.has_error = true;
        return value;
    }
    ObjCMessageSendInput send;
    send.receiver_class = objc_class_entity(class_name);
    send.selector = is_char_pointer ? "stringWithUTF8String:"
                                    : number_selector_for(file_, value.type);
    send.args.push_back(std::move(value));
    send.loc = loc;
    return collect_objc_message_send(std::move(send));
}

ExprResult Session::collect_objc_array_literal(
    std::vector<ExprResult> elements, SrcLoc loc) {
    if (!objc_class_entity("NSArray").valid()) {
        report_error("array literals require 'NSArray' to be declared", loc);
        ExprResult result;
        result.type = objc_.id_type;
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }

    cir::TypeId array_type =
        file_.array_type(objc_.id_type, elements.size());
    cir::EntityId storage = builder_.add_entity(
        cir::EntityKind::Variable, "", array_type, {}, loc,
        cir::StorageDuration::Automatic);
    file_.entity_mut(storage).is_definition = true;
    cir::Fragment fragment;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.array.build");
    cir::InstId array_place = builder_.local_place(storage, array_type, loc);
    for (size_t i = 0; i < elements.size(); ++i) {
        ExprResult element = require_value(std::move(elements[i]),
                                           UseContext::RValue, loc);
        fragment = chain(std::move(fragment), std::move(element.fragment), loc);
        cir::InstId index =
            builder_.integer_literal(static_cast<int64_t>(i),
                                     file_.builtin_type(
                                         cir::BuiltinTypeKind::ULong),
                                     std::to_string(i), loc);
        cir::InstId slot = builder_.array_element_place(array_place, index,
                                                        loc);
        cir::InstId converted =
            builder_.cast(objc_.id_type, element.value, "arith", loc);
        (void)builder_.store(slot, converted, loc);
    }
    cir::InstId base = builder_.array_element_place(
        array_place,
        builder_.integer_literal(0, file_.builtin_type(
                                        cir::BuiltinTypeKind::ULong),
                                 "0", loc),
        loc);
    cir::InstId base_ptr = builder_.addr_of(base, loc);
    cir::Fragment build_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(build_fragment), loc);

    ObjCMessageSendInput send;
    send.receiver_class = objc_class_entity("NSArray");
    send.selector = "arrayWithObjects:count:";
    ExprResult objects;
    objects.value = base_ptr;
    objects.type = pointer_type(type_ref(objc_.id_type));
    objects.category = ValueCategory::PrValue;
    ExprResult count = make_integer_literal(
        static_cast<int64_t>(elements.size()), std::to_string(elements.size()),
        file_.builtin_type(cir::BuiltinTypeKind::ULong), loc);
    send.args.push_back(std::move(objects));
    send.args.push_back(std::move(count));
    send.loc = loc;
    ExprResult result = collect_objc_message_send(std::move(send));
    result.fragment = chain(std::move(fragment), std::move(result.fragment),
                            loc);
    return result;
}

ExprResult Session::collect_objc_dictionary_literal(
    std::vector<std::pair<ExprResult, ExprResult>> entries, SrcLoc loc) {
    if (!objc_class_entity("NSDictionary").valid()) {
        report_error("dictionary literals require 'NSDictionary' to be "
                     "declared", loc);
        ExprResult result;
        result.type = objc_.id_type;
        result.category = ValueCategory::PrValue;
        result.has_error = true;
        return result;
    }
    cir::TypeId array_type = file_.array_type(objc_.id_type, entries.size());
    auto make_storage = [&]() {
        cir::EntityId storage = builder_.add_entity(
            cir::EntityKind::Variable, "", array_type, {}, loc,
            cir::StorageDuration::Automatic);
        file_.entity_mut(storage).is_definition = true;
        return storage;
    };
    cir::EntityId objects_storage = make_storage();
    cir::EntityId keys_storage = make_storage();
    cir::Fragment fragment;
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.dict.build");
    cir::InstId objects_place =
        builder_.local_place(objects_storage, array_type, loc);
    cir::InstId keys_place =
        builder_.local_place(keys_storage, array_type, loc);
    auto ulong = [&](size_t v) {
        return builder_.integer_literal(
            static_cast<int64_t>(v),
            file_.builtin_type(cir::BuiltinTypeKind::ULong),
            std::to_string(v), loc);
    };
    for (size_t i = 0; i < entries.size(); ++i) {
        ExprResult key = require_value(std::move(entries[i].first),
                                       UseContext::RValue, loc);
        fragment = chain(std::move(fragment), std::move(key.fragment), loc);
        (void)builder_.store(
            builder_.array_element_place(keys_place, ulong(i), loc),
            builder_.cast(objc_.id_type, key.value, "arith", loc), loc);
        ExprResult val = require_value(std::move(entries[i].second),
                                       UseContext::RValue, loc);
        fragment = chain(std::move(fragment), std::move(val.fragment), loc);
        (void)builder_.store(
            builder_.array_element_place(objects_place, ulong(i), loc),
            builder_.cast(objc_.id_type, val.value, "arith", loc), loc);
    }
    cir::InstId objects_ptr = builder_.addr_of(
        builder_.array_element_place(objects_place, ulong(0), loc), loc);
    cir::InstId keys_ptr = builder_.addr_of(
        builder_.array_element_place(keys_place, ulong(0), loc), loc);
    cir::Fragment build_fragment = finish_fragment_block(block, previous);
    fragment = chain(std::move(fragment), std::move(build_fragment), loc);

    ObjCMessageSendInput send;
    send.receiver_class = objc_class_entity("NSDictionary");
    send.selector = "dictionaryWithObjects:forKeys:count:";
    auto ptr_arg = [&](cir::InstId ptr) {
        ExprResult arg;
        arg.value = ptr;
        arg.type = pointer_type(type_ref(objc_.id_type));
        arg.category = ValueCategory::PrValue;
        return arg;
    };
    send.args.push_back(ptr_arg(objects_ptr));
    send.args.push_back(ptr_arg(keys_ptr));
    send.args.push_back(make_integer_literal(
        static_cast<int64_t>(entries.size()),
        std::to_string(entries.size()),
        file_.builtin_type(cir::BuiltinTypeKind::ULong), loc));
    send.loc = loc;
    ExprResult result = collect_objc_message_send(std::move(send));
    result.fragment = chain(std::move(fragment), std::move(result.fragment),
                            loc);
    return result;
}

ObjCSynchronizedControl Session::begin_objc_synchronized(ExprResult object,
                                                         SrcLoc loc) {
    ObjCSynchronizedControl control;
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_ptr = pointer_type(type_ref(void_type));
    ExprResult value = require_value(std::move(object), UseContext::RValue,
                                     loc);
    control.has_error = value.has_error;
    cir::Fragment prologue = std::move(value.fragment);
    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.sync.enter");
    control.object = builder_.cast(void_ptr, value.value, "arith", loc);
    cir::EntityId enter = extern_runtime_function(
        "objc_sync_enter",
        file_.function_type(file_.builtin_type(cir::BuiltinTypeKind::Int),
                            {void_ptr}),
        loc);
    (void)builder_.call(enter,
                        file_.builtin_type(cir::BuiltinTypeKind::Int),
                        {control.object}, loc);
    cir::Fragment enter_fragment = finish_fragment_block(block, previous);
    control.prologue = chain(std::move(prologue), std::move(enter_fragment),
                             loc);
    control.try_control = begin_try(loc);
    return control;
}

StmtResult Session::finish_objc_synchronized(ObjCSynchronizedControl& control,
                                             StmtResult body,
                                             SrcLoc loc) {
    cir::TypeId void_type = file_.builtin_type(cir::BuiltinTypeKind::Void);
    cir::TypeId void_ptr = pointer_type(type_ref(void_type));
    cir::EntityId exit = extern_runtime_function(
        "objc_sync_exit",
        file_.function_type(file_.builtin_type(cir::BuiltinTypeKind::Int),
                            {void_ptr}),
        loc);
    auto make_exit_fragment = [&]() {
        cir::BlockId previous = builder_.current_block();
        cir::BlockId block = begin_fragment_block("objc.sync.exit");
        (void)builder_.call(exit,
                            file_.builtin_type(cir::BuiltinTypeKind::Int),
                            {control.object}, loc);
        return finish_fragment_block(block, previous);
    };

    finish_try_body(control.try_control, std::move(body));

    begin_catch_handler(control.try_control, std::nullopt, "", loc);
    StmtResult handler;
    handler.fragment = make_exit_fragment();
    StmtResult rethrow = collect_objc_throw_stmt(std::nullopt, loc);
    handler.fragment = chain(std::move(handler.fragment),
                             std::move(rethrow.fragment), loc);
    handler.fragment.falls_through = false;
    handler.falls_through = false;
    finish_catch_handler(control.try_control, std::move(handler), loc);

    StmtResult result = finish_try(control.try_control, loc);
    result.fragment = chain(std::move(control.prologue),
                            std::move(result.fragment), loc);
    if (result.falls_through) {
        result.fragment = chain(std::move(result.fragment),
                                make_exit_fragment(), loc);
    }
    result.has_error = result.has_error || control.has_error;
    return result;
}

ObjCForInControl Session::begin_objc_for_in(std::string_view loop_var_name,
                                            cir::TypeRef loop_var_type,
                                            ExprResult collection,
                                            SrcLoc loc) {
    enter_scope(ScopeFlags::BlockScope | ScopeFlags::LoopScope);
    ObjCForInControl control;
    control.loc = loc;
    cir::TypeId ulong_type = file_.builtin_type(cir::BuiltinTypeKind::ULong);
    cir::TypeId id_ptr_type = pointer_type(type_ref(objc_.id_type));

    ExprResult value = require_value(std::move(collection),
                                     UseContext::RValue, loc);
    control.has_error = value.has_error;
    cir::TypeId collection_type = file_.resolved_type(value.type);
    bool object_pointer = file_.valid(collection_type) &&
        file_.type(collection_type).kind == cir::TypeKind::Pointer;
    if (object_pointer) {
        cir::TypeId pointee = file_.resolved_type(
            file_.pointer_pointee_type(collection_type));
        object_pointer = objc_interface_for_object_type(pointee).valid() ||
            (file_.valid(pointee) &&
             pointee == file_.resolved_type(objc_id_pointee_type()));
    }
    if (!object_pointer && !control.has_error) {
        report_error("the collection in a for-in statement must be an "
                     "Objective-C object", loc);
        control.has_error = true;
    }
    control.prologue = std::move(value.fragment);

    DeclResult loop_var = declare_local_variable(loop_var_name,
                                                 loop_var_type.type,
                                                 std::nullopt, loc);
    control.has_error = control.has_error || loop_var.has_error;
    control.prologue = chain(std::move(control.prologue),
                             std::move(loop_var.fragment), loc);

    auto automatic_storage = [&](cir::TypeId type) {
        cir::EntityId storage = builder_.add_entity(
            cir::EntityKind::Variable, "", type, {}, loc,
            cir::StorageDuration::Automatic);
        file_.entity_mut(storage).is_definition = true;
        return storage;
    };
    cir::TypeId state_type = file_.array_type(objc_.id_type, 8);
    cir::TypeId buffer_type = file_.array_type(objc_.id_type, 16);
    cir::EntityId state = automatic_storage(state_type);
    cir::EntityId buffer = automatic_storage(buffer_type);
    cir::EntityId index_var = automatic_storage(ulong_type);
    cir::EntityId limit_var = automatic_storage(ulong_type);

    auto ulong_literal = [&](int64_t v) {
        return builder_.integer_literal(v, ulong_type, std::to_string(v), loc);
    };

    cir::BlockId previous = builder_.current_block();
    cir::BlockId block = begin_fragment_block("objc.forin.begin");
    cir::InstId receiver = builder_.cast(objc_.id_type, value.value, "arith",
                                         loc);
    (void)builder_.zero_object(builder_.local_place(state, state_type, loc),
                               loc);
    (void)builder_.store(builder_.local_place(index_var, ulong_type, loc),
                         ulong_literal(0), loc);
    (void)builder_.store(builder_.local_place(limit_var, ulong_type, loc),
                         ulong_literal(0), loc);
    control.prologue = chain(std::move(control.prologue),
                             finish_fragment_block(block, previous), loc);

    previous = builder_.current_block();
    block = begin_fragment_block("objc.forin.cond");
    cir::InstId index_value = builder_.load(
        builder_.local_place(index_var, ulong_type, loc), loc);
    cir::InstId limit_value = builder_.load(
        builder_.local_place(limit_var, ulong_type, loc), loc);
    control.condition_value = builder_.binary(cir::BinaryOpKind::Less,
                                              builder_.bool_type(),
                                              index_value, limit_value, loc);
    control.condition = finish_fragment_block(block, previous);

    previous = builder_.current_block();
    block = begin_fragment_block("objc.forin.refill");
    cir::InstId state_ptr = builder_.cast(
        objc_.id_type,
        builder_.addr_of(
            builder_.array_element_place(
                builder_.local_place(state, state_type, loc),
                ulong_literal(0), loc),
            loc),
        "arith", loc);
    cir::InstId buffer_ptr = builder_.cast(
        id_ptr_type,
        builder_.addr_of(
            builder_.array_element_place(
                builder_.local_place(buffer, buffer_type, loc),
                ulong_literal(0), loc),
            loc),
        "arith", loc);
    cir::ObjCMessageSendPayload send;
    send.selector =
        file_.intern_selector("countByEnumeratingWithState:objects:count:");
    send.receiver_kind = cir::ObjCReceiverKind::Instance;
    cir::InstId fetched = builder_.objc_message_send(
        send, {receiver, state_ptr, buffer_ptr, ulong_literal(16)},
        ulong_type, loc);
    (void)builder_.store(builder_.local_place(limit_var, ulong_type, loc),
                         fetched, loc);
    (void)builder_.store(builder_.local_place(index_var, ulong_type, loc),
                         ulong_literal(0), loc);
    control.refill_empty_value = builder_.binary(cir::BinaryOpKind::Equal,
                                                 builder_.bool_type(),
                                                 fetched, ulong_literal(0),
                                                 loc);
    control.refill = finish_fragment_block(block, previous);

    previous = builder_.current_block();
    block = begin_fragment_block("objc.forin.prep");
    cir::InstId items = builder_.cast(
        id_ptr_type,
        builder_.load(
            builder_.array_element_place(
                builder_.local_place(state, state_type, loc),
                ulong_literal(1), loc),
            loc),
        "arith", loc);
    cir::InstId current_index = builder_.load(
        builder_.local_place(index_var, ulong_type, loc), loc);
    cir::InstId slot_address = builder_.binary(
        cir::BinaryOpKind::Add, ulong_type,
        builder_.cast(ulong_type, items, "arith", loc),
        builder_.binary(cir::BinaryOpKind::Mul, ulong_type, current_index,
                        ulong_literal(8), loc),
        loc);
    cir::InstId element = builder_.load(
        builder_.deref(builder_.cast(id_ptr_type, slot_address, "arith", loc),
                       loc),
        loc);
    if (file_.valid(loop_var.entity)) {
        cir::InstId converted = file_.valid(loop_var_type.type)
            ? builder_.cast(loop_var_type.type, element, "arith", loc)
            : element;
        (void)builder_.store(
            builder_.local_place(loop_var.entity, loop_var_type.type, loc),
            converted, loc);
    }
    control.prepare = finish_fragment_block(block, previous);

    previous = builder_.current_block();
    block = begin_fragment_block("objc.forin.next");
    cir::InstId step_index = builder_.load(
        builder_.local_place(index_var, ulong_type, loc), loc);
    (void)builder_.store(
        builder_.local_place(index_var, ulong_type, loc),
        builder_.binary(cir::BinaryOpKind::Add, ulong_type, step_index,
                        ulong_literal(1), loc),
        loc);
    control.step = finish_fragment_block(block, previous);

    control.continuation_block =
        builder_.create_detached_block("objc.forin.end");
    control_stack_.push_back(ControlTargets{
        ControlKind::Loop,
        control.step.entry,
        control.continuation_block});
    return control;
}

StmtResult Session::finish_objc_for_in(ObjCForInControl& control,
                                       const StmtResult& body,
                                       SrcLoc loc) {
    if (!control_stack_.empty()) {
        control_stack_.pop_back();
    }
    leave_scope();

    cir::BlockId condition_entry = control.condition.entry;
    cir::BlockId prepare_entry = control.prepare.entry;
    cir::Fragment fragment = chain(std::move(control.prologue),
                                   std::move(control.condition), loc);
    builder_.cond_branch_from(fragment.exit, control.condition_value,
                              prepare_entry, control.refill.entry, {}, loc);

    append_fragment_blocks(fragment, control.refill);
    builder_.cond_branch_from(control.refill.exit, control.refill_empty_value,
                              control.continuation_block, prepare_entry, {},
                              loc);

    append_fragment_blocks(fragment, control.prepare);
    if (body.fragment.empty()) {
        builder_.branch_from(control.prepare.exit, control.step.entry, {},
                             loc);
    } else {
        builder_.branch_from(control.prepare.exit, body.fragment.entry, {},
                             loc);
        append_fragment_blocks(fragment, body.fragment);
        if (body.falls_through &&
            !builder_.block_terminated(body.fragment.exit)) {
            builder_.branch_from(body.fragment.exit, control.step.entry, {},
                                 loc);
        }
    }

    append_fragment_blocks(fragment, control.step);
    builder_.branch_from(control.step.exit, condition_entry, {}, loc);

    append_fragment_blocks(fragment,
                           builder_.block_fragment(control.continuation_block));
    fragment.exit = control.continuation_block;
    fragment.falls_through = true;

    StmtResult result = make_stmt_result(std::move(fragment), false,
                                         control.has_error || body.has_error);
    result.contains_switch_label = body.contains_switch_label;
    return result;
}

ExprResult Session::collect_objc_subscript_reference(ExprResult base,
                                                     ExprResult index,
                                                     SrcLoc loc) {

    cir::TypeId index_type = file_.resolved_type(index.type);
    bool keyed = file_.valid(index_type) &&
                 file_.type(index_type).kind == cir::TypeKind::Pointer;
    auto reference = std::make_shared<ObjCPropertyReference>();
    reference->getter =
        keyed ? "objectForKeyedSubscript:" : "objectAtIndexedSubscript:";
    reference->setter =
        keyed ? "setObject:forKeyedSubscript:" : "setObject:atIndexedSubscript:";
    reference->type = objc_.id_type;
    reference->receiver = std::make_shared<ExprResult>(std::move(base));
    reference->subscript_index =
        std::make_shared<ExprResult>(std::move(index));

    ExprResult result;
    result.objc_property = std::move(reference);
    result.type = objc_.id_type;
    result.category = ValueCategory::PrValue;
    return result;
}

} // namespace aburi::collect
