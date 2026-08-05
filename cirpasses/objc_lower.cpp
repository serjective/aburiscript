

#include "objc_lower.h"

#include <algorithm>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

#include "../abi/objc_runtime.h"
#include "../cir/builder.h"
#include "../cir/layout.h"

namespace aburi::cirpasses {

namespace {

using aburi::objc_runtime::MsgSendVariant;

void write_u32(std::vector<uint8_t>& bytes, size_t offset, uint32_t value) {
    for (size_t i = 0; i < 4; ++i) {
        bytes[offset + i] = static_cast<uint8_t>((value >> (i * 8)) & 0xff);
    }
}

void write_u64(std::vector<uint8_t>& bytes, size_t offset, uint64_t value) {
    for (size_t i = 0; i < 8; ++i) {
        bytes[offset + i] = static_cast<uint8_t>((value >> (i * 8)) & 0xff);
    }
}

class ObjCLowerer {
public:
    explicit ObjCLowerer(cir::File& file, bool arc)
        : file_(file), builder_(file), arc_(arc) {}

    bool run() {
        add_backing_ivars();
        compute_layouts();
        synthesize_accessors();
        synthesize_cxx_destruct();
        synthesize_class_metadata();
        expand_instructions();

        emit_image_tables();
        return true;
    }

private:
    cir::File& file_;
    cir::Builder builder_;
    bool arc_ = false;
    std::unordered_set<uint32_t> arc_destruct_classes_;

    std::unordered_map<uint32_t, cir::EntityId> methnames_;
    std::unordered_map<uint32_t, cir::EntityId> selrefs_;
    std::unordered_map<std::string, cir::EntityId> shared_cstrings_;
    std::unordered_map<uint64_t, cir::EntityId> classrefs_;
    std::unordered_map<uint64_t, cir::EntityId> class_objects_;
    std::unordered_map<uint64_t, cir::EntityId> metaclass_objects_;
    std::unordered_map<uint64_t, cir::EntityId> ivar_offset_vars_;
    std::unordered_map<std::string, cir::EntityId> msgsend_decls_;
    std::unordered_map<std::string, cir::EntityId> arc_decls_;
    std::unordered_map<std::string, cir::EntityId> extern_globals_;
    std::vector<cir::EntityId> defined_classes_;
    uint32_t name_counter_ = 0;
    uint32_t selref_counter_ = 0;
    uint32_t classref_counter_ = 0;
    uint32_t cfstring_counter_ = 0;

    uint64_t key(cir::EntityId id) const {
        return (static_cast<uint64_t>(id.generation) << 32) | id.index;
    }

    cir::TypeId char_type() { return file_.builtin_type(cir::BuiltinTypeKind::Char); }
    cir::TypeId ulong_type() { return file_.builtin_type(cir::BuiltinTypeKind::ULong); }

    cir::EntityId make_data_global(
        std::string_view name,
        std::vector<uint8_t> bytes,
        std::vector<cir::StaticInitializerRelocation> relocations,
        std::string_view section,
        size_t alignment,
        cir::LinkageKind linkage,
        bool used,
        cir::TypeId explicit_type = {}) {

        cir::TypeId type = explicit_type;
        if (type.valid()) {

        } else if (!relocations.empty() && bytes.size() == 8) {

            type = file_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
        } else if (!relocations.empty() && (bytes.size() % 8) == 0) {
            cir::TypeId void_ptr = file_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
            type = file_.array_type(void_ptr, bytes.size() / 8);
        } else {
            type = file_.array_type(char_type(), bytes.size());
        }
        cir::EntityId entity = builder_.add_entity(cir::EntityKind::Variable,
                                                   name,
                                                   type,
                                                   {},
                                                   SrcLoc(),
                                                   cir::StorageDuration::Static,
                                                   cir::MemorySpace::Default,
                                                   {});
        cir::Entity& record = file_.entity_mut(entity);
        record.is_definition = true;
        record.linkage = linkage;
        record.has_static_initializer = true;
        record.static_initializer_bytes = std::move(bytes);
        record.static_initializer_relocations = std::move(relocations);
        record.attr_facts.section = std::string(section);
        record.attr_facts.requested_alignment = alignment;
        record.attr_facts.is_used = used;
        return entity;
    }

    cir::EntityId make_cstring_global(std::string_view name,
                                      std::string_view content,
                                      std::string_view section) {
        std::vector<uint8_t> bytes(content.begin(), content.end());
        bytes.push_back(0);
        return make_data_global(name, std::move(bytes), {}, section, 1,
                                cir::LinkageKind::Internal, /*used=*/false);
    }

    cir::EntityId extern_global(std::string_view name) {
        auto found = extern_globals_.find(std::string(name));
        if (found != extern_globals_.end()) {
            return found->second;
        }
        cir::EntityId entity = builder_.add_entity(
            cir::EntityKind::Variable,
            name,
            file_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void)),
            {},
            SrcLoc(),
            cir::StorageDuration::Static,
            cir::MemorySpace::Default,
            {});
        file_.entity_mut(entity).is_definition = false;
        file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        extern_globals_.emplace(std::string(name), entity);
        return entity;
    }

    cir::EntityId methname(cir::SelectorId selector) {
        auto found = methnames_.find(selector.index);
        if (found != methnames_.end()) {
            return found->second;
        }
        cir::EntityId entity = make_cstring_global(
            objc_runtime::meth_var_name_symbol(name_counter_++),
            file_.selector_spelling(selector),
            objc_runtime::methname_section());
        methnames_.emplace(selector.index, entity);
        return entity;
    }

    cir::EntityId shared_cstring(std::string content, std::string_view section,
                                 std::string_view symbol_prefix) {
        std::string cache_key = std::string(section) + "\x01" + content;
        auto found = shared_cstrings_.find(cache_key);
        if (found != shared_cstrings_.end()) {
            return found->second;
        }
        std::string name = std::string(symbol_prefix) +
                           std::to_string(name_counter_++);
        cir::EntityId entity = make_cstring_global(name, content, section);
        shared_cstrings_.emplace(std::move(cache_key), entity);
        return entity;
    }

    cir::EntityId selref(cir::SelectorId selector) {
        auto found = selrefs_.find(selector.index);
        if (found != selrefs_.end()) {
            return found->second;
        }
        std::vector<uint8_t> bytes(8, 0);
        std::vector<cir::StaticInitializerRelocation> relocations;
        relocations.push_back({0, methname(selector), 0});
        cir::EntityId entity = make_data_global(
            objc_runtime::selector_ref_symbol(selref_counter_++),
            std::move(bytes), std::move(relocations),
            objc_runtime::selrefs_section(), 8, cir::LinkageKind::Internal,
            /*used=*/true);
        selrefs_.emplace(selector.index, entity);
        return entity;
    }

    std::string interface_name(cir::EntityId interface) const {
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(interface);
        return facts ? std::string(file_.name(facts->name)) : std::string();
    }

    bool interface_defined_here(cir::EntityId interface) const {
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(interface);
        return facts && facts->implementation.valid();
    }

    cir::EntityId class_object(cir::EntityId interface) {
        auto found = class_objects_.find(key(interface));
        if (found != class_objects_.end()) {
            return found->second;
        }

        cir::EntityId entity = extern_global(
            objc_runtime::class_symbol(interface_name(interface)));
        class_objects_.emplace(key(interface), entity);
        return entity;
    }

    cir::EntityId metaclass_object(cir::EntityId interface) {
        auto found = metaclass_objects_.find(key(interface));
        if (found != metaclass_objects_.end()) {
            return found->second;
        }
        cir::EntityId entity = extern_global(
            objc_runtime::metaclass_symbol(interface_name(interface)));
        metaclass_objects_.emplace(key(interface), entity);
        return entity;
    }

    cir::EntityId classref(cir::EntityId interface) {
        auto found = classrefs_.find(key(interface));
        if (found != classrefs_.end()) {
            return found->second;
        }
        std::vector<uint8_t> bytes(8, 0);
        std::vector<cir::StaticInitializerRelocation> relocations;
        relocations.push_back({0, class_object(interface), 0});
        cir::EntityId entity = make_data_global(
            objc_runtime::classlist_ref_symbol(classref_counter_++),
            std::move(bytes), std::move(relocations),
            objc_runtime::classrefs_section(), 8, cir::LinkageKind::Internal,
            /*used=*/true);
        classrefs_.emplace(key(interface), entity);
        return entity;
    }

    std::unordered_map<uint64_t, cir::EntityId> superrefs_;
    uint32_t superref_counter_ = 0;

    cir::EntityId superref(cir::EntityId interface, bool metaclass) {
        uint64_t cache_key = key(interface) ^ (metaclass ? 1u : 0u);
        auto found = superrefs_.find(cache_key);
        if (found != superrefs_.end()) {
            return found->second;
        }
        std::vector<uint8_t> bytes(8, 0);
        std::vector<cir::StaticInitializerRelocation> relocations;
        relocations.push_back(
            {0,
             metaclass ? metaclass_object(interface) : class_object(interface),
             0});
        cir::EntityId entity = make_data_global(
            objc_runtime::superclass_ref_symbol(superref_counter_++),
            std::move(bytes), std::move(relocations),
            objc_runtime::superrefs_section(), 8, cir::LinkageKind::Internal,
            /*used=*/true);
        superrefs_.emplace(cache_key, entity);
        return entity;
    }

    size_t instance_size_of(cir::EntityId interface) {
        cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts_mut(interface);
        if (!facts) {

            return 8;
        }
        if (facts->layout_computed) {
            return facts->instance_size_bytes;
        }
        size_t offset = facts->super_class.valid()
                            ? instance_size_of(facts->super_class)
                            : 8;
        size_t max_align = 8;
        bool first = true;
        for (cir::ObjCIvarFact& ivar : facts->ivars) {
            auto size_align = cir::size_align_of_type(file_, ivar.type.type);
            size_t size = size_align ? size_align->size_bytes : 8;
            size_t align = size_align ? size_align->alignment_bytes : 8;
            if (align > 1) {
                offset = (offset + align - 1) & ~(align - 1);
            }
            if (first) {
                facts->instance_start_bytes = offset;
                first = false;
            }
            ivar.offset_bytes = offset;
            offset += size;
            if (align > max_align) {
                max_align = align;
            }
        }
        if (first) {
            facts->instance_start_bytes = offset;
        }
        offset = (offset + max_align - 1) & ~(max_align - 1);
        facts->instance_size_bytes = offset;
        facts->layout_computed = true;
        return offset;
    }

    void compute_layouts() {
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            (void)instance_size_of(facts.entity);
        }
    }

    cir::EntityId ivar_offset_var(cir::EntityId ivar_entity) {
        auto found = ivar_offset_vars_.find(key(ivar_entity));
        if (found != ivar_offset_vars_.end()) {
            return found->second;
        }
        cir::EntityId interface = file_.entity(ivar_entity).parent;
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(interface);
        std::string ivar_name(file_.name(file_.entity(ivar_entity).name));
        std::string symbol = objc_runtime::ivar_offset_symbol(
            interface_name(interface), ivar_name);
        cir::EntityId entity;
        if (facts && interface_defined_here(interface)) {
            size_t offset_value = 0;
            for (const cir::ObjCIvarFact& ivar : facts->ivars) {
                if (ivar.entity == ivar_entity) {
                    offset_value = ivar.offset_bytes;
                    break;
                }
            }
            std::vector<uint8_t> bytes(8, 0);
            write_u64(bytes, 0, offset_value);
            entity = make_data_global(symbol, std::move(bytes), {},
                                      objc_runtime::objc_ivar_section(), 8,
                                      cir::LinkageKind::External,
                                      /*used=*/false, ulong_type());
        } else {
            entity = extern_global(symbol);
        }
        ivar_offset_vars_.emplace(key(ivar_entity), entity);
        return entity;
    }

    std::unordered_map<uint64_t, cir::EntityId> protocol_objects_;

    cir::EntityId protocol_method_list(const std::string& protocol_name,
                                       std::string_view flavor,
                                       const std::vector<const cir::ObjCMethodFact*>& methods) {

        std::vector<uint8_t> bytes(8 + 24 * methods.size(), 0);
        write_u32(bytes, 0, 24);
        write_u32(bytes, 4, static_cast<uint32_t>(methods.size()));
        std::vector<cir::StaticInitializerRelocation> relocations;
        size_t offset = 8;
        for (const cir::ObjCMethodFact* method : methods) {
            relocations.push_back({offset, methname(method->selector), 0});
            relocations.push_back(
                {offset + 8,
                 shared_cstring(objc_runtime::encode_method(
                                    file_, method->function_type),
                                objc_runtime::methtype_section(),
                                "OBJC_METH_VAR_TYPE_."),
                 0});
            offset += 24;
        }
        return make_data_global(
            "_OBJC_$_PROTOCOL_" + std::string(flavor) + "_" + protocol_name,
            std::move(bytes), std::move(relocations),
            objc_runtime::objc_const_section(), 8,
            cir::LinkageKind::Internal, /*used=*/false);
    }

    cir::EntityId protocol_object(cir::EntityId protocol) {
        auto found = protocol_objects_.find(key(protocol));
        if (found != protocol_objects_.end()) {
            return found->second;
        }
        const cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts(protocol);
        std::string name =
            facts ? std::string(file_.name(facts->name)) : std::string("?");

        std::vector<const cir::ObjCMethodFact*> required_instance;
        std::vector<const cir::ObjCMethodFact*> required_class;
        std::vector<const cir::ObjCMethodFact*> optional_instance;
        std::vector<const cir::ObjCMethodFact*> optional_class;
        if (facts) {
            for (const cir::ObjCMethodFact& method : facts->instance_methods) {
                (method.is_optional ? optional_instance : required_instance)
                    .push_back(&method);
            }
            for (const cir::ObjCMethodFact& method : facts->class_methods) {
                (method.is_optional ? optional_class : required_class)
                    .push_back(&method);
            }
        }

        std::vector<uint8_t> image(96, 0);
        write_u32(image, 64, 96);
        std::vector<cir::StaticInitializerRelocation> relocations;
        relocations.push_back(
            {8,
             shared_cstring(name, objc_runtime::classname_section(),
                            "OBJC_CLASS_NAME_."),
             0});
        cir::EntityId entity = make_data_global(
            "_OBJC_PROTOCOL_$_" + name, std::move(image),
            std::move(relocations), objc_runtime::objc_data_section(), 8,
            cir::LinkageKind::Internal, /*used=*/true);

        protocol_objects_.emplace(key(protocol), entity);

        auto add_reloc = [&](size_t offset, cir::EntityId target) {
            file_.entity_mut(entity).static_initializer_relocations.push_back(
                {offset, target, 0});
        };
        if (facts && !facts->protocols.empty()) {
            std::vector<uint8_t> list(8 + 8 * facts->protocols.size(), 0);
            write_u64(list, 0, facts->protocols.size());
            std::vector<cir::StaticInitializerRelocation> list_relocs;
            for (size_t i = 0; i < facts->protocols.size(); ++i) {
                list_relocs.push_back(
                    {8 + i * 8, protocol_object(facts->protocols[i]), 0});
            }
            add_reloc(16, make_data_global(
                              "_OBJC_$_PROTOCOL_REFS_" + name,
                              std::move(list), std::move(list_relocs),
                              objc_runtime::objc_const_section(), 8,
                              cir::LinkageKind::Internal, /*used=*/false));
        }
        if (!required_instance.empty()) {
            add_reloc(24, protocol_method_list(name, "INSTANCE_METHODS",
                                               required_instance));
        }
        if (!required_class.empty()) {
            add_reloc(32, protocol_method_list(name, "CLASS_METHODS",
                                               required_class));
        }
        if (!optional_instance.empty()) {
            add_reloc(40, protocol_method_list(name, "OPT_INSTANCE_METHODS",
                                               optional_instance));
        }
        if (!optional_class.empty()) {
            add_reloc(48, protocol_method_list(name, "OPT_CLASS_METHODS",
                                               optional_class));
        }

        size_t member_count = required_instance.size() +
                              required_class.size() +
                              optional_instance.size() +
                              optional_class.size();
        if (member_count > 0) {
            std::vector<uint8_t> types(8 * member_count, 0);
            std::vector<cir::StaticInitializerRelocation> type_relocs;
            size_t index = 0;
            auto append_types =
                [&](const std::vector<const cir::ObjCMethodFact*>& methods) {
                    for (const cir::ObjCMethodFact* method : methods) {
                        type_relocs.push_back(
                            {index * 8,
                             shared_cstring(
                                 objc_runtime::encode_method(
                                     file_, method->function_type),
                                 objc_runtime::methtype_section(),
                                 "OBJC_METH_VAR_TYPE_."),
                             0});
                        ++index;
                    }
                };
            append_types(required_instance);
            append_types(required_class);
            append_types(optional_instance);
            append_types(optional_class);
            add_reloc(72, make_data_global(
                              "_OBJC_$_PROTOCOL_METHOD_TYPES_" + name,
                              std::move(types), std::move(type_relocs),
                              objc_runtime::objc_const_section(), 8,
                              cir::LinkageKind::Internal, /*used=*/false));
        }
        std::sort(
            file_.entity_mut(entity).static_initializer_relocations.begin(),
            file_.entity_mut(entity).static_initializer_relocations.end(),
            [](const cir::StaticInitializerRelocation& a,
               const cir::StaticInitializerRelocation& b) {
                return a.offset < b.offset;
            });

        std::vector<uint8_t> label(8, 0);
        std::vector<cir::StaticInitializerRelocation> label_reloc;
        label_reloc.push_back({0, entity, 0});
        (void)make_data_global(
            "_OBJC_LABEL_PROTOCOL_$_" + name, std::move(label),
            std::move(label_reloc),
            "__DATA,__objc_protolist,coalesced,no_dead_strip", 8,
            cir::LinkageKind::Internal, /*used=*/true);
        if (facts && facts->protocol_reference.valid()) {
            cir::Entity& slot = file_.entity_mut(facts->protocol_reference);
            slot.has_static_initializer = true;
            slot.static_initializer_bytes.assign(8, 0);
            slot.static_initializer_relocations.push_back({0, entity, 0});
            slot.attr_facts.section =
                "__DATA,__objc_protorefs,coalesced,no_dead_strip";
            slot.attr_facts.requested_alignment = 8;
            slot.attr_facts.is_used = true;
        }
        return entity;
    }

    void add_backing_ivars() {
        std::vector<cir::EntityId> interfaces;
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (facts.implementation.valid() &&
                file_.entity(facts.entity).kind ==
                    cir::EntityKind::ObjCInterface) {
                interfaces.push_back(facts.entity);
            }
        }
        for (cir::EntityId interface : interfaces) {
            cir::ObjCInterfaceFacts* facts =
                file_.objc_interface_facts_mut(interface);
            for (cir::ObjCPropertyFact& property : facts->properties) {
                if (property.is_dynamic || property.is_class_property ||
                    property.backing_ivar.valid()) {
                    continue;
                }
                std::string backing =
                    property.spelled_backing_name.valid()
                        ? std::string(file_.name(property.spelled_backing_name))
                        : "_" + std::string(file_.name(property.name));
                cir::NameId backing_id = file_.intern_name(backing);
                for (const cir::ObjCIvarFact& ivar : facts->ivars) {
                    if (ivar.name == backing_id) {
                        property.backing_ivar = ivar.entity;
                        break;
                    }
                }
                if (property.backing_ivar.valid()) {
                    continue;
                }
                cir::ObjCIvarFact ivar;
                ivar.entity = builder_.add_entity(cir::EntityKind::ObjCIvar,
                                                  backing,
                                                  property.type.type,
                                                  interface,
                                                  property.loc);
                ivar.name = backing_id;
                ivar.type = property.type;
                ivar.access = cir::ObjCIvarAccess::Private;
                ivar.is_property_backing = true;
                ivar.loc = property.loc;
                property.backing_ivar = ivar.entity;
                facts->ivars.push_back(std::move(ivar));
            }
        }
    }

    cir::EntityId emit_accessor(const cir::ObjCInterfaceFacts& facts,
                                const cir::ObjCPropertyFact& property,
                                bool is_setter) {
        const std::string class_name = std::string(file_.name(facts.name));
        cir::SelectorId selector =
            is_setter ? property.setter : property.getter;
        std::string symbol = "-[" + class_name + " " +
                             std::string(file_.selector_spelling(selector)) +
                             "]";
        cir::TypeId void_ptr =
            file_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
        cir::TypeId self_type = file_.pointer_type(facts.object_type);
        cir::TypeId value_type = property.type.type;
        cir::TypeId result_type =
            is_setter ? file_.builtin_type(cir::BuiltinTypeKind::Void)
                      : value_type;
        std::vector<cir::TypeId> param_types = {self_type, void_ptr};
        if (is_setter) {
            param_types.push_back(value_type);
        }
        cir::TypeId fn_type = file_.function_type(result_type, param_types);
        cir::EntityId entity = builder_.add_entity(
            cir::EntityKind::Function, symbol, fn_type, {}, property.loc);
        file_.entity_mut(entity).is_definition = true;
        file_.entity_mut(entity).linkage = cir::LinkageKind::Internal;
        file_.entity_mut(entity).attr_facts.asm_label = symbol;

        std::vector<std::pair<cir::EntityId, cir::TypeId>> params;
        cir::EntityId self_entity = builder_.add_entity(
            cir::EntityKind::Parameter, "self", self_type, entity,
            property.loc, cir::StorageDuration::Parameter);
        cir::EntityId cmd_entity = builder_.add_entity(
            cir::EntityKind::Parameter, "_cmd", void_ptr, entity,
            property.loc, cir::StorageDuration::Parameter);
        params.push_back({self_entity, self_type});
        params.push_back({cmd_entity, void_ptr});
        if (is_setter) {
            cir::EntityId value_entity = builder_.add_entity(
                cir::EntityKind::Parameter, "value", value_type, entity,
                property.loc, cir::StorageDuration::Parameter);
            params.push_back({value_entity, value_type});
        }
        cir::FunctionStart start =
            builder_.begin_function(entity, result_type, params, property.loc);
        builder_.switch_to_block(start.entry);
        cir::InstId receiver = start.parameters[0].value.inst;
        cir::InstId offset_place = builder_.global_place(
            ivar_offset_var(property.backing_ivar), property.loc);
        cir::InstId offset = builder_.load(offset_place, property.loc);
        cir::InstId raw =
            builder_.cast(ulong_type(), receiver, "arith", property.loc);
        cir::InstId sum = builder_.binary(cir::BinaryOpKind::Add, ulong_type(),
                                          raw, offset, property.loc);
        cir::InstId typed = builder_.cast(file_.pointer_type(value_type), sum,
                                          "arith", property.loc);
        cir::InstId place = builder_.deref(typed, property.loc);
        if (is_setter) {
            (void)builder_.store(place, start.parameters[2].value.inst,
                                 property.loc);
            builder_.return_void(property.loc);
        } else {
            cir::InstId value = builder_.load(place, property.loc);
            builder_.return_value(value, property.loc);
        }
        return entity;
    }

    void synthesize_accessors() {
        std::vector<cir::EntityId> interfaces;
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (facts.implementation.valid() &&
                file_.entity(facts.entity).kind ==
                    cir::EntityKind::ObjCInterface) {
                interfaces.push_back(facts.entity);
            }
        }
        std::sort(interfaces.begin(), interfaces.end(),
                  [](cir::EntityId a, cir::EntityId b) {
                      return a.index < b.index;
                  });
        for (cir::EntityId interface : interfaces) {

            std::vector<cir::ObjCPropertyFact> properties =
                file_.objc_interface_facts(interface)->properties;
            for (const cir::ObjCPropertyFact& property : properties) {
                if (property.is_dynamic || property.is_class_property ||
                    !property.backing_ivar.valid()) {
                    continue;
                }
                auto define = [&](cir::SelectorId selector, bool is_setter) {
                    if (!selector.valid()) {
                        return;
                    }
                    cir::ObjCInterfaceFacts* facts =
                        file_.objc_interface_facts_mut(interface);
                    for (cir::ObjCMethodFact& method :
                         facts->instance_methods) {
                        if (method.selector == selector) {
                            if (!method.definition.valid()) {
                                method.definition = emit_accessor(
                                    *file_.objc_interface_facts(interface),
                                    property, is_setter);
                            }
                            return;
                        }
                    }
                };
                define(property.getter, false);
                define(property.setter, true);
            }
        }
    }

    cir::EntityId method_list_global(const std::string& symbol,
                                     const std::vector<const cir::ObjCMethodFact*>& methods) {
        std::vector<uint8_t> bytes(8 + 24 * methods.size(), 0);
        write_u32(bytes, 0, 24);
        write_u32(bytes, 4, static_cast<uint32_t>(methods.size()));
        std::vector<cir::StaticInitializerRelocation> relocations;
        size_t offset = 8;
        for (const cir::ObjCMethodFact* method : methods) {
            relocations.push_back({offset, methname(method->selector), 0});
            std::string encoding = objc_runtime::encode_method(
                file_, method->function_type);
            relocations.push_back(
                {offset + 8,
                 shared_cstring(std::move(encoding),
                                objc_runtime::methtype_section(),
                                "OBJC_METH_VAR_TYPE_."),
                 0});
            relocations.push_back({offset + 16, method->definition, 0});
            offset += 24;
        }
        return make_data_global(symbol, std::move(bytes),
                                std::move(relocations),
                                objc_runtime::objc_const_section(), 8,
                                cir::LinkageKind::Internal, /*used=*/false);
    }

    bool retainable_pointee(cir::TypeId pointee) {
        if (!file_.valid(pointee) ||
            file_.type(pointee).kind != cir::TypeKind::Record) {
            return false;
        }
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (facts.object_type.valid() &&
                file_.resolved_type(facts.object_type) == pointee) {
                return true;
            }
        }
        cir::EntityId record = file_.record_entity(pointee);
        return record.valid() && file_.entity(record).name.valid() &&
            file_.name(file_.entity(record).name) == "objc_object";
    }
    cir::ObjCOwnership arc_ivar_ownership(const cir::TypeRef& ref) {
        cir::TypeId resolved = file_.resolved_type(ref.type);
        if (!file_.valid(resolved) ||
            file_.type(resolved).kind != cir::TypeKind::Pointer) {
            return cir::ObjCOwnership::Unspecified;
        }
        const auto* pointer = std::get_if<cir::PointerTypePayload>(
            &file_.type_payload(resolved));
        if (!pointer ||
            !retainable_pointee(file_.resolved_type(pointer->pointee.type))) {
            return cir::ObjCOwnership::Unspecified;
        }
        cir::ObjCOwnership ownership = cir::ownership_of(ref.qualifiers);
        if (ownership == cir::ObjCOwnership::Unspecified) {
            ownership = cir::ownership_of(pointer->pointee.qualifiers);
        }
        return ownership == cir::ObjCOwnership::Unspecified
            ? cir::ObjCOwnership::Strong
            : ownership;
    }
    void synthesize_cxx_destruct() {
        if (!arc_) {
            return;
        }
        std::vector<cir::EntityId> interfaces;
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (facts.implementation.valid() &&
                file_.entity(facts.entity).kind ==
                    cir::EntityKind::ObjCInterface) {
                interfaces.push_back(facts.entity);
            }
        }
        std::sort(interfaces.begin(), interfaces.end(),
                  [](cir::EntityId a, cir::EntityId b) {
                      return a.index < b.index;
                  });
        for (cir::EntityId interface : interfaces) {
            const cir::ObjCInterfaceFacts* facts =
                file_.objc_interface_facts(interface);
            std::vector<std::pair<cir::EntityId, cir::ObjCOwnership>> managed;
            for (const cir::ObjCIvarFact& ivar : facts->ivars) {
                cir::ObjCOwnership ownership = arc_ivar_ownership(ivar.type);
                if (ownership == cir::ObjCOwnership::Strong ||
                    ownership == cir::ObjCOwnership::Weak) {
                    managed.push_back({ivar.entity, ownership});
                }
            }
            if (managed.empty()) {
                continue;
            }
            const std::string class_name =
                std::string(file_.name(facts->name));
            std::string symbol = "-[" + class_name + " .cxx_destruct]";
            cir::TypeId void_type =
                file_.builtin_type(cir::BuiltinTypeKind::Void);
            cir::TypeId void_ptr = file_.pointer_type(void_type);
            cir::TypeId self_type = file_.pointer_type(facts->object_type);
            cir::TypeId fn_type =
                file_.function_type(void_type, {self_type, void_ptr});
            cir::EntityId entity = builder_.add_entity(
                cir::EntityKind::Function, symbol, fn_type, {}, SrcLoc());
            file_.entity_mut(entity).is_definition = true;
            file_.entity_mut(entity).linkage = cir::LinkageKind::Internal;
            file_.entity_mut(entity).attr_facts.asm_label = symbol;

            std::vector<std::pair<cir::EntityId, cir::TypeId>> params;
            params.push_back({builder_.add_entity(
                                  cir::EntityKind::Parameter, "self",
                                  self_type, entity, SrcLoc(),
                                  cir::StorageDuration::Parameter),
                              self_type});
            params.push_back({builder_.add_entity(
                                  cir::EntityKind::Parameter, "_cmd",
                                  void_ptr, entity, SrcLoc(),
                                  cir::StorageDuration::Parameter),
                              void_ptr});
            cir::FunctionStart start = builder_.begin_function(
                entity, void_type, params, SrcLoc());
            builder_.switch_to_block(start.entry);
            cir::InstId receiver = start.parameters[0].value.inst;
            cir::InstId raw =
                builder_.cast(ulong_type(), receiver, "arith", SrcLoc());
            cir::InstId null_object = builder_.cast(
                void_ptr,
                builder_.integer_literal(0, ulong_type(), "0", SrcLoc()),
                "arith", SrcLoc());
            for (size_t i = managed.size(); i-- > 0;) {
                cir::InstId offset = builder_.load(
                    builder_.global_place(ivar_offset_var(managed[i].first),
                                          SrcLoc()),
                    SrcLoc());
                cir::InstId slot = builder_.cast(
                    void_ptr,
                    builder_.binary(cir::BinaryOpKind::Add, ulong_type(),
                                    raw, offset, SrcLoc()),
                    "arith", SrcLoc());
                if (managed[i].second == cir::ObjCOwnership::Weak) {
                    (void)builder_.call(
                        arc_runtime_decl("objc_destroyWeak", 1, false),
                        void_type, {slot}, SrcLoc());
                } else {
                    (void)builder_.call(
                        arc_runtime_decl("objc_storeStrong", 2, false),
                        void_type, {slot, null_object}, SrcLoc());
                }
            }
            builder_.return_void(SrcLoc());

            cir::ObjCMethodFact fact;
            fact.selector = file_.intern_selector(".cxx_destruct");
            fact.function_type = fn_type;
            fact.return_type = file_.type_ref(void_type);
            fact.definition = entity;
            file_.objc_interface_facts_mut(interface)
                ->instance_methods.push_back(std::move(fact));
            arc_destruct_classes_.insert(interface.index);
        }
    }

    void synthesize_class_metadata() {

        std::vector<cir::EntityId> interfaces;
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (facts.implementation.valid()) {
                interfaces.push_back(facts.entity);
            }
        }
        std::sort(interfaces.begin(), interfaces.end(),
                  [](cir::EntityId a, cir::EntityId b) {
                      return a.index < b.index;
                  });
        for (cir::EntityId interface : interfaces) {
            synthesize_one_class(interface);
        }
    }

    void fill_ehtypes() {
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (!facts.ehtype.valid() || !facts.implementation.valid()) {

                continue;
            }
            cir::Entity& record = file_.entity_mut(facts.ehtype);
            record.is_definition = true;
            record.linkage = cir::LinkageKind::Internal;
            record.has_static_initializer = true;
            record.static_initializer_bytes.assign(24, 0);
            record.static_initializer_relocations = {

                {0, extern_global("objc_ehtype_vtable"), 16},
                {8,
                 shared_cstring(std::string(file_.name(facts.name)),
                                objc_runtime::classname_section(),
                                "OBJC_CLASS_NAME_."),
                 0},
                {16, class_object(facts.entity), 0},
            };
            record.attr_facts.section = objc_runtime::objc_const_section();
            record.attr_facts.requested_alignment = 8;
            record.attr_facts.is_used = true;
            cir::TypeId void_ptr = file_.pointer_type(
                file_.builtin_type(cir::BuiltinTypeKind::Void));
            record.type = file_.array_type(void_ptr, 3);
        }
    }

    void emit_image_tables() {
        fill_ehtypes();

        std::vector<cir::EntityId> pending;
        for (const auto& [entity_key, facts] :
             file_.objc_interface_fact_table()) {
            (void)entity_key;
            if (facts.protocol_reference.valid() &&
                !protocol_objects_.count(key(facts.entity))) {
                pending.push_back(facts.entity);
            }
        }
        std::sort(pending.begin(), pending.end(),
                  [](cir::EntityId a, cir::EntityId b) {
                      return a.index < b.index;
                  });
        for (cir::EntityId protocol : pending) {
            (void)protocol_object(protocol);
        }

        if (!defined_classes_.empty()) {
            std::vector<uint8_t> bytes(8 * defined_classes_.size(), 0);
            std::vector<cir::StaticInitializerRelocation> relocations;
            for (size_t i = 0; i < defined_classes_.size(); ++i) {
                relocations.push_back({i * 8, defined_classes_[i], 0});
            }
            (void)make_data_global(objc_runtime::label_class_list_symbol(),
                                   std::move(bytes), std::move(relocations),
                                   objc_runtime::classlist_section(), 8,
                                   cir::LinkageKind::Internal, /*used=*/true);
        }
        if (!defined_classes_.empty() || !selrefs_.empty() ||
            !classrefs_.empty() || cfstring_counter_ != 0) {
            std::vector<uint8_t> info(8, 0);
            write_u32(info, 0, objc_runtime::image_info_version);
            write_u32(info, 4, objc_runtime::image_info_flags);
            (void)make_data_global(objc_runtime::image_info_symbol(),
                                   std::move(info), {},
                                   objc_runtime::imageinfo_section(), 8,
                                   cir::LinkageKind::Internal, /*used=*/true);
        }
    }

    void synthesize_one_class(cir::EntityId interface) {
        cir::ObjCInterfaceFacts* facts =
            file_.objc_interface_facts_mut(interface);
        if (!facts) {
            return;
        }
        const std::string name = std::string(file_.name(facts->name));
        const bool is_root = !facts->super_class.valid();

        cir::EntityId class_name_literal = shared_cstring(
            name, objc_runtime::classname_section(), "OBJC_CLASS_NAME_.");

        cir::EntityId ivar_list{};
        if (!facts->ivars.empty()) {
            std::vector<uint8_t> bytes(8 + 32 * facts->ivars.size(), 0);
            write_u32(bytes, 0, 32);
            write_u32(bytes, 4, static_cast<uint32_t>(facts->ivars.size()));
            std::vector<cir::StaticInitializerRelocation> relocations;
            size_t offset = 8;
            for (const cir::ObjCIvarFact& ivar : facts->ivars) {
                auto size_align = cir::size_align_of_type(file_, ivar.type.type);
                size_t size = size_align ? size_align->size_bytes : 8;
                size_t align = size_align ? size_align->alignment_bytes : 8;
                uint32_t align_log2 = 0;
                while ((size_t(1) << align_log2) < align) {
                    ++align_log2;
                }
                relocations.push_back({offset, ivar_offset_var(ivar.entity), 0});
                relocations.push_back(
                    {offset + 8,
                     shared_cstring(std::string(file_.name(ivar.name)),
                                    objc_runtime::methtype_section(),
                                    "OBJC_METH_VAR_NAME_."),
                     0});
                relocations.push_back(
                    {offset + 16,
                     shared_cstring(objc_runtime::encode_type(file_, ivar.type,
                                                              {}),
                                    objc_runtime::methtype_section(),
                                    "OBJC_METH_VAR_TYPE_."),
                     0});
                write_u32(bytes, offset + 24, align_log2);
                write_u32(bytes, offset + 28, static_cast<uint32_t>(size));
                offset += 32;
            }
            ivar_list = make_data_global(objc_runtime::ivar_list_symbol(name),
                                         std::move(bytes),
                                         std::move(relocations),
                                         objc_runtime::objc_const_section(), 8,
                                         cir::LinkageKind::Internal,
                                         /*used=*/false);
        }

        cir::EntityId protocol_list{};
        if (!facts->protocols.empty()) {
            std::vector<uint8_t> list(8 + 8 * facts->protocols.size(), 0);
            write_u64(list, 0, facts->protocols.size());
            std::vector<cir::StaticInitializerRelocation> list_relocs;
            for (size_t i = 0; i < facts->protocols.size(); ++i) {
                list_relocs.push_back(
                    {8 + i * 8, protocol_object(facts->protocols[i]), 0});
            }
            protocol_list = make_data_global(
                "_OBJC_CLASS_PROTOCOLS_$_" + name, std::move(list),
                std::move(list_relocs), objc_runtime::objc_const_section(), 8,
                cir::LinkageKind::Internal, /*used=*/false);
            facts = file_.objc_interface_facts_mut(interface);
        }

        auto defined_methods = [&](const std::vector<cir::ObjCMethodFact>& list) {
            std::vector<const cir::ObjCMethodFact*> methods;
            for (const cir::ObjCMethodFact& method : list) {
                if (method.definition.valid()) {
                    methods.push_back(&method);
                }
            }
            return methods;
        };
        std::vector<const cir::ObjCMethodFact*> instance_methods =
            defined_methods(facts->instance_methods);
        std::vector<const cir::ObjCMethodFact*> class_methods =
            defined_methods(facts->class_methods);
        cir::EntityId instance_list =
            instance_methods.empty()
                ? cir::EntityId{}
                : method_list_global(
                      objc_runtime::instance_method_list_symbol(name),
                      instance_methods);
        cir::EntityId class_list =
            class_methods.empty()
                ? cir::EntityId{}
                : method_list_global(
                      objc_runtime::class_method_list_symbol(name),
                      class_methods);

        auto make_ro = [&](bool meta) {
            std::vector<uint8_t> bytes(72, 0);
            uint32_t flags = 0;
            if (meta) {
                flags |= objc_runtime::RO_META;
            }
            if (is_root) {
                flags |= objc_runtime::RO_ROOT;
            }
            if (arc_) {
                flags |= objc_runtime::RO_IS_ARC;
            }
            if (!meta && arc_destruct_classes_.count(interface.index)) {
                flags |= objc_runtime::RO_HAS_CXX_STRUCTORS |
                         objc_runtime::RO_HAS_CXX_DTOR_ONLY;
            }
            write_u32(bytes, 0, flags);
            write_u32(bytes, 4,
                      meta ? 40
                           : static_cast<uint32_t>(
                                 facts->instance_start_bytes));
            write_u32(bytes, 8,
                      meta ? 40
                           : static_cast<uint32_t>(
                                 facts->instance_size_bytes));
            std::vector<cir::StaticInitializerRelocation> relocations;
            relocations.push_back({24, class_name_literal, 0});
            cir::EntityId methods = meta ? class_list : instance_list;
            if (methods.valid()) {
                relocations.push_back({32, methods, 0});
            }
            if (protocol_list.valid()) {
                relocations.push_back({40, protocol_list, 0});
            }
            if (!meta && ivar_list.valid()) {
                relocations.push_back({48, ivar_list, 0});
            }
            return make_data_global(objc_runtime::class_ro_symbol(name, meta),
                                    std::move(bytes), std::move(relocations),
                                    objc_runtime::objc_const_section(), 8,
                                    cir::LinkageKind::Internal,
                                    /*used=*/false);
        };
        cir::EntityId instance_ro = make_ro(false);
        cir::EntityId meta_ro = make_ro(true);

        cir::EntityId empty_cache = extern_global("_objc_empty_cache");
        auto make_class_object = [&](bool meta, cir::EntityId ro) {
            std::vector<uint8_t> bytes(40, 0);
            std::vector<cir::StaticInitializerRelocation> relocations;
            relocations.push_back({16, empty_cache, 0});
            relocations.push_back({32, ro, 0});
            return make_data_global(
                meta ? objc_runtime::metaclass_symbol(name)
                     : objc_runtime::class_symbol(name),
                std::move(bytes), std::move(relocations),
                objc_runtime::objc_data_section(), 8,
                cir::LinkageKind::External, /*used=*/false);
        };
        cir::EntityId class_entity = make_class_object(false, instance_ro);
        cir::EntityId meta_entity = make_class_object(true, meta_ro);
        class_objects_[key(interface)] = class_entity;
        metaclass_objects_[key(interface)] = meta_entity;

        cir::EntityId root = interface;
        while (true) {
            const cir::ObjCInterfaceFacts* walk =
                file_.objc_interface_facts(root);
            if (!walk || !walk->super_class.valid()) {
                break;
            }
            root = walk->super_class;
        }
        auto add_reloc = [&](cir::EntityId owner, size_t offset,
                             cir::EntityId target) {
            file_.entity_mut(owner).static_initializer_relocations.push_back(
                {offset, target, 0});
        };
        add_reloc(class_entity, 0, meta_entity);
        add_reloc(meta_entity, 0,
                  root == interface ? meta_entity : metaclass_object(root));
        if (is_root) {
            add_reloc(meta_entity, 8, class_entity);
        } else {
            add_reloc(class_entity, 8, class_object(facts->super_class));
            add_reloc(meta_entity, 8, metaclass_object(facts->super_class));
        }

        auto sort_relocs = [&](cir::EntityId owner) {
            auto& relocations =
                file_.entity_mut(owner).static_initializer_relocations;
            std::sort(relocations.begin(), relocations.end(),
                      [](const cir::StaticInitializerRelocation& a,
                         const cir::StaticInitializerRelocation& b) {
                          return a.offset < b.offset;
                      });
        };
        sort_relocs(class_entity);
        sort_relocs(meta_entity);
        defined_classes_.push_back(class_entity);
    }

    void expand_instructions() {
        for (cir::FunctionId function_id : file_.function_ids()) {
            const cir::Function& function = file_.function(function_id);
            if (file_.entity(function.entity).is_template_pattern) {
                continue;
            }
            for (cir::BlockId block_id : function.blocks) {
                expand_block(block_id);
            }
        }
    }

    void expand_block(cir::BlockId block_id) {
        for (size_t index = 0;
             index < file_.block(block_id).instructions.size(); ++index) {
            cir::InstId inst_id = file_.block(block_id).instructions[index];
            const cir::Inst inst = file_.inst(inst_id);
            std::vector<cir::InstId> prep;
            switch (inst.kind) {
                case cir::InstKind::ObjCMessageSend:
                    prep = expand_message_send(inst_id, inst);
                    break;
                case cir::InstKind::ObjCSelectorLiteral:
                    prep = expand_selector_literal(inst_id, inst);
                    break;
                case cir::InstKind::ObjCStringLiteral:
                    prep = expand_string_literal(inst_id, inst);
                    break;
                case cir::InstKind::ObjCIvarAddr:
                    prep = expand_ivar_addr(inst_id, inst);
                    break;
                case cir::InstKind::ObjCArcOp:
                    prep = expand_arc_op(inst_id, inst);
                    break;
                default:
                    continue;
            }
            cir::Block& block = file_.block_mut(block_id);
            block.instructions.insert(block.instructions.begin() + index,
                                      prep.begin(), prep.end());
            index += prep.size();
        }
    }

    struct Scratch {
        ObjCLowerer& owner;
        cir::BlockId block;
        explicit Scratch(ObjCLowerer& lowerer)
            : owner(lowerer),
              block(lowerer.builder_.create_detached_block("objc.lower")) {
            owner.builder_.switch_to_block(block);
        }
        std::vector<cir::InstId> finish(cir::InstId original) {
            std::vector<cir::InstId> instructions =
                owner.file_.block(block).instructions;
            owner.file_.block_mut(block).instructions.clear();
            cir::InstId last = instructions.back();
            instructions.pop_back();
            cir::Inst replacement = owner.file_.inst(last);
            owner.file_.inst_mut(original) = replacement;
            if (replacement.place_fact.valid()) {

                owner.file_.place_fact_mut(replacement.place_fact).source =
                    original;
            }

            owner.file_.inst_mut(last) = cir::Inst{};
            return instructions;
        }
    };

    cir::EntityId msgsend_decl(const char* function_name) {
        auto found = msgsend_decls_.find(function_name);
        if (found != msgsend_decls_.end()) {
            return found->second;
        }
        cir::TypeId void_ptr =
            file_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
        cir::TypeId fn_type = file_.function_type(void_ptr, {void_ptr, void_ptr});
        cir::EntityId entity = builder_.add_entity(cir::EntityKind::Function,
                                                   function_name,
                                                   fn_type,
                                                   {},
                                                   SrcLoc());
        file_.entity_mut(entity).is_definition = false;
        file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        msgsend_decls_.emplace(function_name, entity);
        return entity;
    }

    cir::InstId load_selector(cir::SelectorId selector, SrcLoc loc) {
        cir::InstId place = builder_.global_place(selref(selector), loc);
        return builder_.load(place, loc);
    }

    std::vector<cir::InstId> expand_message_send(cir::InstId inst_id,
                                                 const cir::Inst& inst) {

        const auto* payload_ptr = std::get_if<cir::ObjCMessageSendPayload>(
            &file_.payload(inst.payload_index));
        std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
        Scratch scratch(*this);
        if (!payload_ptr) {
            (void)builder_.error("malformed message send", inst.loc);
            return scratch.finish(inst_id);
        }
        const cir::ObjCMessageSendPayload payload_copy = *payload_ptr;
        const cir::ObjCMessageSendPayload* payload = &payload_copy;
        bool is_super =
            payload->receiver_kind == cir::ObjCReceiverKind::Super ||
            payload->receiver_kind == cir::ObjCReceiverKind::SuperClass;

        cir::TypeId void_ptr =
            file_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
        cir::InstId self_value{};
        std::vector<cir::InstId> args;
        if (payload->receiver_kind == cir::ObjCReceiverKind::Class) {
            cir::InstId place =
                builder_.global_place(classref(payload->interface_context),
                                      inst.loc);
            self_value = builder_.load(place, inst.loc);
            for (const cir::ValueRef& value : values) {
                args.push_back(value.inst);
            }
        } else if (is_super) {

            cir::InstId receiver =
                values.empty() ? cir::InstId{} : values.front().inst;
            for (size_t i = 1; i < values.size(); ++i) {
                args.push_back(values[i].inst);
            }
            cir::TypeId pair_type = file_.array_type(void_ptr, 2);
            cir::TypeId usize =
                file_.builtin_type(cir::BuiltinTypeKind::USize);
            cir::InstId size = builder_.integer_literal(16, usize, "16",
                                                        inst.loc);
            cir::InstId buffer = builder_.stack_alloc(
                file_.type_ref(pair_type), size, {}, inst.loc);
            cir::InstId address = builder_.addr_of(buffer, inst.loc);
            cir::InstId receiver_slot = builder_.deref(
                builder_.cast(file_.pointer_type(void_ptr), address, "arith",
                              inst.loc),
                inst.loc);
            (void)builder_.store(
                receiver_slot,
                builder_.cast(void_ptr, receiver, "arith", inst.loc),
                inst.loc);
            cir::InstId class_value = builder_.load(
                builder_.global_place(
                    superref(payload->interface_context,
                             payload->receiver_kind ==
                                 cir::ObjCReceiverKind::SuperClass),
                    inst.loc),
                inst.loc);
            cir::InstId base = builder_.cast(ulong_type(), address, "arith",
                                             inst.loc);
            cir::InstId eight =
                builder_.integer_literal(8, ulong_type(), "8", inst.loc);
            cir::InstId class_address = builder_.binary(
                cir::BinaryOpKind::Add, ulong_type(), base, eight, inst.loc);
            cir::InstId class_slot = builder_.deref(
                builder_.cast(file_.pointer_type(void_ptr), class_address,
                              "arith", inst.loc),
                inst.loc);
            (void)builder_.store(class_slot, class_value, inst.loc);
            self_value = builder_.cast(void_ptr, address, "arith", inst.loc);
        } else {
            self_value = values.empty() ? cir::InstId{} : values.front().inst;
            for (size_t i = 1; i < values.size(); ++i) {
                args.push_back(values[i].inst);
            }
        }

        cir::InstId sel_value = load_selector(payload->selector, inst.loc);

        bool is_variadic = false;
        if (payload->method_declaration.valid()) {
            const auto* declared = std::get_if<cir::FunctionTypePayload>(
                &file_.type_payload(
                    file_.entity(payload->method_declaration).type));
            if (declared) {
                is_variadic = declared->is_variadic;
            }
        }
        std::vector<cir::TypeRef> params;
        params.push_back(file_.type_ref(
            self_value.valid() ? file_.inst(self_value).result_type
                               : void_ptr));
        params.push_back(file_.type_ref(void_ptr));
        for (cir::InstId arg : args) {
            params.push_back(file_.type_ref(file_.inst(arg).result_type));
        }
        cir::TypeId site_type = file_.function_type(
            file_.type_ref(inst.result_type), params, is_variadic);

        MsgSendVariant variant = objc_runtime::select_msgsend_variant(
            file_, inst.result_type, file_.target_info(), is_super);
        cir::EntityId callee =
            msgsend_decl(objc_runtime::msgsend_function_name(variant));
        cir::InstId fn = builder_.function_to_pointer(callee, inst.loc);
        cir::InstId cast_fn = builder_.cast(file_.pointer_type(site_type), fn,
                                            "arith", inst.loc);
        std::vector<cir::InstId> call_args;
        call_args.push_back(self_value);
        call_args.push_back(sel_value);
        call_args.insert(call_args.end(), args.begin(), args.end());
        (void)builder_.call_indirect(cast_fn, inst.result_type, call_args,
                                     inst.loc);
        return scratch.finish(inst_id);
    }
    cir::EntityId arc_runtime_decl(const char* function_name,
                                   size_t param_count,
                                   bool returns_value) {
        auto found = arc_decls_.find(function_name);
        if (found != arc_decls_.end()) {
            return found->second;
        }
        cir::TypeId void_ptr =
            file_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
        cir::TypeId result = returns_value
            ? void_ptr
            : file_.builtin_type(cir::BuiltinTypeKind::Void);
        std::vector<cir::TypeId> params(param_count, void_ptr);
        cir::EntityId entity = builder_.add_entity(
            cir::EntityKind::Function, function_name,
            file_.function_type(result, params), {}, SrcLoc());
        file_.entity_mut(entity).is_definition = false;
        file_.entity_mut(entity).linkage = cir::LinkageKind::External;
        arc_decls_.emplace(function_name, entity);
        return entity;
    }

    std::vector<cir::InstId> expand_arc_op(cir::InstId inst_id,
                                           const cir::Inst& inst) {
        const auto* payload_ptr =
            std::get_if<cir::ObjCArcOpPayload>(&file_.payload(inst.payload_index));
        std::vector<cir::ValueRef> values = file_.value_operands(inst.operands);
        Scratch scratch(*this);
        if (!payload_ptr) {
            (void)builder_.error("malformed ARC operation", inst.loc);
            return scratch.finish(inst_id);
        }
        const cir::ObjCArcOpKind op = payload_ptr->op;
        const char* symbol = nullptr;
        bool returns_value = false;
        switch (op) {
            case cir::ObjCArcOpKind::Retain:
                symbol = "objc_retain"; returns_value = true; break;
            case cir::ObjCArcOpKind::Release:
                symbol = "objc_release"; break;
            case cir::ObjCArcOpKind::Autorelease:
                symbol = "objc_autorelease"; returns_value = true; break;
            case cir::ObjCArcOpKind::RetainAutoreleasedReturnValue:
                symbol = "objc_retainAutoreleasedReturnValue";
                returns_value = true; break;
            case cir::ObjCArcOpKind::AutoreleaseReturnValue:
                symbol = "objc_autoreleaseReturnValue";
                returns_value = true; break;
            case cir::ObjCArcOpKind::StoreStrong:
                symbol = "objc_storeStrong"; break;
            case cir::ObjCArcOpKind::LoadWeak:
                symbol = "objc_loadWeakRetained"; returns_value = true; break;
            case cir::ObjCArcOpKind::StoreWeak:
                symbol = "objc_storeWeak"; returns_value = true; break;
            case cir::ObjCArcOpKind::InitWeak:
                symbol = "objc_initWeak"; returns_value = true; break;
            case cir::ObjCArcOpKind::DestroyWeak:
                symbol = "objc_destroyWeak"; break;
            case cir::ObjCArcOpKind::MoveWeak:
                symbol = "objc_moveWeak"; break;
            case cir::ObjCArcOpKind::CopyWeak:
                symbol = "objc_copyWeak"; break;
            case cir::ObjCArcOpKind::RetainBlock:
                symbol = "objc_retainBlock"; returns_value = true; break;
        }
        cir::TypeId void_ptr =
            file_.pointer_type(file_.builtin_type(cir::BuiltinTypeKind::Void));
        cir::EntityId callee =
            arc_runtime_decl(symbol, values.size(), returns_value);
        std::vector<cir::InstId> args;
        args.reserve(values.size());
        for (const cir::ValueRef& value : values) {
            args.push_back(builder_.cast(void_ptr, value.inst, "arith",
                                         inst.loc));
        }
        cir::TypeId call_result = returns_value
            ? void_ptr
            : file_.builtin_type(cir::BuiltinTypeKind::Void);
        cir::InstId call = builder_.call(callee, call_result, args, inst.loc);
        if (returns_value && file_.valid(inst.result_type)) {
            (void)builder_.cast(inst.result_type, call, "arith", inst.loc);
        }
        return scratch.finish(inst_id);
    }

    std::vector<cir::InstId> expand_selector_literal(cir::InstId inst_id,
                                                     const cir::Inst& inst) {
        const auto* payload_ptr = std::get_if<cir::ObjCSelectorLiteralPayload>(
            &file_.payload(inst.payload_index));
        Scratch scratch(*this);
        if (!payload_ptr) {
            (void)builder_.error("malformed selector literal", inst.loc);
            return scratch.finish(inst_id);
        }
        const cir::ObjCSelectorLiteralPayload payload = *payload_ptr;
        cir::InstId place =
            builder_.global_place(selref(payload.selector), inst.loc);
        cir::InstId loaded = builder_.load(place, inst.loc);
        (void)builder_.cast(inst.result_type, loaded, "arith", inst.loc);
        return scratch.finish(inst_id);
    }

    std::vector<cir::InstId> expand_string_literal(cir::InstId inst_id,
                                                   const cir::Inst& inst) {
        const auto* payload =
            std::get_if<cir::LiteralPayload>(&file_.payload(inst.payload_index));
        Scratch scratch(*this);
        const auto* bytes_value =
            payload ? std::get_if<cir::LiteralByteArray>(&payload->value)
                    : nullptr;
        if (!bytes_value) {
            (void)builder_.error("malformed @-string literal", inst.loc);
            return scratch.finish(inst_id);
        }
        std::string content(bytes_value->begin(), bytes_value->end());
        cir::EntityId cstring = shared_cstring(
            content, objc_runtime::cstring_section(), ".str.");
        std::vector<uint8_t> image(32, 0);
        write_u32(image, 8, objc_runtime::cfstring_layout().flags_value);
        write_u64(image, 24, content.size());
        std::vector<cir::StaticInitializerRelocation> relocations;
        relocations.push_back(
            {0, extern_global("__CFConstantStringClassReference"), 0});
        relocations.push_back({16, cstring, 0});
        cir::EntityId cfstring = make_data_global(
            objc_runtime::cfstring_symbol(cfstring_counter_++),
            std::move(image), std::move(relocations),
            objc_runtime::cfstring_section(), 8, cir::LinkageKind::Internal,
            /*used=*/false);
        cir::InstId place = builder_.global_place(cfstring, inst.loc);
        cir::InstId address = builder_.addr_of(place, inst.loc);
        (void)builder_.cast(inst.result_type, address, "arith", inst.loc);
        return scratch.finish(inst_id);
    }

    std::vector<cir::InstId> expand_ivar_addr(cir::InstId inst_id,
                                              const cir::Inst& inst) {
        std::vector<cir::Operand> operands = file_.operands(inst.operands);
        Scratch scratch(*this);
        const cir::ValueRef* receiver =
            operands.empty() ? nullptr
                             : std::get_if<cir::ValueRef>(&operands[0].data);
        const cir::EntityId* ivar =
            operands.size() < 2 ? nullptr
                                : std::get_if<cir::EntityId>(&operands[1].data);
        if (!receiver || !ivar) {
            (void)builder_.error("malformed ivar access", inst.loc);
            return scratch.finish(inst_id);
        }
        cir::InstId offset_place =
            builder_.global_place(ivar_offset_var(*ivar), inst.loc);
        cir::InstId offset = builder_.load(offset_place, inst.loc);
        cir::InstId raw = builder_.cast(ulong_type(), receiver->inst, "arith",
                                        inst.loc);
        cir::InstId sum = builder_.binary(cir::BinaryOpKind::Add, ulong_type(),
                                          raw, offset, inst.loc);

        cir::TypeId place_type = inst.result_type;
        cir::TypeId object_type = file_.place_object_type(place_type);
        cir::InstId typed = builder_.cast(file_.pointer_type(object_type), sum,
                                          "arith", inst.loc);
        (void)builder_.deref(typed, inst.loc);
        return scratch.finish(inst_id);
    }
};

} // namespace

ObjCLowerResult lower_objc(cir::File& file, bool arc) {
    ObjCLowerResult result;
    result.changed = ObjCLowerer(file, arc).run();
    return result;
}

} // namespace aburi::cirpasses
