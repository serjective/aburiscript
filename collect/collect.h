#ifndef ABURI_COLLECT_COLLECT_H
#define ABURI_COLLECT_COLLECT_H

#include <optional>
#include <cstdint>
#include <functional>
#include <limits>
#include <memory>
#include <string>
#include <string_view>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

#include "../lang_options.h"
#include "../lexer.h"
#include "../abi/target_info.h"
#include "../cir/builder.h"
#include "../cir/file.h"
#include "../parser/syntax_tree.h"
#include "../constexpr/const_value.h"
#include "collect_types.h"

struct ConstValue;
struct ConstEvalContext;

namespace aburi::modules {
class ModuleLoader;
struct LoadedModuleUnit;
}

namespace aburi::collect {

class Session {
public:
    struct TemplateInfo;

    ~Session();
    explicit Session(LangOptions lang_opts = LangOptions(),
                     std::shared_ptr<TargetInfo> target = nullptr);

    cir::File finish_file();
    const cir::File& file() const { return file_; }
    cir::File& file() { return file_; }

    void report_error(std::string message, SrcLoc loc = SrcLoc());
    void report_warning(std::string message, SrcLoc loc = SrcLoc());
    void report_note(std::string message, SrcLoc loc = SrcLoc());
    void report_warning(WarningId id, std::string message, SrcLoc loc = SrcLoc());
    void set_source_manager(std::shared_ptr<SourceManager> source_manager) {
        source_manager_ = std::move(source_manager);
    }
    void apply_attributes(cir::EntityId entity,
                          AttributeTarget target,
                          const AttributeList& attrs,
                          SrcLoc loc = SrcLoc());
    void apply_weak_pragma(std::string_view alias_name,
                           std::string_view target_name,
                           SrcLoc loc = SrcLoc());
    void drain_weak_pragmas();
    cir::EntityId bind_prototype_parameter(std::string_view name,
                                           cir::TypeRef type,
                                           SrcLoc loc,
                                           bool type_originates_from_template_parameter = false);
    DeclResult declare_block_byref_variable(std::string_view name,
                                            cir::TypeId type,
                                            std::optional<ExprResult> initializer,
                                            SrcLoc loc,
                                            DeclFlags flags);
    void apply_record_attributes(cir::RecordFacts& facts,
                                 cir::RecordKind kind,
                                 const AttributeList& attrs,
                                 SrcLoc loc = SrcLoc());
    void apply_field_attributes(cir::RecordFieldFact& fact,
                                const AttributeList& attrs,
                                SrcLoc loc = SrcLoc());
    size_t requested_alignment_from_attributes(const AttributeList& attrs,
                                               SrcLoc loc = SrcLoc());
    void enter_dead_branch() { ++dead_branch_depth_; }
    void leave_dead_branch() { if (dead_branch_depth_) --dead_branch_depth_; }
    bool in_dead_branch() const { return dead_branch_depth_ > 0; }

    class SpeculativeParseGuard {
    public:
        SpeculativeParseGuard(SpeculativeParseGuard&& other) noexcept;
        ~SpeculativeParseGuard();

        SpeculativeParseGuard(const SpeculativeParseGuard&) = delete;
        SpeculativeParseGuard& operator=(const SpeculativeParseGuard&) =
            delete;
        SpeculativeParseGuard& operator=(SpeculativeParseGuard&&) = delete;

        void commit();
        void rollback();
        bool active() const { return session_ != nullptr; }

    private:
        friend class Session;
        explicit SpeculativeParseGuard(Session& session);
        void finish(bool commit);

        Session* session_ = nullptr;
        size_t depth_ = 0;
    };

    [[nodiscard]] SpeculativeParseGuard speculative_parse();
    void begin_speculative_parse();
    void commit_speculative_parse();
    void rollback_speculative_parse();
    bool is_speculative_parsing() const { return !speculative_snapshots_.empty(); }
    size_t begin_discarded_statement_validation();
    void end_discarded_statement_validation();
    void merge_discarded_control_flow_events(size_t event_watermark);
    bool in_discarded_statement_validation() const {
        return discarded_statement_validation_depth_ > 0;
    }
    void track_speculative_rollback(std::function<void()> undo);
    void track_speculative_rollback(std::string_view label,
                                    std::function<void()> undo);
    template <typename Map, typename Key>
    void journal_speculative_map_entry(std::string_view label,
                                       Map& map,
                                       const Key& key) {
        if (!is_speculative_parsing()) {
            return;
        }
        using StoredKey = std::decay_t<Key>;
        using Mapped = typename Map::mapped_type;
        StoredKey stored_key(key);
        std::optional<Mapped> previous;
        auto found = map.find(stored_key);
        if (found != map.end()) {
            previous = found->second;
        }
        Map* map_pointer = &map;
        track_speculative_rollback(
            label,
            [map_pointer, stored_key = std::move(stored_key),
             previous = std::move(previous)]() mutable {
                if (previous.has_value()) {
                    map_pointer->insert_or_assign(stored_key,
                                                  std::move(*previous));
                } else {
                    map_pointer->erase(stored_key);
                }
            });
    }

    template <typename Vector>
    void journal_speculative_vector_size(std::string_view label,
                                         Vector& vector) {
        if (!is_speculative_parsing()) {
            return;
        }
        Vector* vector_pointer = &vector;
        size_t previous_size = vector.size();
        track_speculative_rollback(
            label,
            [vector_pointer, previous_size] {
                vector_pointer->resize(previous_size);
            });
    }

    template <typename Set, typename Key>
    void journal_speculative_set_entry(std::string_view label,
                                       Set& set,
                                       const Key& key) {
        if (!is_speculative_parsing()) {
            return;
        }
        using StoredKey = std::decay_t<Key>;
        StoredKey stored_key(key);
        bool was_present = set.count(stored_key) != 0;
        Set* set_pointer = &set;
        track_speculative_rollback(
            label,
            [set_pointer, stored_key = std::move(stored_key),
             was_present]() mutable {
                if (was_present) {
                    set_pointer->insert(std::move(stored_key));
                } else {
                    set_pointer->erase(stored_key);
                }
            });
    }

    ScopeEnterResult enter_scope(ScopeFlags flags);
    void leave_scope();

    struct NamespaceEnterResult {
        cir::EntityId entity{};
        bool has_error = false;
    };
    NamespaceEnterResult enter_named_namespace(std::string_view name,
                                                SrcLoc loc,
                                                bool is_inline = false);
    NamespaceEnterResult enter_anonymous_namespace(SrcLoc loc);
    void leave_namespace();
    bool collect_namespace_alias(std::string_view alias,
                                 cir::DeclContextId target,
                                 SrcLoc loc);
    bool collect_dependent_namespace_alias(std::string_view alias,
                                           SrcLoc loc);
    bool collect_using_directive(cir::DeclContextId nominated, SrcLoc loc);
    // The [basic.link] ODR invariant gives every name transitively owned by an
    // unnamed namespace internal linkage, regardless of its declared form.
    void finalize_name_linkage();
    bool entity_has_internal_name_linkage(cir::EntityId entity) const;
    bool collect_using_declaration(cir::DeclContextId source_context,
                                   std::string_view name,
                                   SrcLoc loc,
                                   bool uses_typename = false,
                                   cir::TypeRef dependent_qualifier = {});
    bool collect_inherited_constructor_nomination(
        cir::DeclContextId base_context,
        cir::TypeRef dependent_qualifier,
        SrcLoc loc);
    bool collect_using_enum_declaration(cir::DeclContextId enum_context,
                                        SrcLoc loc);
    struct QualifierResolution {
        cir::DeclContextId context{};
        cir::EntityId entity{};
        cir::TypeRef dependent_type{};
        bool is_namespace = false;
        bool has_error = false;
    };
    QualifierResolution resolve_qualifier_root() const;
    QualifierResolution resolve_qualifier_component(cir::DeclContextId scope,
                                                    std::string_view name,
                                                    SrcLoc loc);
    std::optional<QualifierResolution> resolve_type_qualifier(
        cir::TypeRef type,
        SrcLoc loc,
        std::string_view display_name = {});
    std::optional<cir::Binding> qualified_namespace_direct_binding(
        cir::DeclContextId context,
        std::string_view name) const;
    ExprResult lookup_qualified_name(cir::DeclContextId context,
                                     std::string_view name,
                                     SrcLoc loc);
    cir::TypeRef lookup_qualified_type_name_ref(
        cir::DeclContextId context,
        std::string_view name) const;
    cir::TypeId lookup_qualified_type_name(cir::DeclContextId context,
                                           std::string_view name) const;
    cir::TypeRef lookup_qualified_type_name_ref_checked(
        cir::DeclContextId context,
        std::string_view name,
        SrcLoc loc,
        cir::EntityId accessing_record = {},
        std::string_view accessing_function_name = {});
    cir::TypeId lookup_qualified_type_name_checked(
        cir::DeclContextId context,
        std::string_view name,
        SrcLoc loc,
        cir::EntityId accessing_record = {},
        std::string_view accessing_function_name = {});
    void enter_template_argument_access_exemption();
    void leave_template_argument_access_exemption();
    void set_current_record_member_access(
        std::optional<cir::RecordMemberAccess> access);
    std::optional<cir::RecordMemberAccess>
    current_record_member_access() const;
    cir::TypeRef peek_qualified_type_ref(bool global_qualifier,
                                         const std::vector<std::string_view>& qualifiers,
                                         std::string_view terminal,
                                         cir::DeclContextId* terminal_context =
                                             nullptr) const;
    bool qualified_type_name_denotes_concrete_type(
        cir::DeclContextId context,
        std::string_view name,
        const TemplateInfo* template_info) const;
    // Pushes a scope frame onto an existing declaration context (out-of-line
    // namespace member definitions now; template instantiation later).
    ScopeEnterResult enter_existing_context(cir::DeclContextId context,
                                            ScopeFlags flags);
    void enter_linkage_spec(bool is_extern_c,
                            bool implies_extern_storage = false) {
        linkage_spec_stack_.push_back(is_extern_c);
        linkage_spec_extern_storage_stack_.push_back(implies_extern_storage);
    }
    void leave_linkage_spec() {
        if (!linkage_spec_stack_.empty()) {
            linkage_spec_stack_.pop_back();
        }
        if (!linkage_spec_extern_storage_stack_.empty()) {
            linkage_spec_extern_storage_stack_.pop_back();
        }
    }
    bool in_extern_c_linkage() const {
        return !linkage_spec_stack_.empty() && linkage_spec_stack_.back();
    }
    bool linkage_spec_implies_extern_storage() const {
        return !linkage_spec_extern_storage_stack_.empty() &&
               linkage_spec_extern_storage_stack_.back();
    }

    ScopeId current_scope() const { return current_scope_; }
    cir::DeclContextId current_decl_context() const;
    ScopeId find_enclosing_scope(ScopeFlags flags) const;
    bool is_file_scope() const;
    uint64_t lookup_generation() const { return lookup_generation_; }

    void collect_global_module_fragment(SrcLoc loc);
    void collect_module_declaration(std::string_view module_name,
                                    std::string_view partition_name,
                                    bool has_partition,
                                    bool exported,
                                    bool at_start,
                                    SrcLoc loc);
    void collect_private_module_fragment(SrcLoc loc);
    void collect_module_import(std::string_view target,
                               bool is_partition,
                               bool exported,
                               SrcLoc loc);
    bool begin_export_region(SrcLoc loc);
    void end_export_region();
    bool in_module_interface_purview() const;
    void note_module_hidden_name(std::string_view name, SrcLoc loc);
    void set_module_loader(aburi::modules::ModuleLoader* loader) {
        module_loader_ = loader;
    }
    using ModuleUnitReplayCallback =
        std::function<bool(const std::vector<Token>& tokens)>;
    ModuleUnitReplayCallback set_module_unit_replay_callback(
        ModuleUnitReplayCallback callback) {
        ModuleUnitReplayCallback previous =
            std::move(module_unit_replay_callback_);
        module_unit_replay_callback_ = std::move(callback);
        return previous;
    }
    using ModuleUnitRegisterCallback = std::function<void(
        const std::vector<Token>& tokens, cir::ModuleAttachmentId unit)>;
    ModuleUnitRegisterCallback set_module_unit_register_callback(
        ModuleUnitRegisterCallback callback) {
        ModuleUnitRegisterCallback previous =
            std::move(module_unit_register_callback_);
        module_unit_register_callback_ = std::move(callback);
        return previous;
    }
    cir::ModuleAttachmentId current_module_unit() const {
        return module_state_.unit;
    }
    cir::ModuleAttachmentId import_module_unit_by_key(
        const std::string& module_name,
        const std::string& partition_name,
        SrcLoc loc);
    std::shared_ptr<void> export_template_state() const;
    void adopt_imported_templates(const void* exported_state,
                                  const cir::File::ModuleGraphRemap& remap,
                                  const cir::File& source_file,
                                  size_t first_imported_entity_index);
    static bool template_state_adoptable(const void* exported_state,
                                         const cir::File& source_file);
    static bool template_state_has_templates(const void* exported_state);
    static void serialize_template_state(const void* exported_state,
                                         std::string& out);
    static std::shared_ptr<void> deserialize_template_state(
        std::string_view bytes);
    class ModuleVisibilityOverride {
    public:
        ModuleVisibilityOverride(Session& session,
                                 cir::ModuleAttachmentId unit);
        ~ModuleVisibilityOverride();
        ModuleVisibilityOverride(const ModuleVisibilityOverride&) = delete;
        ModuleVisibilityOverride& operator=(const ModuleVisibilityOverride&) =
            delete;

    private:
        Session& session_;
        bool active_ = false;
    };

    void begin_scope();
    void end_scope();
    void apply_visibility_pragma(bool is_push, std::string_view value, SrcLoc loc);
    void enter_statement_expression() { ++statement_expr_depth_; }
    void leave_statement_expression() {
        if (statement_expr_depth_ > 0) {
            --statement_expr_depth_;
        }
    }
    bool is_type_name(std::string_view name) const;
    bool is_typedef_name(std::string_view name) const;
    cir::TypeId lookup_type_name(std::string_view name) const;
    cir::TypeRef lookup_type_name_ref(std::string_view name) const;
    cir::TypeRef lookup_type_name_ref_checked(std::string_view name,
                                              SrcLoc loc);
    bool type_name_is_active_template_type_parameter(std::string_view name) const;
    cir::TypeRef type_ref(cir::TypeId type,
                          uint8_t qualifiers = cir::QualNone,
                          cir::MemorySpace memory_space = cir::MemorySpace::Default) const;
    cir::TypeId pointer_type(cir::TypeId pointee);
    cir::TypeId pointer_type(cir::TypeRef pointee);
    cir::TypeId block_pointer_type(cir::TypeRef pointee);
    cir::TypeId reference_type(cir::TypeRef referred, cir::ReferenceKind reference_kind);
    cir::TypeId member_pointer_type(cir::TypeRef class_type, cir::TypeRef member_type);
    cir::TypeId auto_type(cir::AutoTypeFlavor flavor = cir::AutoTypeFlavor::Gnu);
    cir::TypeId dependent_type(std::string_view name);
    cir::TypeId complex_type(cir::TypeRef element_type);
    cir::TypeId vector_type(cir::TypeRef element_type,
                            uint32_t element_count,
                            uint64_t size_bytes);
    cir::TypeRef apply_type_attributes(cir::TypeRef type,
                                       const AttributeList& attrs,
                                       SrcLoc loc = SrcLoc());
    cir::TypeId typeof_expr_type(cir::InstId expr);
    cir::TypeId decltype_expr_type(cir::InstId expr,
                                   bool use_declared_type_rule,
                                   cir::DecltypeOperandCategory operand_category,
                                   cir::TypeRef operand_type,
                                   cir::TypeRef dependent_value_qualifier = {},
                                   cir::NameId dependent_value_name = {},
                                   cir::TemplateValueExpression
                                       operand_expression = {});
    cir::TypeRef resolve_typeof_expr_type(const ExprResult& expr, SrcLoc loc = SrcLoc());
    cir::TypeRef resolve_decltype_expr_type(const ExprResult& expr,
                                            bool use_declared_type_rule,
                                            SrcLoc loc = SrcLoc());
    enum class UnevaluatedCallResolutionStatus : uint8_t {
        Resolved,
        StillDependent,
        SubstitutionFailure,
        HardError,
    };
    struct UnevaluatedCallResolution {
        struct SelectedCall {
            uint32_t node = cir::TemplateValueExprNoNode;
            cir::EntityId entity{};
            bool has_implicit_object = false;
        };

        UnevaluatedCallResolutionStatus status =
            UnevaluatedCallResolutionStatus::StillDependent;
        cir::TypeRef type;
        cir::TemplateValueExpression expression;
        std::vector<SelectedCall> selected_calls;
    };
    void begin_decltype_operand() {
        ++decltype_operand_depth_;
        ++unevaluated_operand_depth_;
    }
    void end_decltype_operand() {
        if (decltype_operand_depth_ > 0) {
            --decltype_operand_depth_;
        }
        end_unevaluated_operand();
    }
    void begin_unevaluated_operand() { ++unevaluated_operand_depth_; }
    void end_unevaluated_operand() {
        if (unevaluated_operand_depth_ > 0) {
            --unevaluated_operand_depth_;
        }
    }
    bool in_unevaluated_operand() const {
        return unevaluated_operand_depth_ > 0;
    }
    void begin_typeid_probe_operand() {
        ++unevaluated_operand_depth_;
        ++typeid_capture_discovery_depth_;
    }
    void end_typeid_probe_operand() {
        if (typeid_capture_discovery_depth_ > 0) {
            --typeid_capture_discovery_depth_;
        }
        end_unevaluated_operand();
    }
    bool in_typeid_capture_discovery() const {
        return typeid_capture_discovery_depth_ > 0;
    }
    bool contains_auto_type(cir::TypeId type,
                            std::optional<cir::AutoTypeFlavor> flavor = std::nullopt) const;
    size_t count_auto_type_occurrences(
        cir::TypeId type,
        cir::AutoTypeFlavor flavor = cir::AutoTypeFlavor::Cxx) const;
    bool function_has_placeholder_return(cir::TypeId function_type,
                                         cir::TypeRef* pattern = nullptr) const;
    bool explicit_instantiation_declaration_leaves_specialization_undeclared(
        cir::EntityId entity) const;
    cir::TypeId deduce_auto_type(cir::TypeId pattern,
                                 const ExprResult& initializer,
                                 SrcLoc loc = SrcLoc());
    std::shared_ptr<const OverloadDesignator> canonical_overload_designator(
        const ExprResult& expression,
        bool address_of_written = false) const;
    cir::TypeId replace_auto_type(cir::TypeId pattern, cir::TypeRef replacement, SrcLoc loc = SrcLoc());
    cir::TypeId replace_auto_type_occurrences(
        cir::TypeId pattern,
        const std::vector<cir::TypeRef>& replacements,
        cir::AutoTypeFlavor flavor = cir::AutoTypeFlavor::Cxx,
        SrcLoc loc = SrcLoc());
    cir::TypeId array_type(cir::TypeId element, std::optional<size_t> size);
    cir::TypeId array_type(cir::TypeRef element, std::optional<size_t> size);
    cir::TypeId array_type_with_extent_param(cir::TypeRef element,
                                             std::optional<size_t> size,
                                             uint32_t extent_param);
    cir::TypeId array_type(cir::TypeRef element,
                           cir::ArraySizeKind size_kind,
                           std::optional<size_t> size = std::nullopt,
                           cir::InstId size_expr = {},
                           bool size_expr_is_dependent = false,
                           cir::TemplateValueExpression dependent_size_expr = {});
    cir::TypeId function_type(cir::TypeRef result,
                              const std::vector<cir::TypeRef>& params,
                              bool is_variadic = false,
                              bool has_prototype = true,
                              bool member_is_const = false,
                              cir::FunctionExceptionSpec exception_spec = {},
                              const std::vector<uint8_t>& parameter_pack_flags = {},
                              cir::FunctionRefQualifierKind member_ref_qualifier =
                                  cir::FunctionRefQualifierKind::None,
                              bool member_is_volatile = false);

    RecordDeclResult declare_record_tag(cir::RecordKind kind,
                                        std::string_view tag,
                                        SrcLoc loc = SrcLoc());
    RecordDeclResult declare_record_tag_in_current_scope(cir::RecordKind kind,
                                                        std::string_view tag,
                                                        SrcLoc loc = SrcLoc(),
                                                        cir::EntityId record_to_redeclare = {});
    RecordDeclResult declare_hidden_friend_record(
        cir::RecordKind kind,
        std::string_view tag,
        cir::DeclContextId target_context,
        SrcLoc loc = SrcLoc());
    cir::TypeId declare_enum_tag(std::string_view tag,
                                 bool is_scoped = false,
                                 cir::TypeRef fixed_underlying = {},
                                 SrcLoc loc = SrcLoc());
    cir::EntityId declare_enumerator(std::string_view name,
                                     int64_t value,
                                     cir::TypeId provisional_type,
                                     SrcLoc loc = SrcLoc());
    cir::TypeRef select_enum_underlying(
        cir::TypeRef fixed_underlying,
        const std::vector<EnumEnumeratorInput>& enumerators);
    EnumDeclResult define_enum(std::string_view tag,
                               std::vector<EnumEnumeratorInput> enumerators,
                               SrcLoc loc = SrcLoc(),
                               cir::TypeRef fixed_underlying = {},
                               bool is_packed = false,
                               bool is_scoped = false);
    RecordDeclResult begin_record_definition(cir::RecordKind kind,
                                             std::string_view tag,
                                             SrcLoc loc = SrcLoc(),
                                             cir::EntityId record_to_complete = {});
    RecordDeclResult begin_explicit_member_record_specialization(
        cir::RecordKind kind,
        std::string_view tag,
        SrcLoc loc = SrcLoc());
    ScopeEnterResult enter_record_scope(cir::EntityId record_entity,
                                        SrcLoc loc = SrcLoc());
    void bind_record_injected_class_name(std::string_view name,
                                         cir::EntityId record_entity,
                                         SrcLoc loc = SrcLoc());
    void set_current_record_pending_bases(
        const std::vector<RecordBaseInput>& bases);
    RecordDeclResult define_record(cir::RecordKind kind,
                                   std::string_view tag,
                                   std::vector<RecordFieldInput> fields,
                                   SrcLoc loc = SrcLoc(),
                                   RecordLayoutOptions layout_options = {});
    cir::EntityId declare_record_static_data_member(
        const RecordStaticDataMemberInput& member);
    void stage_record_static_data_member_fact(
        const RecordStaticDataMemberInput& member);
    bool complete_record_static_data_member_type(
        cir::EntityId entity,
        std::string_view name,
        cir::TypeId type);
    cir::EntityId declare_record_method_shell(
        cir::EntityId record_entity,
        RecordMethodInput& method);
    bool validate_record_static_data_member_definition(
        cir::EntityId entity,
        bool has_initializer,
        const DeclFlags& flags,
        SrcLoc loc = SrcLoc());
    bool materialize_record_static_data_member_initializer(
        cir::EntityId entity,
        cir::TypeId type,
        const ExprResult& initializer,
        SrcLoc loc,
        ConstructorInitializationKind init_kind =
            ConstructorInitializationKind::Direct);
    const cir::RecordStaticDataMemberFact*
    record_static_data_member_fact(cir::EntityId entity) const {
        return static_data_member_fact(entity);
    }
    RecordDeclResult finish_record_definition(
        RecordDeclResult decl,
        cir::RecordKind kind,
        std::vector<RecordFieldInput> fields,
        std::vector<RecordStaticDataMemberInput> static_data_members,
        std::vector<RecordMethodInput> methods,
        SrcLoc loc = SrcLoc(),
        RecordLayoutOptions layout_options = {},
        std::vector<cir::EntityId>* method_entities_out = nullptr,
        const std::vector<const TemplateInfo*>* method_template_heads = nullptr,
        std::vector<RecordBaseInput> bases = {},
        bool is_final = false,
        bool is_anonymous_union_definition = false);
    ObjCInterfaceDeclResult declare_objc_class_forward(std::string_view name,
                                                       SrcLoc loc = SrcLoc());
    ObjCInterfaceDeclResult begin_objc_interface(std::string_view name,
                                                 std::string_view super_name,
                                                 const AttributeList& attrs,
                                                 SrcLoc loc = SrcLoc());
    void collect_objc_ivars(cir::EntityId interface,
                            std::vector<ObjCIvarInput> ivars,
                            SrcLoc loc = SrcLoc());
    cir::EntityId declare_objc_method(cir::EntityId interface,
                                      ObjCMethodInput& method);
    void finish_objc_interface(cir::EntityId interface, SrcLoc loc = SrcLoc());
    cir::EntityId begin_objc_implementation(std::string_view name,
                                            SrcLoc loc = SrcLoc());
    FunctionDeclStart begin_objc_method_definition(cir::EntityId interface,
                                                   ObjCMethodInput& method,
                                                   SrcLoc loc = SrcLoc());
    void finish_objc_implementation(cir::EntityId interface,
                                    SrcLoc loc = SrcLoc());
    ObjCInterfaceDeclResult declare_objc_protocol_forward(
        std::string_view name, SrcLoc loc = SrcLoc());
    ObjCInterfaceDeclResult begin_objc_protocol(
        std::string_view name,
        const std::vector<std::string>& inherited,
        SrcLoc loc = SrcLoc());
    void finish_objc_protocol(cir::EntityId protocol, SrcLoc loc = SrcLoc());
    cir::EntityId begin_objc_category(std::string_view class_name,
                                      std::string_view category_name,
                                      SrcLoc loc = SrcLoc());
    void set_objc_container_protocols(
        cir::EntityId container,
        const std::vector<std::string>& protocol_names,
        SrcLoc loc = SrcLoc());
    cir::EntityId declare_objc_property(cir::EntityId container,
                                        ObjCPropertyInput& property);
    void collect_objc_synthesize(cir::EntityId interface,
                                 std::string_view property_name,
                                 std::string_view backing_name,
                                 bool is_dynamic,
                                 SrcLoc loc = SrcLoc());
    bool is_objc_protocol_name(std::string_view name) const;
    void push_objc_type_parameters(std::vector<std::string> names);
    void pop_objc_type_parameters();
    bool objc_type_accepts_angle_suffix(std::string_view name) const;
    ExprResult collect_objc_message_send(ObjCMessageSendInput&& input);
    ExprResult collect_objc_selector_expr(std::string_view selector,
                                          SrcLoc loc = SrcLoc());
    ExprResult collect_objc_protocol_expr(std::string_view name,
                                          SrcLoc loc = SrcLoc());
    ExprResult collect_objc_box_expr(ExprResult value, SrcLoc loc = SrcLoc());
    ExprResult collect_objc_array_literal(std::vector<ExprResult> elements,
                                          SrcLoc loc = SrcLoc());
    ExprResult collect_objc_dictionary_literal(
        std::vector<std::pair<ExprResult, ExprResult>> entries,
        SrcLoc loc = SrcLoc());
    StmtResult collect_objc_throw_stmt(std::optional<ExprResult> operand,
                                       SrcLoc loc = SrcLoc());
    StmtResult collect_objc_autoreleasepool(StmtResult body,
                                            SrcLoc loc = SrcLoc());
    ObjCSynchronizedControl begin_objc_synchronized(ExprResult object,
                                                    SrcLoc loc = SrcLoc());
    StmtResult finish_objc_synchronized(ObjCSynchronizedControl& control,
                                        StmtResult body,
                                        SrcLoc loc = SrcLoc());
    StmtResult arc_finish_dealloc_body(StmtResult body,
                                       const FunctionDeclStart& start,
                                       SrcLoc loc);
    ExprResult collect_objc_bridge_cast(ObjCBridgeKind kind,
                                        cir::TypeId target_type,
                                        ExprResult operand,
                                        SrcLoc loc);
    bool arc_check_plain_cast(cir::TypeId target_type,
                              cir::TypeId source_type,
                              SrcLoc loc);
    struct ArcWriteback {
        cir::EntityId original{};
        cir::TypeId original_type{};
        cir::EntityId temporary{};
        cir::TypeId temporary_type{};
    };
    bool arc_prepare_writeback_argument(ExprResult& argument,
                                        std::vector<ArcWriteback>& writebacks,
                                        SrcLoc loc);
    void arc_emit_writebacks(const std::vector<ArcWriteback>& writebacks,
                             SrcLoc loc);
    ObjCForInControl begin_objc_for_in(std::string_view loop_var_name,
                                       cir::TypeRef loop_var_type,
                                       ExprResult collection,
                                       SrcLoc loc = SrcLoc());
    StmtResult finish_objc_for_in(ObjCForInControl& control,
                                  const StmtResult& body,
                                  SrcLoc loc = SrcLoc());
    cir::EntityId objc_ehtype_entity(cir::EntityId interface,
                                     SrcLoc loc = SrcLoc());
    cir::TypeId objc_id_pointee_type() const {
        return objc_.object_record_type;
    }
    ExprResult collect_objc_string_literal(std::string bytes,
                                           std::string spelling,
                                           SrcLoc loc = SrcLoc());
    bool is_objc_class_name(std::string_view name) const;
    cir::TypeId objc_class_object_type(std::string_view name) const;
    cir::EntityId objc_class_entity(std::string_view name) const {
        auto found = objc_.classes.find(std::string(name));
        return found == objc_.classes.end() ? cir::EntityId{} : found->second;
    }
    cir::EntityId current_objc_interface() const {
        return objc_.current_interface;
    }

    RecordFieldInput declare_anonymous_union_member(
        cir::TypeId union_type,
        cir::RecordMemberAccess access,
        SrcLoc loc = SrcLoc());
    DeclResult declare_anonymous_union_variable(
        cir::TypeId union_type,
        bool namespace_scope,
        DeclFlags flags,
        SrcLoc loc = SrcLoc());
    enum class DerivedToBasePathKind : uint8_t {
        NotFound,
        Unique,
        Ambiguous,
    };

    struct DerivedToBasePathResult {
        DerivedToBasePathKind kind = DerivedToBasePathKind::NotFound;
        std::vector<cir::EntityId> path;
    };

    DerivedToBasePathResult analyze_derived_to_base_path(
        cir::TypeId derived_type,
        cir::TypeId base_type) const;

    bool derived_to_base_path(cir::TypeId derived_type,
                              cir::TypeId base_type,
                              std::vector<cir::EntityId>* path_out) const;
    cir::TypeId member_function_type_with_this(cir::TypeId record_type,
                                               cir::TypeId declared_type);
    bool validate_static_member_function_type(cir::TypeId declared_type,
                                              SrcLoc loc = SrcLoc());
    bool validate_consteval_only_function_type(cir::TypeId declared_type,
                                               bool is_consteval,
                                               SrcLoc loc = SrcLoc());
    bool consteval_only_function_type_immediately_escalates(
        cir::TypeId declared_type,
        bool is_constexpr,
        cir::EntityKind kind,
        bool instantiated_templated_entity) const;
    void mark_function_immediate(cir::EntityId function);
    bool validate_consteval_only_object_definition(cir::EntityId entity,
                                                   cir::TypeId type,
                                                   bool is_constexpr,
                                                   SrcLoc loc = SrcLoc());
    FunctionDeclStart begin_member_function(cir::EntityId method_entity,
                                            const std::vector<ParamInput>& declared_params,
                                            SrcLoc loc = SrcLoc(),
                                            bool suppress_noexcept_region = false);
    void register_member_definition_default_arguments(
        cir::EntityId method_entity,
        const std::vector<ParamInput>& declared_params,
        SrcLoc loc = SrcLoc());
    void finish_member_function(StmtResult body, SrcLoc loc = SrcLoc());
    struct MemberDeclaratorThisScope {
        cir::TypeId previous_type{};
        bool previous_active = false;
    };
    MemberDeclaratorThisScope begin_member_declarator_this(
        cir::EntityId record,
        bool member_is_const,
        bool member_is_volatile,
        bool is_static);
    void finish_member_declarator_this(MemberDeclaratorThisScope scope);
    ExprResult collect_this_expr(SrcLoc loc = SrcLoc());
    bool in_member_function() const { return current_this_place_.valid(); }

    bool record_has_user_constructor(cir::TypeId type) const;
    cir::EntityId corresponding_record_method(cir::DeclContextId context,
                                              std::string_view name,
                                              cir::TypeRef type,
                                              bool ignore_exception_spec = false) const;
    const cir::RecordMethodFact* selected_record_destructor(
        cir::TypeId type) const;
    bool validate_potentially_invoked_destructor(cir::TypeId type,
                                                 SrcLoc loc = SrcLoc());
    cir::EntityId record_destructor(cir::TypeId type) const;
    DeclResult construct_variable(DeclResult started,
                                  std::vector<ExprResult> arguments,
                                  SrcLoc loc = SrcLoc(),
                                  ConstructorInitializationKind init_kind =
                                      ConstructorInitializationKind::Direct,
                                  bool value_initialize = false,
                                  bool full_expression_temporary = false);
    DeclResult default_construct_if_needed(DeclResult started,
                                           SrcLoc loc = SrcLoc());
    cir::EntityId temporary_entity_of_value(cir::InstId value) const;

    enum class LifetimeOwnerKind : uint8_t {
        LexicalScope,
        FullExpression,
        Parameter,
        Result,
        ExceptionObject,
        ConstructorRollback,
        StaticExit,
        ThreadExit,
        Retired,
    };
    struct LifetimeBoundary {
        bool active = false;
        bool owns_cleanup_scope = false;
        uint64_t id = 0;
        size_t scope_depth = 0;
    };
    using FullExpressionWatermark = LifetimeBoundary;
    LifetimeBoundary begin_lifetime_boundary();
    cir::Fragment finish_lifetime_boundary(const LifetimeBoundary& boundary,
                                           SrcLoc loc);
    cir::Fragment extend_lifetime_boundary_to_scope(
        const LifetimeBoundary& boundary,
        SrcLoc loc);
    void close_lifetime_boundary_without_cleanup(
        const LifetimeBoundary& boundary);
    void discard_lifetime_boundary(const LifetimeBoundary& boundary);
    LifetimeBoundary begin_full_expression() {
        return begin_lifetime_boundary();
    }
    cir::Fragment finish_full_expression(const LifetimeBoundary& boundary,
                                         SrcLoc loc) {
        return finish_lifetime_boundary(boundary, loc);
    }
    cir::LifetimeId register_destructor_cleanup(
        cir::EntityId entity,
        cir::TypeId type,
        SrcLoc loc = SrcLoc(),
        bool full_expression_temporary = false);
    cir::LifetimeId register_cleanup_with_function(
        cir::EntityId entity,
        cir::TypeId type,
        SrcLoc loc,
        bool full_expression_temporary,
        cir::EntityId cleanup_function,
        cir::EntityId unwind_cleanup_function,
        bool call_with_address);
    bool transfer_lifetime(cir::LifetimeId lifetime,
                           LifetimeOwnerKind owner,
                           uint64_t owner_id = 0);
    bool retire_lifetime(cir::LifetimeId lifetime);
    cir::LifetimeId lifetime_for_entity(cir::EntityId entity) const;
    cir::LifetimeId temporary_lifetime_of_value(cir::InstId value) const;
    bool adopt_materialized_object_storage(
        const ExprResult& source,
        cir::InstId destination_place,
        cir::EntityId destination_entity = {});
    bool adopt_materialized_result_storage(const ExprResult& source);
    bool remove_destructor_cleanup(cir::EntityId entity);
    struct ClassArrayShape {
        cir::TypeId array_type{};
        cir::TypeId leaf_type{};
        std::vector<uint64_t> extents;
        uint64_t total_leaf_count = 0;
        bool dependent = false;
        bool extent_overflow = false;

        bool valid() const {
            return array_type.valid() && leaf_type.valid() &&
                !dependent && !extent_overflow && total_leaf_count != 0;
        }
    };

    enum class ArrayLifecycleOperation : uint8_t {
        DefaultConstruct,
        ValueConstruct,
        CopyConstruct,
        MoveConstruct,
        CopyAssign,
        MoveAssign,
        Destroy,
    };

    struct ArrayLifecyclePlan {
        ClassArrayShape shape;
        ArrayLifecycleOperation operation =
            ArrayLifecycleOperation::DefaultConstruct;
        cir::EntityId element_function{};
        cir::StorageDuration storage_duration =
            cir::StorageDuration::Automatic;
        uint64_t first_leaf = 0;
        uint64_t past_last_leaf = 0;
        bool value_initialize = false;
        bool track_progress = false;

        bool valid() const {
            return shape.valid() && first_leaf <= past_last_leaf &&
                past_last_leaf <= shape.total_leaf_count;
        }
    };

    enum class RecordLifecycleOperation : uint8_t {
        DefaultConstruct,
        CopyConstruct,
        MoveConstruct,
        CopyAssign,
        MoveAssign,
        Destroy,
    };

    struct RecordLifecycleStep {
        cir::RecordFieldFact field;
        ClassArrayShape array_shape;
        bool complete_object_only = false;
    };

    struct RecordLifecyclePlan {
        RecordLifecycleOperation operation =
            RecordLifecycleOperation::DefaultConstruct;
        std::vector<RecordLifecycleStep> steps;
    };

    RecordLifecyclePlan record_lifecycle_plan(
        const cir::RecordFacts& facts,
        RecordLifecycleOperation operation) const;

    enum class ArrayDestructionMode : uint8_t {
        Normal,
        UnwindCleanup,
    };

    ClassArrayShape class_array_shape(cir::TypeId type) const;
    cir::TypeId array_class_element_leaf(cir::TypeId type) const;
    cir::Fragment array_destroy_loop_fragment(cir::InstId array_place,
                                              cir::TypeId array_type,
                                              cir::InstId count_value,
                                              SrcLoc loc,
                                              ArrayDestructionMode mode =
                                                  ArrayDestructionMode::Normal,
                                              const std::function<cir::InstId(
                                                  SrcLoc)>* action_place =
                                                  nullptr);
    cir::Fragment array_construct_loop_fragment(
        cir::InstId array_place,
        cir::TypeId array_type,
        uint64_t first_leaf,
        uint64_t past_last_leaf,
        SrcLoc loc,
        bool* had_error,
        const std::function<cir::InstId(SrcLoc)>* action_place = nullptr,
        cir::InstId shared_progress_place = {});
    cir::Fragment array_transfer_loop_fragment(
        cir::InstId destination_place,
        cir::InstId source_place,
        cir::TypeId array_type,
        cir::EntityId element_function,
        bool assign,
        bool is_move,
        SrcLoc loc,
        bool* had_error,
        const std::function<cir::InstId(SrcLoc)>* action_place = nullptr);
    cir::InstId rematerialize_entity_place(cir::InstId place, SrcLoc loc);
    cir::InstId begin_array_construct_unwind(
        cir::InstId array_place,
        cir::TypeId array_type,
        cir::TypeId leaf,
        cir::BlockId saved_target,
        SrcLoc loc,
        const std::function<cir::InstId(SrcLoc)>* action_place);
    cir::EntityId array_destroy_helper(
        cir::TypeId array_type,
        SrcLoc loc,
        ArrayDestructionMode mode = ArrayDestructionMode::Normal);
    cir::InstId flatten_array_place(cir::InstId array_place,
                                    cir::TypeId array_type,
                                    cir::TypeId leaf,
                                    size_t total,
                                    SrcLoc loc);
    StmtResult collect_member_initializer(std::string_view member_name,
                                          std::vector<ExprResult> arguments,
                                          SrcLoc loc = SrcLoc());
    struct MemberInitializerInput {
        std::string name;
        cir::TypeId base_type{};
        std::vector<ExprResult> arguments;
        SrcLoc loc{};
        LifetimeBoundary boundary;
        // The [class.base.init] lifetime invariant requires braced reference
        // member initializers to diagnose bindings to temporaries.
        bool braced = false;
    };
    StmtResult collect_constructor_initializers(
        std::vector<MemberInitializerInput> initializers,
        SrcLoc loc = SrcLoc());
    StmtResult collect_destructor_epilogue(SrcLoc loc = SrcLoc());
    bool vptr_field_path(cir::TypeId record_type,
                         std::vector<cir::EntityId>* path_out) const;
    StmtResult store_vptr_fragment(SrcLoc loc = SrcLoc());
    cir::EntityId synthesize_vtable_thunk(
        cir::EntityId target,
        cir::EntityId slot_declaration,
        const cir::VirtualAdjustmentFact& this_adjustment,
        const cir::VirtualAdjustmentFact& result_adjustment,
        SrcLoc loc);
    cir::EntityId synthesize_vtable_thunk(cir::EntityId target,
                                          size_t this_offset_bytes,
                                          SrcLoc loc);
    cir::EntityId record_copy_constructor(cir::TypeId type) const;
    cir::EntityId record_move_constructor(cir::TypeId type) const;
    cir::EntityId synthesize_deleting_destructor(cir::EntityId destructor,
                                                 SrcLoc loc);
    bool try_publish_constant_construction(
        DeclResult& started,
        const std::vector<ExprResult>& arguments,
        ConstructorInitializationKind init_kind,
        bool value_initialize,
        SrcLoc loc);
    bool try_publish_constant_initializer(cir::EntityId entity,
                                          cir::TypeId type,
                                          const ExprResult& initializer,
                                          SrcLoc loc,
                                          bool* diagnosed_error = nullptr,
                                          bool require_static_image = true);
    ExprResult clone_initializer_for_probe(
        const ExprResult& initializer) const;
    bool publish_automatic_constexpr_initializer(
        cir::EntityId entity,
        cir::TypeId type,
        const ExprResult& initializer,
        SrcLoc loc);
    bool write_static_const_value(std::vector<uint8_t>& bytes,
                                  size_t offset,
                                  cir::TypeId type,
                                  const ConstValue& value,
                                  SrcLoc loc,
                                  std::vector<cir::StaticInitializerRelocation>*
                                      relocations = nullptr);
    void publish_constant_state_from_static_initializer(
        cir::EntityId entity,
        cir::EntityId active_union_member = {});
    cir::EntityId union_active_member_from_initializer(
        cir::TypeId type,
        const ExprResult& initializer) const;
    DeclResult construct_global_variable(DeclResult started,
                                         std::vector<ExprResult> arguments,
                                         SrcLoc loc,
                                         ConstructorInitializationKind init_kind,
                                         bool value_initialize,
                                         std::optional<ExprResult> initializer =
                                             std::nullopt);
    // Namespace-scope scalar/aggregate dynamic initialization uses the same
    // ordered global-constructor aggregator as class construction.
    DeclResult initialize_global_variable(DeclResult started,
                                          ExprResult initializer,
                                          SrcLoc loc,
                                          ConstructorInitializationKind
                                              init_kind);
    DeclResult construct_local_static(DeclResult started,
                                      std::vector<ExprResult> arguments,
                                      SrcLoc loc,
                                      ConstructorInitializationKind init_kind,
                                      bool value_initialize,
                                      std::optional<ExprResult> initializer =
                                          std::nullopt);
    DeclResult construct_thread_variable(
        DeclResult started,
        std::vector<ExprResult> arguments,
        SrcLoc loc,
        ConstructorInitializationKind init_kind,
        bool value_initialize,
        std::optional<ExprResult> initializer = std::nullopt);
    cir::Fragment ensure_thread_initialized(cir::EntityId entity,
                                            SrcLoc loc);
    void finish_global_initialization(SrcLoc loc = SrcLoc());
    bool member_access_allowed(cir::EntityId member_owner,
                               cir::RecordMemberAccess access) const;
    bool member_access_allowed_from(cir::EntityId member_owner,
                                    cir::RecordMemberAccess access,
                                    cir::EntityId accessing_record,
                                    cir::EntityId accessing_function,
                                    bool infer_active_template_function = true) const;
    bool check_member_access_from(cir::EntityId member,
                                  cir::RecordMemberAccess access,
                                  cir::EntityId accessing_record,
                                  cir::EntityId accessing_function,
                                  SrcLoc loc);
    struct AccessCaptureToken {
        uint32_t index = 0;
        bool valid() const { return index != 0; }
    };
    AccessCaptureToken begin_access_capture();
    AccessCaptureToken begin_access_capture(AccessCaptureToken prefix);
    void suspend_access_capture(AccessCaptureToken capture);
    bool finish_access_capture(AccessCaptureToken capture,
                               cir::EntityId declaring_entity);
    void discard_access_capture(AccessCaptureToken capture);
    void add_pending_class_friend_type(cir::EntityId record,
                                       cir::TypeRef type,
                                       bool is_pack_expansion = false,
                                       SrcLoc loc = SrcLoc());
    void add_pending_friend_class_template(cir::EntityId record,
                                           cir::EntityId template_entity);
    cir::EntityId add_pending_friend_function(
        cir::EntityId record,
        std::string_view name,
        cir::TypeId type,
        cir::DeclContextId context,
        SrcLoc loc = SrcLoc(),
        cir::EntityId signature_owner = {},
        bool require_existing = false,
        cir::OperatorFunctionIdentity operator_function = {});
    uint32_t base_declaration_index(const cir::RecordFacts& facts,
                                    const cir::RecordFieldFact& field) const;
    void check_member_access(cir::EntityId member,
                             cir::RecordMemberAccess access,
                             SrcLoc loc);
    bool record_needs_construction(cir::TypeId type) const;
    bool record_requires_default_constructor_selection(cir::TypeId type) const;
    // The [class.access.base] invariant requires every subobject edge to be
    // accessible; [expr.cast] deliberately exempts C-style casts.
    bool protected_member_object_access_allowed(cir::EntityId member_owner,
                                                cir::TypeId object_type);
    bool check_base_path_access(const std::vector<cir::EntityId>& path,
                                cir::TypeId derived,
                                cir::TypeId base,
                                SrcLoc loc);
    cir::InstId emit_subobject_path(cir::InstId place,
                                    const std::vector<cir::EntityId>& path,
                                    SrcLoc loc);
    cir::InstId emit_virtual_base_adjust(cir::InstId place,
                                         cir::EntityId vbase_field,
                                         SrcLoc loc);
    cir::TypeId structor_impl_type(cir::TypeId with_this_type);
    cir::Fragment guard_on_structor_flag(cir::Fragment body, SrcLoc loc);
    cir::Fragment branch_on_structor_flag(cir::Fragment complete_body,
                                          cir::Fragment base_body,
                                          SrcLoc loc);
    struct VttInfo {
        struct Slice {
            cir::EntityId record_entity{};
            size_t offset = 0;
            size_t start = 0;
            size_t count = 0;
        };
        struct Site {
            bool is_virtual = false;
            cir::EntityId base_field{};
            std::vector<cir::EntityId> storage_path;
            size_t offset = 0;
            size_t address_point = 0;
        };
        size_t entry_count = 1;
        size_t sub_count = 1;
        size_t sites_start = 1;
        std::vector<Slice> base_slices;
        std::vector<Site> sites;
        std::vector<Slice> vbase_slices;
    };
    VttInfo compute_vtt_info(const cir::RecordFacts& facts) const;
    cir::EntityId emit_construction_vtable(const cir::RecordFacts& complete,
                                           const cir::RecordFacts& base,
                                           size_t offset,
                                           SrcLoc loc);
    void emit_virtual_table_table(cir::RecordFacts& facts, SrcLoc loc);
    cir::InstId load_vtt_entry(size_t index, SrcLoc loc);
    cir::InstId vtt_slice_value(size_t index, SrcLoc loc);
    cir::Fragment vtt_vptr_store_fragment(SrcLoc loc);
    cir::EntityId structor_complete_variant(cir::EntityId structor) const;
    cir::EntityId structor_base_variant(cir::EntityId structor) const;
    cir::EntityId structor_impl_entity(cir::EntityId structor) const;
    void ensure_structor_variants(cir::EntityId structor, SrcLoc loc);
    bool diagnose_constructor_delegation_cycle(
        cir::EntityId constructor,
        SrcLoc loc);
    cir::EntityId synthesize_structor_variant(cir::EntityId impl,
                                               bool complete,
                                               SrcLoc loc,
                                               cir::EntityId
                                                   inherited_origin = {});
    bool diagnose_abstract_instantiation(cir::TypeId type, SrcLoc loc);
    void mark_record_method_required(cir::EntityId method, SrcLoc loc);
    void mark_record_vtable_methods_required(cir::EntityId record_entity);
    enum class ConversionRank : uint8_t {
        Exact,
        Promotion,
        Conversion,
        UserDefined,
        Ellipsis,
        Bad
    };
    enum class TrailingBinding : uint8_t {
        None,
        LValueReference,
        RValueReference,
    };
    enum class StandardConversionStep : uint16_t {
        None = 0,
        LValueToRValue = 1u << 0,
        ArrayToPointer = 1u << 1,
        FunctionToPointer = 1u << 2,
        Promotion = 1u << 3,
        NumericConversion = 1u << 4,
        PointerConversion = 1u << 5,
        PointerToBool = 1u << 6,
        FunctionPointerConversion = 1u << 7,
        QualificationAdjustment = 1u << 8,
        DerivedToBase = 1u << 9,
        ReferenceBinding = 1u << 10,
        MemberPointerConversion = 1u << 11,
    };
    struct StandardConversionSequence {
        cir::TypeRef source;
        cir::TypeRef target;
        ValueCategory source_category = ValueCategory::Invalid;
        ConversionRank rank = ConversionRank::Bad;
        uint16_t steps = 0;
        cir::TypeId bound_referred{};
        uint8_t bound_qualifiers = 0;
        TrailingBinding trailing_binding = TrailingBinding::None;
        // The [dcl.init.ref] lifetime invariant records the temporary actually
        // bound without adding a conversion because [over.ics.rank] compares
        // conversion sets for identity.
        bool binds_converted_temporary = false;

        bool has(StandardConversionStep step) const {
            return (steps & static_cast<uint16_t>(step)) != 0;
        }
        void add(StandardConversionStep step) {
            steps |= static_cast<uint16_t>(step);
        }
    };
    struct ConversionDetail {
        StandardConversionSequence standard;
        cir::EntityId user_conversion{};
        bool user_conversion_unique = false;
        StandardConversionSequence trailing_standard;
        std::shared_ptr<ListInitializationPlan> list_plan;
    };
    int compare_implicit_conversion_sequences(
        ConversionRank lhs_rank,
        const ConversionDetail& lhs,
        ConversionRank rhs_rank,
        const ConversionDetail& rhs,
        bool implicit_object_parameter = false) const;
    struct UnevaluatedOperand {
        cir::TypeRef type;
        ValueCategory category = ValueCategory::Invalid;
        uint8_t object_qualifiers = cir::QualNone;

        bool valid() const {
            return type.valid() && category != ValueCategory::Invalid;
        }
    };
    enum class OperationProbeFailure : uint8_t {
        None,
        InvalidType,
        NoViableOperation,
        Ambiguous,
        Deleted,
        Inaccessible,
        Dependent,
    };
    struct OperationProbeStep {
        cir::EntityId callable{};
        bool trivial = true;
        bool nothrow = true;
    };
    struct OperationProbe {
        OperationProbeFailure failure = OperationProbeFailure::InvalidType;
        bool viable = false;
        bool trivial = false;
        bool nothrow = false;
        cir::EntityId selected{};
        std::vector<OperationProbeStep> steps;
    };
    UnevaluatedOperand make_declval_operand(cir::TypeRef type) const;
    ExprResult unevaluated_operand_view(
        const UnevaluatedOperand& operand) const;
    bool operation_probe_record_callable(OperationProbe& probe,
                                         cir::EntityId callable) const;
    bool operation_probe_public_base_conversion(cir::TypeId source,
                                                cir::TypeId target) const;
    bool operation_probe_standard_sequence_usable(
        const StandardConversionSequence& sequence) const;
    bool operation_probe_require_public_destructor(OperationProbe& probe,
                                                   cir::TypeId type) const;
    OperationProbe probe_implicit_conversion(cir::TypeRef from,
                                             cir::TypeRef to,
                                             bool core_convertibility = false);
    OperationProbe probe_assignment(cir::TypeRef lhs, cir::TypeRef rhs);
    OperationProbe probe_construction(
        cir::TypeRef target,
        const std::vector<cir::TypeRef>& arguments);
    bool probe_reference_binds_to_temporary(cir::TypeRef target,
                                            cir::TypeRef source);
    ConversionRank conversion_rank(cir::TypeId from,
                                   ValueCategory category,
                                   cir::TypeRef to,
                                   uint8_t from_qualifiers = 0,
                                   ConversionDetail* detail = nullptr,
                                   bool allow_user_defined = false,
                                   bool allow_explicit_conversion_functions =
                                       false,
                                   const ExprResult* source_expression =
                                       nullptr) const;
    ConversionRank conversion_rank(const ExprResult& from,
                                   cir::TypeRef to,
                                   uint8_t from_qualifiers = 0,
                                   ConversionDetail* detail = nullptr,
                                   bool allow_user_defined = false,
                                   bool allow_explicit_conversion_functions =
                                       false) const;
    std::optional<cir::TypeRef> initializer_list_element_type(
        cir::TypeId type) const;
    std::optional<cir::TypeRef> constructor_initializer_list_element_type(
        cir::EntityId constructor) const;
    struct UserConversionProbe {
        bool viable = false;
        cir::EntityId route{};
        bool unique = false;
    };
    UserConversionProbe probe_user_defined_conversion(cir::TypeId from,
                                                      ValueCategory category,
                                                      cir::TypeRef to,
                                                      bool allow_explicit_conversion_functions =
                                                          false,
                                                      const ExprResult*
                                                          source_expression =
                                                              nullptr) const;
    bool function_signatures_match(cir::TypeId lhs, cir::TypeId rhs) const;
    bool function_exception_specs_equivalent(cir::TypeId lhs,
                                             cir::TypeId rhs) const;
    struct OverloadAmbiguityInfo {
        bool has_unordered_associated_constraints = false;
        std::vector<SrcLoc> candidate_locs;
    };
    void describe_function_selection_ambiguity(
        const std::vector<cir::EntityId>& candidates,
        OverloadAmbiguityInfo& info);
    cir::EntityId select_overload(const std::vector<cir::EntityId>& candidates,
                                  const std::vector<ExprResult>& arguments,
                                  bool member_object_leading,
                                  bool* ambiguous_out = nullptr,
                                  cir::TypeId conversion_result_target = {},
                                  OverloadAmbiguityInfo* ambiguity_info =
                                      nullptr);
    bool callable_can_use_default_arguments(cir::EntityId entity,
                                            size_t provided_arguments,
                                            size_t hidden_arguments = 0) const;
    const ParamInput::DefaultArgument* callable_default_argument(
        cir::EntityId entity,
        size_t parameter_index) const;
    void register_function_template_default_arguments(
        cir::EntityId entity,
        const std::vector<ParamInput>& params,
        SrcLoc loc);
    void register_hidden_friend_default_arguments(
        cir::EntityId entity,
        const std::vector<ParamInput>& params,
        SrcLoc loc);
    void add_adl_candidates(std::string_view name,
                            const std::vector<ExprResult>& arguments,
                            std::vector<cir::EntityId>& candidates);
    bool record_has_member_name(cir::TypeId record_type,
                                std::string_view name) const;
    void report_overload_ambiguity_notes(
        const OverloadAmbiguityInfo& info,
        SrcLoc loc);
    cir::EntityId resolve_call_overload(ExprResult& callee,
                                        const std::vector<ExprResult>& arguments,
                                        SrcLoc loc);
    ExprResult try_overloaded_binary(syntax::BinaryOperator op,
                                     ExprResult& lhs,
                                     ExprResult& rhs,
                                     bool* handled,
                                     SrcLoc loc,
                                     bool allow_comparison_rewrites = true);
    void expand_operator_function_template_candidates(
        std::vector<cir::EntityId>& candidates,
        const std::vector<ExprResult>& ranking,
        SrcLoc loc);
    cir::EntityId select_overloaded_unary_candidate(
        syntax::UnaryOperator op,
        const ExprResult& operand,
        std::string* name_out,
        bool* postfix_out,
        bool* ambiguous_out,
        SrcLoc loc,
        bool diagnose);
    ExprResult try_overloaded_call(ExprResult& callee,
                                   std::vector<ExprResult>& args,
                                   bool* handled,
                                   SrcLoc loc);
    ExprResult try_overloaded_subscript(ExprResult& base,
                                        ExprResult& index,
                                        bool* handled,
                                        SrcLoc loc);
    ExprResult try_overloaded_unary(syntax::UnaryOperator op,
                                    ExprResult& operand,
                                    bool* handled,
                                    SrcLoc loc);
    cir::EntityId select_constructor(cir::TypeId record_type,
                                     const std::vector<ExprResult>& arguments,
                                     bool* ambiguous_out = nullptr,
                                     SrcLoc loc = SrcLoc(),
                                     ConstructorInitializationKind init_kind =
                                         ConstructorInitializationKind::Direct,
                                     bool demand_selected = true);
    enum class ImplicitMoveContext : uint8_t {
        Return,
        Throw,
    };
    struct ImplicitMoveEligibility {
        cir::EntityId entity{};
        bool eligible = false;
        bool nrvo_eligible = false;
        bool blocked_by_try_scope = false;
    };
    struct ObjectTransferSelection {
        ImplicitMoveEligibility move;
        cir::EntityId constructor{};
        ValueCategory selected_category = ValueCategory::LValue;
        bool used_fallback = false;
        bool ambiguous = false;
        bool has_error = false;
    };
    ImplicitMoveEligibility classify_implicit_move_operand(
        const ExprResult& source,
        ImplicitMoveContext context) const;
    ObjectTransferSelection select_object_transfer_constructor(
        cir::TypeId target_type,
        const ExprResult& source,
        ImplicitMoveContext context,
        SrcLoc loc = SrcLoc());
    enum class UserConversionContext : uint8_t {
        CopyInitialization,
        DirectInitialization,
        DirectConstructorReference,
        DirectReferenceBinding,
        ContextualBool,
        ContextualImplicit,
    };
    enum class PermittedImplicitTarget : uint8_t {
        IntegralOrEnum,
        PointerToObject,
        UnaryPlus,
    };
    cir::EntityId select_conversion_function(
        const ExprResult& source,
        cir::TypeId target_type,
        bool* ambiguous_out = nullptr,
        SrcLoc loc = SrcLoc(),
        UserConversionContext context =
            UserConversionContext::CopyInitialization);
    enum class OperatorRewriteKind : uint8_t {
        None,
        Equality,
        ThreeWay,
    };
    struct OverloadCandidate {
        cir::EntityId entity{};
        bool member_object_leading = false;
        bool ranks_conversion_result = false;
        bool is_rewritten_candidate = false;
        bool has_reversed_parameters = false;
        OperatorRewriteKind rewrite_kind = OperatorRewriteKind::None;
        cir::TypeId canonical_member_object_type{};
    };
    struct OverloadSelection {
        cir::EntityId entity{};
        OperatorRewriteKind rewrite_kind = OperatorRewriteKind::None;
        bool has_reversed_parameters = false;
        bool ambiguous = false;
    };
    cir::EntityId select_overload(const std::vector<OverloadCandidate>& candidates,
                                  const std::vector<ExprResult>& arguments,
                                  bool* ambiguous_out = nullptr,
                                  cir::TypeId conversion_result_target = {},
                                  OverloadAmbiguityInfo* ambiguity_info =
                                      nullptr,
                                  bool allow_user_defined_argument_conversions =
                                      true,
                                  cir::TypeId direct_constructor_target = {});
    OverloadSelection select_overload_detailed(
        const std::vector<OverloadCandidate>& candidates,
        const std::vector<ExprResult>& arguments,
        cir::TypeId conversion_result_target = {},
        OverloadAmbiguityInfo* ambiguity_info = nullptr,
        bool allow_user_defined_argument_conversions = true,
        cir::TypeId direct_constructor_target = {});
    void expand_operator_function_template_candidates(
        std::vector<OverloadCandidate>& candidates,
        const std::vector<ExprResult>& ranking,
        SrcLoc loc);
    struct UserConversionSequence {
        enum class Kind : uint8_t {
            None,
            Constructor,
            ConversionFunction,
            Ambiguous,
        };
        Kind kind = Kind::None;
        UserConversionContext context =
            UserConversionContext::CopyInitialization;
        StandardConversionSequence initial_standard;
        cir::EntityId callable{};
        StandardConversionSequence trailing_standard;
        bool explicit_candidate = false;
        enum class Usability : uint8_t {
            NotChecked,
            Usable,
            Deleted,
            Inaccessible,
        };
        Usability usability = Usability::NotChecked;
        OverloadAmbiguityInfo ambiguity;
    };
    UserConversionSequence resolve_initialization_user_conversion(
        const ExprResult& source,
        cir::TypeId target_type,
        UserConversionContext context,
        SrcLoc loc);
    UserConversionSequence resolve_permitted_implicit_conversion(
        const ExprResult& source,
        PermittedImplicitTarget permitted_target,
        cir::TypeId* target_type,
        SrcLoc loc);
    ExprResult apply_user_conversion_sequence(ExprResult source,
                                              cir::TypeId target_type,
                                              const UserConversionSequence& sequence,
                                              SrcLoc loc);
    void collect_constructor_candidates(cir::TypeId record_type,
                                        const std::vector<ExprResult>& arguments,
                                        ConstructorInitializationKind init_kind,
                                        SrcLoc loc,
                                        std::vector<cir::EntityId>& candidates);
    void collect_conversion_function_candidates(
        const ExprResult& source,
        cir::TypeId target_type,
        bool allow_explicit,
        SrcLoc loc,
        std::vector<cir::EntityId>& candidates);
    void retain_selected_conversion_template_emission(
        cir::EntityId selected,
        const std::vector<cir::EntityId>& candidates);
    cir::BindingId bind_callable(std::string_view name,
                                 cir::EntityId entity,
                                 cir::TypeId type,
                                 bool is_definition,
                                 SrcLoc loc = SrcLoc());
    void refresh_callable_binding(std::string_view name,
                                  cir::EntityId entity,
                                  cir::TypeId type,
                                  bool is_definition,
                                  SrcLoc loc = SrcLoc());
    void diagnose_cxx_callable_redeclaration(const cir::Binding& previous,
                                             std::string_view name,
                                             cir::TypeId new_type,
                                             SrcLoc loc);
    cir::PlaceholderResultFactId register_placeholder_result(
        cir::EntityId entity,
        cir::TypeId declared_function_type,
        const cir::Binding* previous,
        SrcLoc loc);
    cir::TypeId rebuild_function_result(cir::TypeId function_type,
                                        cir::TypeRef result);
    cir::TypeRef deduce_placeholder_return_candidate(
        const cir::PlaceholderResultFact& fact,
        const ExprResult* operand,
        SrcLoc loc,
        bool* deferred_pattern_candidate = nullptr);
    bool record_placeholder_return(const ExprResult* operand,
                                   SrcLoc loc,
                                   bool* deferred_pattern_candidate = nullptr);
    void publish_placeholder_result(cir::PlaceholderResultFactId fact_id,
                                    cir::TypeRef result,
                                    SrcLoc loc,
                                    bool final);

    enum class TemplateParameterKind : uint8_t {
        Type,
        NonType,
        Template,
    };
    enum class TemplateTemplateParameterKind : uint8_t {
        Type,
        Variable,
        Concept,
    };
    struct TemplateParameter {
        std::string name;
        TemplateParameterKind kind = TemplateParameterKind::Type;
        TemplateTemplateParameterKind template_template_parameter_kind =
            TemplateTemplateParameterKind::Type;
        uint32_t depth = 0;
        uint32_t index = 0;
        bool is_parameter_pack = false;
        cir::EntityId entity{};
        cir::TypeId type_param_type{};
        cir::TypeId non_type_type{};
        std::shared_ptr<TemplateInfo> nested_head;
        std::optional<cir::TemplateArgument> default_argument;
        bool requires_complete_class_default_replay = false;
        size_t default_argument_token_begin = 0;
        size_t default_argument_token_end = 0;
        cir::DeclContextId default_argument_context{};
        uint64_t default_argument_lookup_generation = 0;
        SrcLoc loc{};

        bool is_type_parameter() const {
            return kind == TemplateParameterKind::Type;
        }
        bool is_non_type_parameter() const {
            return kind == TemplateParameterKind::NonType;
        }
        bool is_template_parameter() const {
            return kind == TemplateParameterKind::Template;
        }
        const std::vector<TemplateParameter>& nested_parameters() const;
    };
    using TemplateArgumentBindingKind = cir::TemplateArgumentBindingKind;
    enum class TemplateArgumentBindingMode : uint8_t {
        Canonical,
        FunctionExplicitPrefix,
        DeducedCanonical,
    };
    enum class TemplateArgumentCompletionMode : uint8_t {
        Required,
        Candidate,
    };
    using TemplateArgumentBinding = cir::TemplateArgumentBinding;
    using TemplateArgumentBindings = cir::TemplateArgumentBindings;
    enum class NormalizedConstraintKind : uint8_t {
        Atomic,
        ConceptDependent,
        Conjunction,
        Disjunction,
        FoldExpanded
    };
    enum class ConstraintFoldOperator : uint8_t {
        LogicalAnd,
        LogicalOr
    };
    enum class ConstraintFoldExpansionParameterKind : uint8_t {
        Function,
        Type,
        Value,
        Template
    };
    struct ConstraintFoldExpansionParameter {
        ConstraintFoldExpansionParameterKind kind =
            ConstraintFoldExpansionParameterKind::Type;
        std::string name;
        uint32_t parameter_depth = 0;
        uint32_t parameter_index =
            cir::ArrayTypePayload::no_extent_param;
        cir::EntityId parameter_entity{};
        cir::EntityId owning_template_entity{};
        TemplateTemplateParameterKind template_template_parameter_kind =
            TemplateTemplateParameterKind::Type;
        cir::TypeId type_parameter_pack_type{};
        cir::TemplateArgument argument;
        std::optional<std::vector<cir::TemplateArgument>> argument_pack;
    };
    struct ConstraintParameterMapping {
        TemplateParameterKind parameter_kind = TemplateParameterKind::Type;
        uint32_t parameter_depth = 0;
        uint32_t parameter_index =
            cir::ArrayTypePayload::no_extent_param;
        cir::EntityId parameter_entity{};
        TemplateTemplateParameterKind parameter_template_template_kind =
            TemplateTemplateParameterKind::Type;
        bool parameter_is_pack = false;
        cir::TemplateArgument argument;
        std::optional<std::vector<cir::TemplateArgument>> argument_pack;

        bool same_parameter_as(
            const ConstraintParameterMapping& other) const {
            if (parameter_entity.valid() || other.parameter_entity.valid()) {
                return parameter_entity == other.parameter_entity;
            }
            return parameter_kind == other.parameter_kind &&
                   parameter_depth == other.parameter_depth &&
                   parameter_index == other.parameter_index &&
                   (parameter_kind != TemplateParameterKind::Template ||
                    parameter_template_template_kind ==
                        other.parameter_template_template_kind);
        }
    };
    struct ConstraintParameterReference {
        TemplateParameterKind parameter_kind = TemplateParameterKind::Type;
        uint32_t parameter_depth = 0;
        uint32_t parameter_index =
            cir::ArrayTypePayload::no_extent_param;
        cir::EntityId parameter_entity{};
        cir::TypeId parameter_type{};
        cir::EntityId owning_template_entity{};
    };
    struct ConstraintAtomIdentity {
        cir::EntityId appearance_owner{};
        size_t expression_begin = 0;
        size_t expression_end = 0;
        std::vector<ConstraintParameterMapping> parameter_mapping;
        uint64_t declaration_equivalence_key = 0;

        bool same_appearance_as(const ConstraintAtomIdentity& other) const {
            return appearance_owner == other.appearance_owner &&
                   expression_begin == other.expression_begin &&
                   expression_end == other.expression_end;
        }
    };
    struct NormalizedConstraintNode {
        NormalizedConstraintKind kind = NormalizedConstraintKind::Atomic;
        ConstraintAtomIdentity atom;
        cir::EntityId concept_id_entity{};
        uint32_t concept_id_template_parameter_index =
            cir::ArrayTypePayload::no_extent_param;
        cir::TypeRef concept_id_dependent_qualifier;
        cir::NameId concept_id_name{};
        bool concept_id_qualified_name = false;
        size_t concept_id_argument_list_begin = 0;
        size_t concept_id_argument_list_end = 0;
        std::vector<cir::TemplateArgument> concept_id_arguments;
        uint32_t lhs = UINT32_MAX;
        uint32_t rhs = UINT32_MAX;
        ConstraintFoldOperator fold_operator =
            ConstraintFoldOperator::LogicalAnd;
        std::vector<ConstraintFoldExpansionParameter>
            fold_expansion_parameters;
        TemplateArgumentBindings fold_pattern_argument_bindings;
    };
    struct NormalizedConstraint {
        static constexpr uint32_t no_node = UINT32_MAX;

        uint32_t root = no_node;
        std::vector<NormalizedConstraintNode> nodes;
        cir::TemplateValueExpression value_expression;
        std::vector<ConstraintParameterReference> referenced_parameters;

        bool empty() const {
            return root == no_node;
        }

        bool valid_node(uint32_t index) const {
            return index != no_node && index < nodes.size();
        }

        uint32_t add_atomic(ConstraintAtomIdentity atom) {
            NormalizedConstraintNode node;
            node.kind = NormalizedConstraintKind::Atomic;
            node.atom = std::move(atom);
            return append_node(std::move(node));
        }

        uint32_t add_concept_dependent(ConstraintAtomIdentity atom) {
            NormalizedConstraintNode node;
            node.kind = NormalizedConstraintKind::ConceptDependent;
            node.atom = std::move(atom);
            return append_node(std::move(node));
        }

        uint32_t add_conjunction(uint32_t lhs, uint32_t rhs) {
            return add_binary(NormalizedConstraintKind::Conjunction,
                              lhs,
                              rhs);
        }

        uint32_t add_disjunction(uint32_t lhs, uint32_t rhs) {
            return add_binary(NormalizedConstraintKind::Disjunction,
                              lhs,
                              rhs);
        }

        uint32_t add_fold_expanded(
            ConstraintFoldOperator op,
            uint32_t constraint,
            std::vector<ConstraintFoldExpansionParameter>
                expansion_parameters = {}) {
            NormalizedConstraintNode node;
            node.kind = NormalizedConstraintKind::FoldExpanded;
            node.fold_operator = op;
            node.lhs = constraint;
            node.fold_expansion_parameters =
                std::move(expansion_parameters);
            return append_node(std::move(node));
        }

        uint32_t append_copy_of(const NormalizedConstraint& source,
                                uint32_t source_root = no_node) {
            uint32_t root_to_copy =
                source_root == no_node ? source.root : source_root;
            if (!source.valid_node(root_to_copy)) {
                return no_node;
            }
            if (nodes.empty() && source_root == no_node) {
                value_expression = source.value_expression;
                referenced_parameters = source.referenced_parameters;
            } else {
                value_expression = {};
                for (const ConstraintParameterReference& reference :
                     source.referenced_parameters) {
                    auto same = [&](const ConstraintParameterReference& item) {
                        if (reference.parameter_entity.valid() ||
                            item.parameter_entity.valid()) {
                            return reference.parameter_entity ==
                                   item.parameter_entity;
                        }
                        if (reference.parameter_type.valid() ||
                            item.parameter_type.valid()) {
                            return reference.parameter_type ==
                                   item.parameter_type;
                        }
                        return reference.parameter_kind ==
                                   item.parameter_kind &&
                               reference.parameter_depth ==
                                   item.parameter_depth &&
                               reference.parameter_index ==
                                   item.parameter_index &&
                               reference.owning_template_entity ==
                                   item.owning_template_entity;
                    };
                    if (std::find_if(referenced_parameters.begin(),
                                     referenced_parameters.end(),
                                     same) == referenced_parameters.end()) {
                        referenced_parameters.push_back(reference);
                    }
                }
            }
            std::vector<uint32_t> remap(source.nodes.size(), no_node);
            return append_copy_node(source, root_to_copy, remap);
        }

    private:
        uint32_t append_node(NormalizedConstraintNode node) {
            nodes.push_back(std::move(node));
            uint32_t index = static_cast<uint32_t>(nodes.size() - 1);
            root = index;
            return index;
        }

        uint32_t add_binary(NormalizedConstraintKind kind,
                            uint32_t lhs,
                            uint32_t rhs) {
            NormalizedConstraintNode node;
            node.kind = kind;
            node.lhs = lhs;
            node.rhs = rhs;
            return append_node(std::move(node));
        }

        uint32_t append_copy_node(const NormalizedConstraint& source,
                                  uint32_t source_index,
                                  std::vector<uint32_t>& remap) {
            if (!source.valid_node(source_index)) {
                return no_node;
            }
            if (remap[source_index] != no_node) {
                return remap[source_index];
            }

            NormalizedConstraintNode node = source.nodes[source_index];
            if (source.valid_node(node.lhs)) {
                node.lhs = append_copy_node(source, node.lhs, remap);
            }
            if (source.valid_node(node.rhs)) {
                node.rhs = append_copy_node(source, node.rhs, remap);
            }
            uint32_t copied = append_node(std::move(node));
            remap[source_index] = copied;
            return copied;
        }
    };
    struct PatternHole {
        enum class Kind : uint8_t {
            Statement,
            ConstexprIf,
            ExpansionStatement
        };
        size_t token_begin = 0;
        size_t token_end = 0;
        size_t event_watermark = 0;
        Kind kind = Kind::Statement;
    };
    struct PatternScopeEvent {
        enum class Kind : uint8_t {
            EnterScope,
            LeaveScope,
            DeclareLocal,
            DeclareBlockFunction
        };
        Kind kind = Kind::EnterScope;
        cir::EntityId entity{};
        cir::InstId place{};
        uint64_t lookup_generation = 0;
    };
    struct CapturedMemberParam {
        std::string name;
        cir::TypeId type{};
        cir::TypeRef type_ref{};
        SrcLoc loc{};
        AttributeList attrs;
        bool has_default_argument = false;
        size_t default_argument_begin = 0;
        size_t default_argument_end = 0;
        SrcLoc default_argument_loc{};
        bool is_parameter_pack = false;
        std::string source_parameter_pack_name;
        bool is_parameter_pack_expansion_sentinel = false;
        bool type_originates_from_template_parameter = false;
        cir::DeclContextId default_argument_declaration_context{};
        uint64_t default_argument_lookup_generation = 0;
        bool default_argument_requires_complete_class_replay = false;
    };
    struct CapturedMemberBody {
        size_t method_index = 0;
        size_t body_begin = 0;
        size_t body_end = 0;
        size_t init_begin = 0;
        size_t init_end = 0;
        bool is_constructor_function_try = false;
        bool transferable = true;
        std::vector<CapturedMemberParam> params;
    };
    void stash_captured_member_body(uint64_t template_entity_index,
                                    CapturedMemberBody body);
    const std::unordered_map<uint64_t, CapturedMemberBody>&
    captured_member_bodies() const;
    std::vector<std::pair<uint64_t, const CapturedMemberBody*>>
    captured_member_bodies_for_unit(cir::ModuleAttachmentId unit) const;

    struct MemberPattern {
        cir::EntityId method{};
        cir::FunctionId function{};
        size_t body_token_begin = 0;
        size_t body_start_block = 0;
        size_t body_block_count = 0;
        uint32_t hole_index_base = 0;
        std::vector<PatternHole> holes;
        std::vector<PatternScopeEvent> events;
        bool usable = true;
    };
    struct TemplateInfo {
        cir::EntityId entity{};
        std::string name;
        cir::OperatorFunctionIdentity operator_function;
        uint32_t template_parameter_index =
            cir::ArrayTypePayload::no_extent_param;
        bool is_class_template = false;
        bool is_alias_template = false;
        bool is_variable_template = false;
        bool is_concept = false;
        bool has_internal_linkage = false;
        bool is_template_parameter_pack = false;
        bool is_partial_specialization = false;
        bool is_member_template_specialization_overlay = false;
        bool is_candidate_neutral_argument_recipe = false;
        cir::RecordKind record_kind = cir::RecordKind::Struct;
        std::vector<TemplateParameter> parameters;
        struct InventedFunctionParameter {
            uint32_t function_parameter_index = 0;
            uint32_t placeholder_index = 0;
            uint32_t template_parameter_index =
                cir::ArrayTypePayload::no_extent_param;
            SrcLoc loc{};
        };
        std::vector<InventedFunctionParameter>
            invented_function_parameters;
        struct FunctionConstraintParameter {
            std::string name;
            cir::TypeRef type{};
            SrcLoc loc{};
            bool is_parameter_pack = false;
            std::string source_parameter_pack_name;
            bool is_parameter_pack_expansion_sentinel = false;
            bool type_originates_from_template_parameter = false;
        };
        std::vector<FunctionConstraintParameter>
            function_constraint_parameters;
        size_t complete_class_head_begin = 0;
        size_t complete_class_head_end = 0;
        bool has_complete_class_default_recipes = false;
        enum class IntroducedConstraintKind : uint8_t {
            TemplateParameterTypeConstraint,
            TemplateHeadRequires,
            FunctionParameterTypeConstraint,
            FunctionTrailingRequires
        };
        struct IntroducedConstraint {
            IntroducedConstraintKind kind =
                IntroducedConstraintKind::TemplateHeadRequires;
            size_t begin = 0;
            size_t end = 0;
            uint32_t constrained_parameter_index =
                cir::ArrayTypePayload::no_extent_param;
            cir::EntityId type_constraint_concept{};
            std::vector<cir::TemplateArgument> type_constraint_arguments;
            SrcLoc loc{};
            std::optional<NormalizedConstraint> normal_form;
        };
        static constexpr uint8_t associated_constraint_order(
            IntroducedConstraintKind kind) {
            return static_cast<uint8_t>(kind);
        }
        static bool associated_constraint_order_less(
            const IntroducedConstraint& lhs,
            const IntroducedConstraint& rhs) {
            return associated_constraint_order(lhs.kind) <
                associated_constraint_order(rhs.kind);
        }
        std::vector<IntroducedConstraint> introduced_constraints;
        AttributeList declaration_attrs;
        cir::TypeId alias_target_type{};
        cir::TypeRef alias_target_type_ref{};
        size_t alias_type_attribute_begin = 0;
        size_t alias_type_attribute_end = 0;
        enum class AliasTypeTransformKind : uint8_t {
            None,
            VectorSize,
            ExtVectorType,
            NeonVectorType
        };
        AliasTypeTransformKind alias_type_transform_kind =
            AliasTypeTransformKind::None;
        uint32_t alias_type_transform_parameter = UINT32_MAX;
        struct AliasDeductionProjection {
            cir::EntityId target_template{};
            std::vector<cir::TemplateArgument> target_arguments;
        };
        std::optional<AliasDeductionProjection> alias_deduction_projection;
        cir::TypeId variable_type{};
        cir::TypeRef variable_type_ref{};
        bool variable_const_qualification_is_implicit = false;
        cir::DeclSemanticFlags variable_decl_flags{};
        bool variable_is_extern = false;
        bool variable_is_static = false;
        size_t constraint_begin = 0;
        size_t constraint_end = 0;
        std::optional<NormalizedConstraint> constraint_normal_form;
        size_t definition_begin = 0;
        size_t definition_end = 0;
        bool has_definition = false;
        bool is_deleted = false;
        bool hidden_friend_definition_is_pattern = false;
        cir::DeclContextId lexical_context{};
        cir::FunctionId pattern_function{};
        cir::GenericId pattern_generic{};
        bool pattern_usable = false;
        uint64_t definition_generation = 0;
        std::vector<PatternHole> pattern_holes;
        std::vector<PatternScopeEvent> pattern_events;
        cir::EntityId pattern_record{};
        std::vector<MemberPattern> member_patterns;
        struct StaticDataMemberInitializer {
            std::string name;
            size_t begin = 0;
            size_t end = 0;
            SrcLoc loc{};
            cir::DeclContextId declaration_context{};
            uint64_t lookup_generation = 0;
            cir::TemplateValueExpression value_expression;
        };
        std::vector<StaticDataMemberInitializer>
            static_data_member_initializers;
        cir::TypeId pattern_type{};
        std::vector<cir::TypeId> param_types;
        struct TemplateInstantiationBinding {
            std::vector<TemplateParameter> parameters;
            TemplateArgumentBindings argument_bindings;
        };
        std::vector<TemplateInstantiationBinding>
            enclosing_instantiation_bindings;
        struct OutOfLineMember {
            size_t begin = 0;
            size_t end = 0;
            bool is_template_declaration = false;
            bool is_static_data_member_definition = false;
            std::vector<TemplateParameter> head_parameters;
            std::vector<uint32_t> head_parameter_owner_slots;
        };
        std::vector<OutOfLineMember> out_of_line_members;
        struct ExplicitMemberFunctionSpecialization {
            std::string owner_memo_key;
            std::string member_name;
            cir::TypeRef member_type{};
            SrcLoc loc{};
        };
        std::vector<ExplicitMemberFunctionSpecialization>
            explicit_member_function_specializations;
        struct ExplicitStaticDataMemberSpecialization {
            std::string owner_memo_key;
            std::string member_name;
            cir::TypeRef member_type{};
            SrcLoc loc{};
        };
        std::vector<ExplicitStaticDataMemberSpecialization>
            explicit_static_data_member_specializations;
        struct PartialSpecialization {
            cir::EntityId entity{};
            std::vector<cir::TemplateArgument> arguments;
            SrcLoc loc{};
        };
        std::vector<PartialSpecialization> partial_specializations;
        struct DeductionGuide {
            cir::TypeId pattern_type{};
            std::vector<uint8_t> parameter_default_argument_flags;
            std::vector<TemplateParameter> parameters;
            std::vector<cir::TemplateArgument> return_arguments;
            std::vector<IntroducedConstraint> introduced_constraints;
            SrcLoc loc{};
            cir::DeclContextId declaration_context{};
            uint64_t declaration_generation = 0;
            std::optional<cir::RecordMemberAccess> declared_member_access;
            bool is_explicit = false;
            cir::ExplicitSpecifierKind explicit_specifier =
                cir::ExplicitSpecifierKind::Absent;
            size_t explicit_expression_begin = 0;
            size_t explicit_expression_end = 0;
            cir::TemplateValueExpression explicit_value_expression;
            cir::DeclContextId explicit_declaration_context{};
            uint64_t explicit_lookup_generation = 0;
        };
        std::vector<DeductionGuide> deduction_guides;
        cir::ExplicitSpecifierKind explicit_specifier =
            cir::ExplicitSpecifierKind::Absent;
        size_t explicit_expression_begin = 0;
        size_t explicit_expression_end = 0;
        cir::TemplateValueExpression explicit_value_expression;
    };
    struct PrototypeParameterScope {
        bool active = false;
        std::vector<cir::EntityId> entities;
    };
    PrototypeParameterScope begin_prototype_parameter_scope();
    cir::EntityId bind_prototype_parameter(
        PrototypeParameterScope& scope,
        const TemplateInfo::FunctionConstraintParameter& parameter);
    void finish_prototype_parameter_scope(PrototypeParameterScope scope);
    PrototypeParameterScope begin_function_constraint_parameter_scope(
        const std::vector<TemplateInfo::FunctionConstraintParameter>&
            parameters);
    void finish_function_constraint_parameter_scope(
        PrototypeParameterScope scope);
    using TemplateArgument = cir::TemplateArgument;
    struct PatternInstantiationCallbacks;
    struct PartialSpecializationSelection {
        const TemplateInfo* info = nullptr;
        TemplateArgumentBindings argument_bindings;
        bool is_ambiguous = false;
        bool has_unordered_associated_constraints = false;
        std::vector<SrcLoc> candidate_locs;
    };
    using FunctionTemplateInstantiationCallback = std::function<cir::EntityId(
        const TemplateInfo&,
        const TemplateArgumentBindings&,
        SrcLoc)>;
    using PatternInstantiationCallbackConfigurator = std::function<void(
        PatternInstantiationCallbacks&,
        SrcLoc)>;
    using ClassTemplatePlaceholderDeductionCallback =
        std::function<cir::TypeId(
            const TemplateInfo&,
            const ExprResult&,
            SrcLoc,
            bool)>;
    enum class InstantiationDemandResult : uint8_t {
        Satisfied,
        Unavailable,
        Failed,
    };
    enum class TemplateReplayDisposition : uint8_t {
        Success,
        SubstitutionFailure,
        Unavailable,
        HardError,
    };
    struct TemplateReplayOutcome {
        TemplateReplayDisposition disposition =
            TemplateReplayDisposition::Success;
        cir::EntityId blocker{};

        void note_unavailable(cir::EntityId entity = {}) {
            if (disposition == TemplateReplayDisposition::HardError) {
                return;
            }
            disposition = TemplateReplayDisposition::Unavailable;
            if (!blocker.valid()) {
                blocker = entity;
            }
        }
        void note_substitution_failure() {
            if (disposition == TemplateReplayDisposition::Success) {
                disposition =
                    TemplateReplayDisposition::SubstitutionFailure;
            }
        }
        void note_hard_error() {
            disposition = TemplateReplayDisposition::HardError;
        }
        bool substitution_failure() const {
            return disposition ==
                TemplateReplayDisposition::SubstitutionFailure;
        }
        bool unavailable() const {
            return disposition == TemplateReplayDisposition::Unavailable;
        }
        bool hard_error() const {
            return disposition == TemplateReplayDisposition::HardError;
        }
    };
    using ClassInstantiationDemandCallback =
        std::function<InstantiationDemandResult(
            cir::EntityId,
            cir::InstantiationDemandKind,
            cir::EntityId,
            SrcLoc)>;
    using FunctionInstantiationDemandCallback =
        std::function<InstantiationDemandResult(
            cir::EntityId,
            cir::InstantiationDemandKind,
            SrcLoc)>;
    using DefaultArgumentReplayCallback = std::function<ExprResult(
        cir::EntityId,
        size_t,
        SrcLoc)>;
    FunctionTemplateInstantiationCallback
    set_function_template_instantiation_callback(
        FunctionTemplateInstantiationCallback callback);
    bool has_function_template_instantiation_callback() const;
    cir::EntityId form_function_template_specialization_candidate(
        const TemplateInfo& info,
        const TemplateArgumentBindings& argument_bindings,
        SrcLoc loc);
    PatternInstantiationCallbackConfigurator
    set_pattern_instantiation_callback_configurator(
        PatternInstantiationCallbackConfigurator callback);
    ClassTemplatePlaceholderDeductionCallback
    set_class_template_placeholder_deduction_callback(
        ClassTemplatePlaceholderDeductionCallback callback);
    ClassInstantiationDemandCallback
    set_class_instantiation_demand_callback(
        ClassInstantiationDemandCallback callback);
    FunctionInstantiationDemandCallback
    set_function_instantiation_demand_callback(
        FunctionInstantiationDemandCallback callback);
    InstantiationDemandResult request_class_instantiation(
        cir::EntityId specialization,
        cir::InstantiationDemandKind kind,
        SrcLoc loc,
        cir::EntityId subject = {});
    InstantiationDemandResult request_class_member_instantiation(
        cir::EntityId subject,
        cir::InstantiationDemandKind kind,
        SrcLoc loc);
    InstantiationDemandResult request_function_instantiation(
        cir::EntityId specialization,
        cir::InstantiationDemandKind kind,
        SrcLoc loc);
    bool require_placeholder_result(cir::EntityId function,
                                    cir::InstantiationDemandKind kind,
                                    SrcLoc loc);
    InstantiationDemandResult require_complete_class_type_result(
        cir::TypeId type,
        SrcLoc loc,
        cir::InstantiationDemandKind reason =
            cir::InstantiationDemandKind::CompleteClass);
    bool require_complete_class_type(
        cir::TypeId type,
        SrcLoc loc,
        cir::InstantiationDemandKind reason =
            cir::InstantiationDemandKind::CompleteClass);
    TemplateReplayOutcome* set_template_replay_outcome(
        TemplateReplayOutcome* outcome) {
        TemplateReplayOutcome* previous = template_replay_outcome_;
        template_replay_outcome_ = outcome;
        return previous;
    }
    TemplateReplayOutcome* current_template_replay_outcome() const {
        return template_replay_outcome_;
    }
    DefaultArgumentReplayCallback set_default_argument_replay_callback(
        DefaultArgumentReplayCallback callback);
    using DefaultMemberInitializerReplayCallback =
        std::function<ExprResult(cir::EntityId, cir::InstId, SrcLoc)>;
    DefaultMemberInitializerReplayCallback
    set_default_member_initializer_replay_callback(
        DefaultMemberInitializerReplayCallback callback);
    struct DefaultArgumentReplayInfo {
        const ParamInput::DefaultArgument* argument = nullptr;
        const TemplateInfo* template_info = nullptr;
        std::vector<TemplateArgument> arguments;
        cir::DeclContextId declaration_context{};
        SrcLoc point_of_instantiation{};
        uint64_t point_lookup_generation = 0;
    };
    enum class TemplateInstantiationRequestKind : uint8_t {
        TemplateReplay,
        FunctionDefaultArgument,
        TemplateArgumentCompletion,
        TemplateArgumentListParsing,
        ClassInstantiationDemand,
        FunctionInstantiationDemand,
    };
    struct TemplateInstantiationRequest {
        uint64_t id = 0;
        uint64_t parent_id = 0;
        uint64_t duplicate_of_id = 0;
        TemplateInstantiationRequestKind kind =
            TemplateInstantiationRequestKind::TemplateReplay;
        cir::EntityId template_entity{};
        std::string memo_key;
        std::string display_name;
        SrcLoc point{};
        uint64_t point_lookup_generation = 0;
    };
    const std::vector<TemplateInstantiationRequest>&
    template_instantiation_requests() const;
    DefaultArgumentReplayInfo prepare_default_argument_replay(
        cir::EntityId entity,
        size_t parameter_index,
        SrcLoc use_loc = SrcLoc());
    ExprResult initialize_default_argument(ExprResult argument,
                                           cir::TypeId parameter_type,
                                           SrcLoc loc);
    struct CompleteClassDefaultArgumentRef {
        cir::EntityId entity{};
        size_t parameter_index = 0;
        SrcLoc loc{};
    };
    std::vector<CompleteClassDefaultArgumentRef>
        prepare_complete_class_default_arguments(
            cir::EntityId record,
            uint64_t lookup_generation);
    bool resolve_record_method_noexcept(
        cir::EntityId method,
        cir::FunctionExceptionSpec exception_spec);
    bool resolve_record_field_initializer_exception(
        cir::EntityId field,
        bool potentially_throwing,
        bool dependent);
    cir::InstId make_complete_class_validation_object(
        cir::EntityId record,
        SrcLoc loc);
    cir::EntityId create_member_template_specialization(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        cir::TypeId declared_type,
        SrcLoc loc = SrcLoc(),
        const DeclFlags* explicit_specialization_flags = nullptr,
        const TemplateArgumentBindings* exact_bindings = nullptr,
        bool defer_inherited_constructor_definition = false);
    bool define_inherited_constructor_template_specialization(
        cir::EntityId specialization,
        SrcLoc loc);
    cir::EntityId declare_hidden_friend_class_template(
        TemplateInfo info,
        cir::DeclContextId context,
        SrcLoc loc = SrcLoc());
    cir::EntityId declare_template(TemplateInfo info, SrcLoc loc);
    bool add_deduction_guide(cir::EntityId primary_entity,
                             TemplateInfo::DeductionGuide guide,
                             SrcLoc loc);
    void add_pending_friend_function_template(cir::EntityId record,
                                              cir::EntityId template_entity);
    void add_pending_friend_function_template_specialization(
        cir::EntityId record,
        cir::EntityId template_entity,
        std::vector<TemplateArgument> arguments,
        cir::TypeId function_type);
    void add_pending_dependent_member_friend_type(
        cir::EntityId record,
        cir::TypeRef friend_type,
        const std::vector<TemplateParameter>& parameters,
        SrcLoc loc = SrcLoc());
    void add_pending_dependent_member_friend_function(
        cir::EntityId record,
        cir::TypeRef qualifier_pattern,
        std::string_view name,
        cir::TypeRef function_type_pattern,
        const std::vector<TemplateParameter>& parameters,
        SrcLoc loc = SrcLoc());
    void add_pending_dependent_member_friend_function_template(
        cir::EntityId record,
        cir::TypeRef qualifier_pattern,
        std::string_view name,
        cir::TypeRef function_type_pattern,
        const std::vector<TemplateParameter>& friend_parameters,
        const std::vector<TemplateParameter>& member_template_parameters,
        SrcLoc loc = SrcLoc());
    cir::EntityId register_template_partial_specialization(
        const TemplateInfo& primary,
        TemplateInfo partial,
        std::vector<TemplateArgument> arguments,
        SrcLoc loc);
    cir::EntityId register_template_entity(TemplateInfo info,
                                           cir::EntityId entity,
                                           SrcLoc loc);
    bool define_member_template_entity(TemplateInfo info,
                                       cir::EntityId entity,
                                       SrcLoc loc);
    bool define_member_class_template_entity(TemplateInfo info,
                                             cir::EntityId entity,
                                             SrcLoc loc);
    SrcLoc first_implicit_template_specialization(
        cir::EntityId template_entity) const;
    const TemplateInfo* template_info(cir::EntityId entity) const;
    std::vector<TemplateInfo> complete_class_template_default_recipes(
        cir::EntityId record) const;
    bool resolve_complete_class_template_defaults(
        cir::EntityId template_entity,
        const std::vector<TemplateParameter>& parameters);
    const TemplateInfo* template_info_for_name(std::string_view name) const;
    const TemplateInfo* template_info_for_pattern_record(
        cir::EntityId record) const;
    const TemplateInfo* template_parameter_pack_info_for_name(
        std::string_view name) const;
    const TemplateInfo* template_info_in_context(cir::DeclContextId context,
                                                 std::string_view name,
                                                 bool include_parents) const;
    std::vector<const TemplateInfo*> function_template_infos_for_name(
        cir::DeclContextId context,
        std::string_view name,
        bool include_parents) const;
    const TemplateInfo* peek_qualified_template_info(
        bool global_qualifier,
        const std::vector<std::string_view>& qualifiers,
        std::string_view terminal) const;
    struct MemberEntityLookup {
        bool found_name = false;
        bool ambiguous = false;
        std::vector<cir::EntityId> entities;
    };
    MemberEntityLookup lookup_member_entities(
        cir::TypeId record_type,
        std::string_view name) const;
    std::string template_memo_key(cir::EntityId entity,
                                  const std::vector<TemplateArgument>& arguments) const;
    std::string template_memo_key(
        cir::EntityId entity,
        const TemplateArgumentBindings& argument_bindings) const;
    enum class ConstraintSatisfactionRequestKind : uint8_t {
        ConceptId,
        AssociatedConstraints,
        AtomicConstraint
    };
    enum class ConstraintSatisfactionResult : uint8_t {
        Satisfied,
        Unsatisfied,
        Dependent,
        Invalid,
        Unsupported
    };
    struct ConstraintSatisfactionScope {
        enum class State : uint8_t {
            Evaluate,
            Cached,
            Recursive
        };

        State state = State::Evaluate;
        std::optional<ConstraintSatisfactionResult> cached_result;
        std::string key;
        std::string recursion_key;
        uint64_t environment_revision = 0;
        bool stable_identity = false;

        bool should_evaluate() const {
            return state == State::Evaluate;
        }
    };
    ConstraintSatisfactionScope begin_constraint_satisfaction(
        ConstraintSatisfactionRequestKind kind,
        cir::EntityId entity,
        const TemplateArgumentBindings& argument_bindings,
        uint64_t point_lookup_generation,
        uint64_t subject_begin = 0,
        uint64_t subject_end = 0);
    void finish_constraint_satisfaction(
        ConstraintSatisfactionScope scope,
        ConstraintSatisfactionResult result);
    void abandon_constraint_satisfaction(ConstraintSatisfactionScope scope);
    uint64_t constraint_environment_revision() const;
    void note_constraint_environment_change();
    std::string template_display_name(const TemplateInfo& info,
                                      const std::vector<TemplateArgument>& arguments) const;
    bool template_parameter_lists_match(
        const std::vector<TemplateParameter>& lhs,
        const std::vector<TemplateParameter>& rhs) const;
    bool template_heads_equivalent(const TemplateInfo& lhs,
                                   const TemplateInfo& rhs) const;
    std::vector<size_t>
    inherit_prior_class_template_defaults_for_validation(
        TemplateInfo& info) const;
    bool function_template_declarations_correspond(
        const TemplateInfo& lhs,
        const TemplateInfo& rhs) const;
    bool function_template_declarations_correspond(
        const std::vector<TemplateParameter>& lhs_parameters,
        cir::TypeId lhs_pattern_type,
        const std::vector<TemplateParameter>& rhs_parameters,
        cir::TypeId rhs_pattern_type) const;
    cir::EntityId declare_hidden_friend_function_template(
        TemplateInfo info,
        cir::DeclContextId context,
        SrcLoc loc,
        const std::vector<ParamInput>* params = nullptr,
        cir::EntityId granting_record = {},
        cir::EntityId signature_owner = {});
    bool is_hidden_friend_function_template(cir::EntityId entity) const;
    cir::EntityId cached_instantiation(const std::string& key) const;
    void remember_instantiation(const std::string& key, cir::EntityId entity);
    void replace_instantiation(const std::string& key, cir::EntityId entity);
    bool declare_explicit_instantiation_declaration(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        AttributeList attrs = {});
    bool explicit_instantiation_declaration_declared(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc* declaration_loc = nullptr) const;
    void declare_explicit_instantiation_definition(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        AttributeList attrs = {});
    bool explicit_instantiation_definition_declared(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc* definition_loc = nullptr) const;
    void mark_explicit_template_specialization(cir::EntityId entity);
    bool is_explicit_template_specialization(cir::EntityId entity) const;
    bool explicit_template_specialization_declared(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        cir::EntityId* specialization = nullptr) const;
    void apply_explicit_instantiation_declaration_suppression(
        cir::EntityId entity,
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments);
    void apply_explicit_instantiation_definition_emission(
        cir::EntityId entity,
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments);
    void apply_class_explicit_instantiation_declaration_suppression(
        cir::EntityId record_entity,
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments);
    void apply_record_explicit_instantiation_declaration_suppression(
        cir::EntityId record_entity);
    void apply_record_explicit_instantiation_definition_emission(
        cir::EntityId record_entity);
    bool declare_explicit_entity_instantiation_declaration(
        cir::EntityId entity,
        SrcLoc loc,
        AttributeList attrs = {});
    bool explicit_entity_instantiation_declaration_declared(
        cir::EntityId entity,
        SrcLoc* declaration_loc = nullptr) const;
    void declare_explicit_entity_instantiation_definition(
        cir::EntityId entity,
        SrcLoc loc,
        AttributeList attrs = {});
    bool explicit_entity_instantiation_definition_declared(
        cir::EntityId entity,
        SrcLoc* definition_loc = nullptr) const;
    void apply_explicit_entity_instantiation_definition_emission(
        cir::EntityId entity);
    void remember_template_specialization(
        cir::EntityId entity,
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc point_of_instantiation = SrcLoc(),
        uint64_t point_lookup_generation = 0,
        const TemplateInfo* selected_info = nullptr,
        const std::vector<TemplateArgument>* selected_arguments = nullptr,
        const TemplateArgumentBindings* exact_bindings = nullptr,
        const TemplateArgumentBindings* selected_exact_bindings = nullptr);
    void add_template_out_of_line_member(cir::EntityId entity,
                                         size_t begin,
                                         size_t end,
                                         bool is_template_declaration = false,
                                         bool is_static_data_member_definition = false,
                                         std::vector<TemplateParameter> head_parameters = {},
                                         std::vector<uint32_t> head_parameter_owner_slots = {});
    struct OutOfLineHeadRebinding {
        struct Entry {
            std::string name;
            std::optional<cir::Binding> previous;
        };
        std::vector<Entry> entries;
        SrcLoc loc{};
    };
    OutOfLineHeadRebinding bind_out_of_line_member_head(
        const TemplateInfo& head,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc);
    OutOfLineHeadRebinding rebind_active_template_header_in_current_scope(
        SrcLoc loc);
    void restore_out_of_line_member_head(
        const OutOfLineHeadRebinding& rebinding);
    SrcLoc register_explicit_member_function_specialization_declaration(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        std::string_view member_name,
        cir::TypeRef member_type,
        SrcLoc loc);
    bool explicit_member_function_specialization_declared(
        cir::EntityId method,
        SrcLoc* declaration_loc = nullptr) const;
    SrcLoc register_explicit_static_data_member_specialization_declaration(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        std::string_view member_name,
        cir::TypeRef member_type,
        SrcLoc loc);
    bool explicit_static_data_member_specialization_declared(
        cir::EntityId member,
        SrcLoc* declaration_loc = nullptr) const;
    cir::EntityId find_record_static_data_member(cir::DeclContextId context,
                                                 std::string_view name,
                                                 cir::TypeRef type,
                                                 std::optional<cir::StorageDuration>
                                                     specialization_duration =
                                                         std::nullopt);
    void rename_entity(cir::EntityId entity, std::string_view name);
    bool enter_template_replay_guard(SrcLoc loc);
    void leave_template_replay_guard();
    struct BlockContextState;
    struct CoroutineState;
    struct InstantiationScope {
        InstantiationScope();
        InstantiationScope(InstantiationScope&&) noexcept;
        InstantiationScope& operator=(InstantiationScope&&) noexcept;
        ~InstantiationScope();
        bool active = false;
        std::unique_ptr<BlockContextState> saved_context;
        std::unordered_map<uint64_t, uint32_t> saved_header_value_params;
        std::unordered_set<uint64_t> saved_header_value_param_packs;
        const TemplateInfo* saved_active_template_header_info = nullptr;
        bool saved_collecting_pattern = false;
        uint64_t saved_lookup_ceiling = 0;
        bool suspended_parameter_pack_element_replay = false;
        size_t parameter_pack_element_replay_suspension_depth = 0;
        bool suspended_parameter_pack_pattern_capture = false;
        size_t parameter_pack_pattern_capture_suspension_depth = 0;
    };
    InstantiationScope begin_template_instantiation(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0,
        cir::EntityId record_to_complete = {},
        const TemplateArgumentBindings* exact_bindings = nullptr);
    void finish_template_instantiation(InstantiationScope scope);
    struct TemplateArgumentListParsingScope {
        bool active = false;
        uint64_t point_lookup_generation = 0;
    };
    TemplateArgumentListParsingScope begin_template_argument_list_parsing(
        const TemplateInfo& info,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    void finish_template_argument_list_parsing(
        TemplateArgumentListParsingScope scope);
    struct DefaultArgumentInstantiationScope {
        std::unordered_map<uint64_t, uint32_t> saved_header_value_params;
        std::unordered_set<uint64_t> saved_header_value_param_packs;
        const TemplateInfo* saved_active_template_header_info = nullptr;
        bool saved_collecting_pattern = false;
        uint64_t saved_lookup_ceiling = 0;
        bool suspended_parameter_pack_pattern_capture = false;
        size_t parameter_pack_pattern_capture_suspension_depth = 0;
        bool active = false;
    };
    DefaultArgumentInstantiationScope begin_default_argument_instantiation(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation = 0);
    void finish_default_argument_instantiation(
        DefaultArgumentInstantiationScope scope);
    InstantiationScope begin_template_parameter_scope();
    InstantiationScope
    begin_current_template_instantiation_parameter_scope(
        cir::EntityId function,
        SrcLoc loc);
    void declare_template_parameter_binding(TemplateInfo& info,
                                            TemplateParameter& parameter,
                                            SrcLoc loc);
    void finish_template_parameter_scope(InstantiationScope scope);
    InstantiationScope begin_template_header(TemplateInfo& info, SrcLoc loc);
    void finish_template_header(InstantiationScope scope);
    struct PatternBindings;
    enum class TypePatternExceptionMatch : uint8_t {
        Exact,
        IgnoreAtCurrentFunction,
        ArgumentToPatternFunctionPointerConversion,
        PatternToArgumentFunctionPointerConversion,
    };
    enum class TypePatternReturnMatch : uint8_t {
        Exact,
        PlaceholderIsNonDeducedAtCurrentFunction,
    };
    enum class TypePatternParameterMatch : uint8_t {
        Exact,
        AdjustForwardingReferencesAtCurrentFunction,
    };
    bool deduce_template_arguments(const TemplateInfo& info,
                                   const std::vector<ExprResult>& arguments,
                                   std::vector<TemplateArgument>& deduced,
                                   const std::vector<TemplateArgument>*
                                       explicit_arguments = nullptr,
                                   PatternInstantiationCallbacks* callbacks = nullptr,
                                   TemplateArgumentBindings* deduced_bindings =
                                       nullptr,
                                   SrcLoc loc = SrcLoc(),
                                   const std::vector<uint8_t>*
                                       parameter_default_argument_flags =
                                           nullptr);
    void populate_enclosing_type_pack_bindings(
        const TemplateInfo& info,
        PatternBindings& bindings) const;
    bool deduce_conversion_template_arguments(
        const TemplateInfo& info,
        cir::TypeId target_type,
        std::vector<TemplateArgument>& deduced,
        TemplateArgumentBindings* deduced_bindings = nullptr);
    bool deduce_function_template_address_arguments(
        const TemplateInfo& info,
        cir::TypeId target_function_type,
        std::vector<TemplateArgument>& deduced,
        const std::vector<TemplateArgument>* explicit_arguments = nullptr,
        PatternInstantiationCallbacks* callbacks = nullptr,
        SrcLoc loc = SrcLoc(),
        TypePatternExceptionMatch exception_match =
            TypePatternExceptionMatch::Exact,
        TypePatternReturnMatch return_match = TypePatternReturnMatch::Exact,
        TemplateArgumentBindings* deduced_bindings = nullptr);
    bool template_parameter_is_deducible_from_function_parameter_types(
        const TemplateParameter& parameter,
        cir::TypeId function_type) const;
    bool template_parameter_is_deducible_from_type(
        const TemplateParameter& parameter,
        cir::TypeId type) const;
    enum class TemplateArgumentBindingFailureKind : uint8_t {
        None,
        TooManyArguments,
        MissingRequiredArgument,
        ArgumentKindMismatch,
        PackBinding,
        TemplateTemplateMismatch,
        SubstitutionFailure,
        InstantiationDepth,
        InvalidDefaultArgument,
        Internal,
    };
    enum class TemplateArgumentBindingFailureReason : uint8_t {
        None,
        InternalBindingCountMismatch,
        MultipleParameterPacksUnsupported,
        PackExpansionForNonPackUnsupported,
        PartialNonTrailingPackBinding,
        TypeParameterRequiresTypeArgument,
        NonTypeParameterRequiresValueArgument,
        NonTypeArgumentNarrowing,
        TemplateParameterRequiresTemplateArgument,
        TemplateArgumentMustNameTemplate,
        TemplateArgumentMustNameConceptTemplate,
        TemplateArgumentMustNameClassOrAliasTemplate,
        TemplateTemplateParameterListMismatch,
        DependentDefaultArgumentSubstitution,
    };
    struct TemplateArgumentBindingFailure {
        static constexpr uint32_t no_index =
            std::numeric_limits<uint32_t>::max();

        TemplateArgumentBindingFailureKind kind =
            TemplateArgumentBindingFailureKind::None;
        TemplateArgumentBindingFailureReason reason =
            TemplateArgumentBindingFailureReason::None;
        TemplateParameterKind expected_parameter_kind =
            TemplateParameterKind::Type;
        cir::TemplateArgumentKind actual_argument_kind =
            cir::TemplateArgumentKind::Type;
        uint32_t parameter_index = no_index;
        uint32_t argument_index = no_index;
        uint32_t supplied_argument_count = 0;
        uint32_t minimum_argument_count = 0;
        uint32_t maximum_argument_count = no_index;
        std::shared_ptr<const std::string> detail;

        bool failed() const {
            return kind != TemplateArgumentBindingFailureKind::None;
        }
    };
    static_assert(sizeof(TemplateArgumentBindingFailure) <= 48);
    bool bind_template_arguments_to_parameters(
        const std::vector<TemplateParameter>& parameters,
        const std::vector<TemplateArgument>& arguments,
        TemplateArgumentBindings& bindings_out,
        TemplateArgumentBindingFailure* failure_out = nullptr,
        TemplateArgumentBindingMode mode =
            TemplateArgumentBindingMode::Canonical) const;
    void canonicalize_template_argument_bindings(
        TemplateArgumentBindings& bindings) const;
    std::optional<bool> evaluate_dependent_boolean_expression(
        cir::TemplateValueExpression expression,
        const TemplateArgumentBindings& bindings,
        std::string* error_out = nullptr);
    bool bind_explicit_template_arguments_prefix_to_parameters(
        const std::vector<TemplateParameter>& parameters,
        const std::vector<TemplateArgument>& explicit_arguments,
        TemplateArgumentBindings& bindings_out,
        TemplateArgumentBindingFailure* failure_out = nullptr,
        TemplateArgumentBindingMode mode =
            TemplateArgumentBindingMode::Canonical) const;
    bool complete_template_argument_bindings_with_defaults(
        const TemplateInfo& info,
        TemplateArgumentBindings& bindings_out,
        TemplateArgumentBindingFailure* failure_out = nullptr,
        PatternInstantiationCallbacks* callbacks = nullptr,
        SrcLoc loc = SrcLoc(),
        TemplateArgumentCompletionMode mode =
            TemplateArgumentCompletionMode::Required);
    std::vector<TemplateArgument> flatten_template_argument_bindings(
        const TemplateArgumentBindings& bindings) const;
    using PartialSpecializationConstraintPredicate =
        std::function<bool(const TemplateInfo&,
                           const TemplateArgumentBindings&)>;
    using PartialSpecializationCandidatePredicate =
        std::function<bool(const TemplateInfo&,
                           const TemplateArgumentBindings&)>;
    PartialSpecializationSelection
    select_template_partial_specialization(
        const TemplateInfo& primary,
        const std::vector<TemplateArgument>& arguments,
        const PartialSpecializationConstraintPredicate&
            constraint_satisfied = {},
        const PartialSpecializationCandidatePredicate&
            candidate_viable = {});
    PartialSpecializationSelection
    select_template_partial_specialization_uncached(
        const TemplateInfo& primary,
        const std::vector<TemplateArgument>& arguments,
        const PartialSpecializationConstraintPredicate&
            constraint_satisfied = {},
        const PartialSpecializationCandidatePredicate&
            candidate_viable = {});
    struct PatternBindings {
        struct ValueBinding {
            bool bound = false;
            TemplateArgument argument;
            cir::TypeRef deduction_source_type;
            bool source_type_requires_exact_match = false;
            bool deduced_from_array_bound = false;
        };
        struct TemplateBinding {
            bool bound = false;
            TemplateArgument argument;
        };
        struct PendingExceptionMatch {
            cir::FunctionExceptionSpec pattern;
            cir::FunctionExceptionSpec argument;
            TypePatternExceptionMatch policy =
                TypePatternExceptionMatch::Exact;
        };
        std::vector<cir::TypeRef> types;
        std::vector<ValueBinding> values;
        std::vector<TemplateBinding> templates;
        std::vector<std::optional<std::vector<TemplateArgument>>>
            pack_arguments;
        const std::vector<TemplateParameter>* template_parameters = nullptr;
        struct FixedTypePack {
            cir::TypeId pattern_type{};
            std::vector<TemplateArgument> arguments;
        };
        std::vector<FixedTypePack> fixed_type_packs;
        std::optional<size_t> expansion_element_index;
        std::optional<size_t> expansion_element_count;
        std::vector<bool> explicit_types;
        std::vector<bool> explicit_values;
        std::vector<bool> explicit_templates;
        std::vector<PendingExceptionMatch> pending_exception_matches;
        bool partial_ordering = false;
        bool deduce_through_alias_associated_type = false;
        const std::vector<TemplateArgument>*
            partial_ordering_argument_identities = nullptr;
        const std::vector<TemplateParameter>*
            partial_ordering_argument_parameters = nullptr;
        bool partial_ordering_ignored_argument_pack = false;
        std::vector<bool> partial_ordering_used_parameters;
    };
    enum class TemplateArgumentListDeductionMode : uint8_t {
        Ordinary,
        PartialOrdering,
    };
    enum class TemplateArgumentListDeductionResult : uint8_t {
        Match,
        Mismatch,
        NonDeduced,
    };
    bool unify_type_pattern(cir::TypeId pattern,
                            cir::TypeId argument,
                            PatternBindings& bindings,
                            TypePatternExceptionMatch exception_match =
                                TypePatternExceptionMatch::Exact,
                            bool allow_qualification_conversion = false,
                            TypePatternReturnMatch return_match =
                                TypePatternReturnMatch::Exact,
                            TypePatternParameterMatch parameter_match =
                                TypePatternParameterMatch::Exact) const;
    bool unify_type_ref_pattern(cir::TypeRef pattern,
                                cir::TypeRef argument,
                                PatternBindings& bindings,
                                TypePatternExceptionMatch exception_match =
                                    TypePatternExceptionMatch::Exact,
                                bool allow_qualification_conversion = false,
                                TypePatternReturnMatch return_match =
                                    TypePatternReturnMatch::Exact,
                                TypePatternParameterMatch parameter_match =
                                    TypePatternParameterMatch::Exact) const;
    bool reconcile_deduced_value_parameter_types(
        const TemplateInfo& info,
        PatternBindings& bindings);
    bool finalize_pending_exception_matches(
        PatternBindings& bindings,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks* callbacks = nullptr);
    bool function_pointer_conversion_matches(cir::TypeRef source,
                                             cir::TypeRef target) const;
    bool function_type_conversion_matches(cir::TypeRef source,
                                           cir::TypeRef target) const;
    bool deduce_call_argument(cir::TypeId parameter_type,
                              const ExprResult& argument,
                              PatternBindings& bindings,
                              SrcLoc loc = SrcLoc());
    bool deduce_call_derived_class_alternative(
        cir::TypeId parameter_type,
        cir::TypeId argument_type,
        PatternBindings& bindings);
    bool deduce_initializer_list_argument(cir::TypeId parameter_type,
                                          const ExprResult& argument,
                                          PatternBindings& bindings,
                                          SrcLoc loc = SrcLoc());
    bool deduce_overload_set_argument(cir::TypeId parameter_type,
                                      const ExprResult& argument,
                                      PatternBindings& bindings,
                                      SrcLoc loc = SrcLoc());
    std::vector<cir::EntityId> instantiate_addressable_function_templates(
        const std::vector<cir::EntityId>& candidates,
        cir::TypeId target_function_type,
        SrcLoc loc = SrcLoc(),
        const std::vector<TemplateArgument>* explicit_arguments = nullptr,
        const std::vector<CandidateExplicitTemplateArguments>*
            candidate_explicit_arguments = nullptr);
    cir::EntityId select_addressable_function_target(
        const std::vector<cir::EntityId>& candidates,
        cir::TypeId target_function_type,
        SrcLoc loc = SrcLoc(),
        const std::vector<TemplateArgument>* explicit_arguments = nullptr,
        const std::vector<CandidateExplicitTemplateArguments>*
            candidate_explicit_arguments = nullptr,
        OverloadAmbiguityInfo* ambiguity_info = nullptr,
        bool mark_odr_use = true);
    bool callable_is_deleted(cir::EntityId entity) const;
    std::vector<cir::EntityId> select_member_pointer_targets(
        const std::vector<cir::EntityId>& candidates,
        cir::TypeId target_type,
        SrcLoc loc = SrcLoc(),
        const std::vector<TemplateArgument>* explicit_arguments = nullptr,
        const std::vector<CandidateExplicitTemplateArguments>*
            candidate_explicit_arguments = nullptr,
        OverloadAmbiguityInfo* ambiguity_info = nullptr);
    bool entity_is_function_template_specialization(cir::EntityId entity) const;
    void apply_function_template_address_eliminations(
        std::vector<cir::EntityId>& selected);
    bool pattern_bindings_equivalent(const PatternBindings& lhs,
                                     const PatternBindings& rhs) const;
    enum class FunctionTemplateSpecializationOrder : uint8_t {
        Unordered,
        LhsMoreSpecialized,
        RhsMoreSpecialized,
    };
    enum class FunctionTemplateOrderingContextKind : uint8_t {
        Call,
        ConversionCall,
        Address,
        Declaration,
        PlacementDeallocation,
        RewrittenCall,
    };
    struct FunctionTemplateOrderingContext {
        FunctionTemplateOrderingContextKind kind =
            FunctionTemplateOrderingContextKind::Declaration;
        size_t lhs_call_argument_count = 0;
        size_t rhs_call_argument_count = 0;
        bool lhs_reversed = false;
        bool rhs_reversed = false;

        static FunctionTemplateOrderingContext call(size_t lhs_arguments,
                                                    size_t rhs_arguments,
                                                    bool lhs_is_reversed = false,
                                                    bool rhs_is_reversed = false) {
            FunctionTemplateOrderingContext context;
            context.kind = (lhs_is_reversed || rhs_is_reversed)
                ? FunctionTemplateOrderingContextKind::RewrittenCall
                : FunctionTemplateOrderingContextKind::Call;
            context.lhs_call_argument_count = lhs_arguments;
            context.rhs_call_argument_count = rhs_arguments;
            context.lhs_reversed = lhs_is_reversed;
            context.rhs_reversed = rhs_is_reversed;
            return context;
        }

        static FunctionTemplateOrderingContext conversion_call() {
            FunctionTemplateOrderingContext context;
            context.kind = FunctionTemplateOrderingContextKind::ConversionCall;
            return context;
        }

        static FunctionTemplateOrderingContext address() {
            FunctionTemplateOrderingContext context;
            context.kind = FunctionTemplateOrderingContextKind::Address;
            return context;
        }

        static FunctionTemplateOrderingContext declaration() {
            return {};
        }

        static FunctionTemplateOrderingContext placement_deallocation() {
            FunctionTemplateOrderingContext context;
            context.kind =
                FunctionTemplateOrderingContextKind::PlacementDeallocation;
            return context;
        }
    };
    struct FunctionTemplateOrderingCandidate {
        cir::EntityId template_entity{};
        cir::TypeId original_function_type{};
        std::vector<TemplateArgument> synthesized_arguments;
        const std::vector<TemplateParameter>* template_parameters = nullptr;
        bool is_non_static_member = false;
        cir::TypeRef member_class_type;
    };
    struct FunctionTemplatePartialOrdering {
        bool lhs_at_least_as_specialized = false;
        bool rhs_at_least_as_specialized = false;
    };
    std::vector<TemplateArgument> function_template_ordering_identities(
        const TemplateInfo& info,
        cir::TypeId identity_source = {});
    FunctionTemplateOrderingCandidate function_template_ordering_candidate(
        cir::EntityId template_entity,
        cir::TypeId original_function_type);
    FunctionTemplateOrderingCandidate function_template_ordering_candidate(
        const TemplateInfo& info,
        cir::TypeId original_function_type);
    FunctionTemplateOrderingCandidate
    partial_specialization_ordering_candidate(
        const TemplateInfo& primary,
        const TemplateInfo& specialization,
        const std::vector<TemplateArgument>& arguments);
    FunctionTemplatePartialOrdering function_template_partial_ordering(
        const FunctionTemplateOrderingCandidate& lhs,
        const FunctionTemplateOrderingCandidate& rhs,
        const FunctionTemplateOrderingContext& context);
    bool function_template_more_specialized(cir::TypeId lhs_pattern,
                                            cir::TypeId rhs_pattern,
                                            const FunctionTemplateOrderingContext&
                                                context);
    bool function_template_more_specialized(
        cir::TypeId lhs_pattern,
        const TemplateInfo& lhs,
        cir::TypeId rhs_pattern,
        const TemplateInfo& rhs,
        const FunctionTemplateOrderingContext& context);
    bool function_template_more_specialized(const TemplateInfo& lhs,
                                            const TemplateInfo& rhs,
                                            const FunctionTemplateOrderingContext&
                                                context);
    bool function_template_unordered_constraints_tie(
        cir::TypeId lhs_pattern,
        const TemplateInfo& lhs,
        cir::TypeId rhs_pattern,
        const TemplateInfo& rhs,
        const FunctionTemplateOrderingContext& context);
    bool function_template_unordered_constraints_tie(
        const TemplateInfo& lhs,
        const TemplateInfo& rhs,
        const FunctionTemplateOrderingContext& context);
    bool function_template_specializations_unordered_constraints_tie(
        cir::EntityId lhs,
        cir::EntityId rhs,
        const FunctionTemplateOrderingContext& context);
    FunctionTemplateSpecializationOrder compare_function_template_specializations(
        cir::EntityId lhs,
        cir::EntityId rhs,
        const FunctionTemplateOrderingContext& context);
    bool type_contains_type_param(cir::TypeId type) const;
    bool type_contains_type_param_except_record(
        cir::TypeId type,
        cir::EntityId opaque_record) const;
    bool type_contains_dependent_alias_specialization(
        cir::TypeId type) const;
    bool type_contains_nondeduced_context(cir::TypeId type) const;
    bool type_contains_type_parameter_pack(cir::TypeId type) const;
    bool function_parameter_pack_name(std::string_view name) const;
    std::optional<std::vector<ExprResult>>
    function_parameter_pack_arguments(std::string_view name,
                                      SrcLoc loc);
    enum class ParameterPackKind : uint8_t {
        Function,
        Type,
        Value,
        Template,
    };
    struct ParameterPackIdentity {
        ParameterPackKind kind = ParameterPackKind::Type;
        std::string name;
        cir::EntityId declaration{};
        cir::EntityId owner{};
        uint32_t depth = 0;
        uint32_t index = cir::ArrayTypePayload::no_extent_param;
        cir::TypeId parameter_type{};
        bool is_unbound_template_parameter = false;
    };
    struct ParameterPackPatternCaptureScope {
        bool active = false;
        size_t depth = 0;
    };
    bool in_pack_pattern_capture() const;
    ParameterPackPatternCaptureScope begin_parameter_pack_pattern_capture();
    std::vector<ParameterPackIdentity> finish_parameter_pack_pattern_capture(
        ParameterPackPatternCaptureScope scope);
    struct ParameterPackPatternCaptureCheckpoint {
        bool active = false;
        size_t depth = 0;
        size_t size = 0;
    };
    ParameterPackPatternCaptureCheckpoint
        checkpoint_parameter_pack_pattern_capture() const;
    void restore_parameter_pack_pattern_capture(
        ParameterPackPatternCaptureCheckpoint checkpoint);
    struct TypeParameterPackPattern {
        std::string name;
        cir::EntityId template_entity{};
        uint32_t depth = 0;
        uint32_t index = cir::ArrayTypePayload::no_extent_param;
        cir::TypeId type{};
    };
    bool capture_type_parameter_pack_name(std::string_view name);
    using FunctionParameterPackElement = collect::FunctionParameterPackElement;
    struct FunctionParameterPackScopeState {
        std::unordered_set<std::string> names;
        std::unordered_map<std::string,
                           std::vector<FunctionParameterPackElement>>
            elements;
        std::unordered_map<std::string, uint32_t> template_pack_indices;
    };
    using ParameterPackElement =
        std::variant<FunctionParameterPackElement, cir::TypeRef, TemplateArgument>;
    struct ParameterPackElementBinding {
        ParameterPackIdentity pack;
        ParameterPackElement element;
    };
    struct ParameterPackElementReplayScope {
        bool active = false;
        size_t depth = 0;
    };
    ParameterPackElementReplayScope begin_parameter_pack_element_replay(
        const std::vector<ParameterPackIdentity>& packs,
        size_t index);
    ParameterPackElementReplayScope begin_parameter_pack_element_replay(
        const std::vector<ParameterPackElementBinding>& bindings);
    void finish_parameter_pack_element_replay(
        ParameterPackElementReplayScope scope);
    std::optional<size_t> parameter_pack_element_count(
        const ParameterPackIdentity& pack) const;
    std::optional<ParameterPackIdentity> parameter_pack_identity(
        ParameterPackKind kind,
        std::string_view name) const;
    bool capture_parameter_pack(ParameterPackKind kind,
                                std::string_view name);
    bool capture_any_parameter_pack_name(std::string_view name);
    const ParameterPackElement* parameter_pack_replay_element(
        ParameterPackKind kind,
        std::string_view name) const;
    bool template_argument_names_parameter_pack(
        const TemplateArgument& argument) const;
    std::optional<std::vector<TemplateArgument>>
    template_argument_pack_arguments(const TemplateArgument& argument) const;
    std::optional<std::vector<TemplateArgument>>
    template_argument_pack_arguments(const ParameterPackIdentity& pack) const;
    std::optional<uint32_t> type_parameter_pack_index(cir::TypeId type) const;
    std::optional<cir::TypeId>
    type_parameter_pack_type(std::string_view name) const;
    std::optional<std::vector<TemplateArgument>>
    template_type_pack_arguments(cir::TypeId type) const;
    std::optional<std::vector<TemplateArgument>>
    template_type_pack_arguments(const TypeParameterPackPattern& pack) const;
    cir::TypeRef collect_pack_index_type(cir::TypeRef pack_type,
                                         ExprResult index,
                                         SrcLoc loc = SrcLoc());
    cir::TypeRef collect_builtin_pack_element_type(
        std::vector<TemplateArgument> arguments,
        SrcLoc loc = SrcLoc(),
        bool diagnose = true);
    ExprResult collect_pack_index_expr(std::string_view name,
                                       ExprResult index,
                                       SrcLoc loc = SrcLoc());
    const TemplateParameter*
    template_value_parameter_for_entity(cir::EntityId entity) const;
    uint32_t template_value_param_index(cir::EntityId entity) const;
    bool template_value_param_is_pack(cir::EntityId entity) const;
    const TemplateArgument*
    dependent_instantiation_value_argument(cir::EntityId entity) const;
    std::optional<uint32_t>
    template_value_pack_param_index_for_name(std::string_view name) const;
    std::optional<uint32_t>
    template_template_pack_param_index_for_name(std::string_view name) const;
    void register_template_value_parameter_equivalence(
        cir::EntityId variable,
        cir::TypeId variable_type,
        const ExprResult& initializer);
    bool is_dependent_type(cir::TypeId type) const;
    const TemplateInfo*
    class_template_placeholder_info(cir::TypeId type) const;
    bool constant_template_parameter_type_is_supported(cir::TypeId type) const;
    bool form_class_template_value_argument(
        cir::TypeId declared_type,
        ExprResult source,
        TemplateArgument& argument,
        SrcLoc loc,
        std::string_view constant_expression_diagnostic,
        std::string* error_out = nullptr,
        bool diagnose_deduction = true);
    cir::TypeRef collect_builtin_type_transform(BuiltinKind kind,
                                                cir::TypeRef operand,
                                                SrcLoc loc = SrcLoc());
    bool expr_is_dependent(const ExprResult& expr) const;
    bool expr_is_value_dependent(const ExprResult& expr) const;
    ExprResult make_dependent_expr(ExprResult operand, SrcLoc loc);
    ExprResult make_deferred_typed_expr(ExprResult operand,
                                        cir::TypeId expression_type,
                                        ValueCategory category,
                                        SrcLoc loc);
    cir::TemplateValueExpression template_value_operand_expression(
        const ExprResult& operand);
    ExprResult make_deferred_conversion_expr(ExprResult operand,
                                             cir::TypeId target_type,
                                             SrcLoc loc);
    void set_in_template_definition(bool value) {
        in_template_definition_ = value;
    }
    void note_substitution_hard_error() { substitution_hard_error_ = true; }
    bool take_substitution_hard_error() {
        bool value = substitution_hard_error_;
        substitution_hard_error_ = false;
        return value;
    }
    bool in_template_definition() const { return in_template_definition_; }
    bool in_template_header() const {
        return active_template_header_info_ != nullptr;
    }
    class ActiveTemplateHeaderScope {
    public:
        ActiveTemplateHeaderScope(Session& session, const TemplateInfo& info)
            : session_(&session),
              saved_(session.active_template_header_info_) {
            session.active_template_header_info_ = &info;
        }
        ~ActiveTemplateHeaderScope() {
            session_->active_template_header_info_ = saved_;
        }
        ActiveTemplateHeaderScope(const ActiveTemplateHeaderScope&) = delete;
        ActiveTemplateHeaderScope& operator=(
            const ActiveTemplateHeaderScope&) = delete;

    private:
        Session* session_;
        const TemplateInfo* saved_;
    };
    bool in_template_instantiation() const {
        return !active_instantiations_.empty();
    }
    bool template_instantiation_reclassifies_data_member_as_function(
        std::string_view name,
        SrcLoc loc) const;
    const TemplateInfo::StaticDataMemberInitializer*
    current_instantiation_static_data_member_initializer(
        std::string_view name,
        SrcLoc loc) const;
    // The [temp.dep.candidate] ODR invariant hides unqualified declarations
    // added after template definition while allowing ADL at instantiation.
    void set_lookup_generation_ceiling(uint64_t ceiling) {
        lookup_generation_ceiling_ = ceiling;
    }
    uint64_t lookup_generation_ceiling() const {
        return lookup_generation_ceiling_;
    }
    class LookupGenerationCeilingScope {
    public:
        LookupGenerationCeilingScope(Session& session, uint64_t ceiling)
            : session_(session),
              saved_(session.lookup_generation_ceiling()) {
            session_.set_lookup_generation_ceiling(ceiling);
        }
        ~LookupGenerationCeilingScope() {
            session_.set_lookup_generation_ceiling(saved_);
        }
        LookupGenerationCeilingScope(const LookupGenerationCeilingScope&) =
            delete;
        LookupGenerationCeilingScope& operator=(
            const LookupGenerationCeilingScope&) = delete;

    private:
        Session& session_;
        uint64_t saved_ = 0;
    };
    cir::EntityId create_incomplete_record_specialization(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc);
    cir::EntityId create_dependent_record_specialization(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc);
    cir::EntityId create_dependent_variable_specialization(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc);
    cir::EntityId create_function_template_declaration_specialization(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        PatternInstantiationCallbacks& callbacks,
        SrcLoc loc,
        cir::TypeId declared_type = {},
        const TemplateArgumentBindings* exact_bindings = nullptr);
    void inherit_function_template_default_arguments(
        cir::EntityId specialization,
        const TemplateInfo& info);
    cir::EntityId create_alias_template_specialization(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        cir::TypeRef associated_type,
        SrcLoc loc);
    bool is_instantiating() const { return !active_instantiations_.empty(); }
    size_t template_instantiation_depth_limit() const {
        return template_instantiation_depth_limit_;
    }
    void begin_template_validation(const TemplateInfo& info);
    cir::EntityId template_validation_entity(const TemplateInfo& info) const;
    void finish_template_validation();
    void note_current_instantiation_dependent_bases(
        cir::EntityId record,
        bool has_dependent_bases);
    bool current_instantiation_context_has_dependent_bases(
        cir::DeclContextId context) const;
    bool current_instantiation_type_has_dependent_bases(
        cir::TypeId type) const;
    const TemplateInfo* validating_template_info() const {
        return validating_template_info_;
    }
    const TemplateInfo* current_abbreviated_function_template() const;
    cir::TypeRef abbreviated_function_parameter_replacement(
        const TemplateInfo& info,
        uint32_t template_parameter_index) const;
    cir::EntityId current_instantiation_record(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments) const;
    bool template_arguments_for_record(
        cir::EntityId record,
        cir::EntityId* template_entity_out,
        std::vector<TemplateArgument>* arguments_out) const {
        return class_template_arguments_for_record(record,
                                                   template_entity_out,
                                                   arguments_out);
    }
    bool current_instantiation_replay_will_claim_record(
        std::string_view name) const;
    bool begin_member_instantiation_scope(cir::EntityId method,
                                          InstantiationScope& scope);
    void begin_pattern_collection();
    struct PatternCollection {
        std::vector<PatternHole> holes;
        std::vector<PatternScopeEvent> events;
        std::vector<MemberPattern> members;
        bool usable = true;
    };
    PatternCollection finish_pattern_collection();
    void begin_member_pattern(cir::EntityId method,
                              cir::FunctionId function,
                              size_t body_token_begin,
                              size_t leading_blocks);
    void finish_member_pattern(size_t body_blocks);
    cir::EntityId current_validation_record() const;
    bool collecting_pattern() const { return collecting_pattern_; }
    uint64_t pattern_taint() const { return pattern_taint_; }
    void bump_pattern_taint() {
        if (collecting_pattern_) {
            ++pattern_taint_;
        }
    }
    void mark_pattern_unusable() {
        if (member_pattern_active_) {
            current_member_pattern_.usable = false;
        } else {
            pattern_usable_ = false;
        }
    }
    size_t pattern_event_count() const { return pattern_events_.size(); }
    StmtResult make_pattern_hole_stmt(size_t token_begin,
                                      size_t token_end,
                                      uint64_t taint_before,
                                      size_t events_before,
                                      std::string display,
                                      SrcLoc loc,
                                      PatternHole::Kind kind =
                                          PatternHole::Kind::Statement);
    enum class ConceptValueEvaluationStatus : uint8_t {
        Satisfied,
        Unsatisfied,
        StillDependent,
        Invalid,
    };

    struct PatternInstantiationCallbacks {
        uint64_t point_lookup_generation = 0;
        cir::EntityId access_record{};
        cir::EntityId access_function{};
        SrcLoc access_loc{};
        bool has_explicit_access_context = false;
        TemplateArgumentCompletionMode argument_completion_mode =
            TemplateArgumentCompletionMode::Required;
        TemplateReplayOutcome* replay_outcome = nullptr;
        std::function<StmtResult(const PatternHole&)> replay_statement;
        std::function<cir::TypeRef(
            cir::EntityId,
            std::vector<TemplateArgument>,
            uint64_t,
            bool,
            TemplateArgumentCompletionMode)>
            instantiate_type_template;
        bool materialize_type_template_definition = true;
        std::function<cir::EntityId(cir::EntityId,
                                    std::vector<TemplateArgument>)>
            instantiate_value_entity;
        std::function<std::optional<TemplateArgument>(
            cir::EntityId,
            std::vector<TemplateArgument>)>
            instantiate_value;
        std::function<ConceptValueEvaluationStatus(
            cir::EntityId,
            std::vector<TemplateArgument>,
            uint64_t)>
            evaluate_concept_id;
        cir::TypeId self_pattern_type{};
        cir::TypeId self_instance_type{};
        std::unordered_map<uint32_t, TemplateArgumentBinding>
            exact_type_parameter_bindings;
        std::unordered_map<uint32_t, TemplateArgumentBinding>
            exact_value_parameter_bindings;
        std::unordered_map<uint32_t, TemplateArgumentBinding>
            exact_template_parameter_bindings;
        bool exact_type_parameter_bindings_are_authoritative = false;
        bool deferred_on_enclosing_type_pack = false;
        bool allow_parameter_pack_element_substitution = false;
        bool defer_function_exception_spec = false;
        bool preserve_opaque_dependent_call_types = false;
        cir::EntityId dependent_primary_record{};
        std::function<StmtResult()> collect_subobject_init;
    };
    enum class PatternCloneBailReason : uint8_t {
        None,
        ArgumentBinding,
        TypeSubstitution,
        EhRegion,
        UnsupportedInst,
        UnsupportedTerminator,
        UnsupportedPayload,
        HoleReplay,
        UnresolvedDependency,
        CleanupScopes,
        ScopeEvents,
        IdRemap,
        PatternShape,
        ImmediateInvocation,
        ForeignModuleUnit,
        NestedClone,
    };
    PatternCloneBailReason last_pattern_clone_bail() const {
        return pattern_clone_bail_;
    }
    static const char* pattern_clone_bail_text(PatternCloneBailReason reason);
    cir::EntityId clone_pattern_function(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        PatternInstantiationCallbacks& callbacks,
        SrcLoc loc,
        cir::EntityId declaration_shell = {},
        const TemplateArgumentBindings* exact_bindings = nullptr);
    cir::EntityId set_function_template_materialization_target(
        cir::EntityId target);
    bool clone_member_pattern(const TemplateInfo& info,
                              const MemberPattern& member,
                              cir::EntityId method,
                              const std::vector<TemplateArgument>& arguments,
                              const std::vector<ParamInput>& instantiated_params,
                              PatternInstantiationCallbacks& callbacks,
                              SrcLoc loc,
                              const TemplateArgumentBindings* exact_bindings =
                                  nullptr);
    const TemplateInfo* member_instantiation_template(
        cir::EntityId method,
        std::vector<TemplateArgument>* arguments,
        const cir::TemplateSpecializationFact** fact_out = nullptr) const;

private:
    struct MemberLookupResult;

    bool type_contains_type_parameter_pack(
        cir::TypeId type,
        std::vector<cir::TypeId>& visited) const;

    void materialize_qualifier_entity(cir::EntityId entity, SrcLoc loc);

    struct AccessContext {
        cir::EntityId declaring_entity{};
        cir::EntityId accessing_record{};
        cir::EntityId accessing_function{};
        cir::DeclContextId lexical_context{};
        bool exact = false;
    };

    enum class AccessObligationKind : uint8_t {
        Member,
        MemberLookupBase,
        BaseConversion,
    };

    struct AccessObligation {
        AccessObligationKind kind = AccessObligationKind::Member;
        cir::EntityId member{};
        cir::EntityId access_owner{};
        cir::RecordMemberAccess declared_access =
            cir::RecordMemberAccess::Public;
        cir::TypeId declaring_class{};
        cir::TypeId derived_type{};
        cir::TypeId base_type{};
        cir::TypeId designating_class{};
        cir::TypeId object_class{};
        std::vector<std::vector<AccessBaseStep>> base_routes;
        std::vector<cir::EntityId> storage_path;
        AccessContext captured_context{};
        bool fixed_context = false;
        SrcLoc loc{};
    };

    struct AccessCapture {
        std::vector<AccessObligation> obligations;
        bool active = false;
        bool retained = true;
    };

    AccessContext current_access_context() const;
    AccessContext access_context_for_entity(cir::EntityId entity) const;
    bool evaluate_access_obligation(const AccessObligation& obligation,
                                    const AccessContext& context,
                                    bool report = true);
    bool capture_access_obligation(AccessObligation obligation);
    bool check_member_access_in_context(cir::EntityId member,
                                        cir::RecordMemberAccess access,
                                        const AccessContext& context,
                                        SrcLoc loc,
                                        cir::EntityId access_owner = {},
                                        bool report = true);
    bool check_member_lookup_base_access_in_context(
        const std::vector<std::vector<AccessBaseStep>>& routes,
        cir::TypeId declaring_class,
        cir::TypeId derived_type,
        const AccessContext& context,
        SrcLoc loc,
        bool report = true);
    bool check_base_path_access_in_context(
        const std::vector<cir::EntityId>& path,
        cir::TypeId derived,
        cir::TypeId base,
        const AccessContext& context,
        SrcLoc loc);

    enum class AbstractFunctionUse : uint8_t {
        Definition,
        Call
    };

    bool diagnose_abstract_function_use(cir::TypeId function_type,
                                        AbstractFunctionUse use,
                                        SrcLoc loc);
    void record_member_declaration(cir::EntityId entity,
                                   cir::EntityId owner,
                                   cir::RecordMemberAccess access,
                                   SrcLoc loc);
    void diagnose_abstract_call_result_materialization(ExprResult& expr,
                                                       SrcLoc loc);
    void index_template_pattern_record(const TemplateInfo& info);
    void erase_template_pattern_record(const TemplateInfo& info);
    void restore_template_info(uint64_t key, TemplateInfo info);
    void erase_template_info(uint64_t key);
    cir::EntityId class_template_entity_for_record(
        cir::EntityId record) const;
    std::vector<TemplateArgument> self_template_arguments(
        const TemplateInfo& info) const;
    bool class_template_arguments_for_record(
        cir::EntityId record,
        cir::EntityId* template_entity_out,
        std::vector<TemplateArgument>* arguments_out) const;
    bool constant_parameter_declared_type_pattern_matches(
        cir::TypeRef pattern,
        cir::TypeRef argument,
        PatternBindings& bindings) const;
    bool template_argument_patterns_match(
        const std::vector<TemplateArgument>& pattern_arguments,
        const std::vector<TemplateArgument>& actual_arguments,
        PatternBindings& bindings,
        const std::vector<TemplateParameter>* pattern_parameters = nullptr,
        const std::vector<TemplateParameter>* actual_parameters = nullptr) const;
    TemplateArgumentListDeductionResult deduce_template_argument_list(
        const std::vector<TemplateParameter>& pattern_parameters,
        const std::vector<TemplateArgument>& pattern_arguments,
        const std::vector<TemplateArgument>& actual_arguments,
        PatternBindings& bindings,
        TemplateArgumentListDeductionMode mode,
        const std::vector<TemplateParameter>* actual_parameters = nullptr) const;
    bool dependent_member_friend_parameters_deduced(
        const std::vector<uint32_t>& required_type_params,
        const std::vector<uint32_t>& required_value_params,
        const std::vector<uint32_t>& required_template_params,
        const PatternBindings& bindings) const;
    bool dependent_member_friend_qualifier_matches(
        cir::EntityId record,
        cir::TypeRef qualifier_pattern,
        PatternBindings& bindings) const;
    bool dependent_member_friend_parameters_deducible_from_qualifier(
        cir::TypeRef qualifier_pattern,
        const std::vector<uint32_t>& required_type_params,
        const std::vector<uint32_t>& required_value_params,
        const std::vector<uint32_t>& required_template_params) const;
    bool dependent_member_friend_type_matches(
        cir::EntityId record,
        const cir::RecordClassFriendGrant& grant) const;
    bool dependent_member_friend_function_matches(
        cir::EntityId function,
        const cir::RecordFunctionFriendGrant& grant) const;
    bool dependent_member_friend_function_template_matches(
        cir::EntityId function,
        const cir::RecordFunctionFriendGrant& grant) const;
    bool dependent_member_friend_template_parameter_lists_match(
        const std::vector<cir::TemplateParameterPattern>& pattern,
        const std::vector<TemplateParameter>& actual,
        const PatternBindings& outer_bindings) const;
    enum class DependentTypeCorrespondenceMode : uint8_t {
        MatchPattern,
        CompareDeclarations,
    };
    bool dependent_member_friend_template_type_corresponds(
        cir::TypeId pattern,
        cir::TypeId actual,
        const PatternBindings& outer_bindings,
        const std::vector<
            std::pair<cir::TypeId, cir::TypeId>>& inner_type_params,
        DependentTypeCorrespondenceMode mode) const;
    const TemplateInfo* template_info_from_related_ordinary_binding(
        cir::DeclContextId context,
        std::string_view name,
        bool include_parents) const;
    const TemplateInfo* template_info_from_declaration(
        cir::EntityId entity) const;
    cir::DeclContextId current_instantiation_pattern_context(
        cir::DeclContextId context) const;

    struct PatternCloneJob {
        const cir::Function* pattern = nullptr;
        size_t first_block = 0;
        size_t block_count = 0;
        const std::vector<PatternHole>* holes = nullptr;
        uint32_t hole_index_base = 0;
        const std::vector<PatternScopeEvent>* events = nullptr;
        const TemplateArgumentBindings* argument_bindings = nullptr;
        PatternInstantiationCallbacks* callbacks = nullptr;
        cir::EntityId owner{};
        cir::FunctionId attach_function{};
        std::vector<cir::BlockId>* fragment_blocks = nullptr;
        std::function<void()> before_first_hole;
        std::unordered_map<uint32_t, cir::EntityId>* entity_map = nullptr;
        std::unordered_map<uint32_t, cir::InstId>* inst_map = nullptr;
        std::unordered_map<uint32_t, cir::BlockId>* block_map = nullptr;
        std::unordered_map<uint32_t, cir::InstId>* param_places = nullptr;
    };
    bool run_pattern_clone(PatternCloneJob& job);
    size_t pattern_clone_depth_ = 0;
    PatternCloneBailReason pattern_clone_bail_ = PatternCloneBailReason::None;
    void reset_pattern_clone_bail() {
        pattern_clone_bail_ = PatternCloneBailReason::None;
    }
    void note_pattern_clone_bail(PatternCloneBailReason reason) {
        if (pattern_clone_bail_ == PatternCloneBailReason::None) {
            pattern_clone_bail_ = reason;
        }
    }

public:
    cir::EntityId enclosing_injected_class_record(
        cir::DeclContextId context,
        std::string_view name) const;
    bool deduce_template_arguments_from_argument_pattern(
        const TemplateInfo& pattern_info,
        const std::vector<TemplateArgument>& pattern_arguments,
        const std::vector<TemplateArgument>& actual_arguments,
        std::vector<TemplateArgument>& deduced_arguments,
        bool complete_defaults = true);
    cir::TypeId substitute_pattern_type(
        cir::TypeId type,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        cir::TypeRef* complete_type = nullptr);
    UnevaluatedCallResolution resolve_unevaluated_call_expression(
        cir::TemplateValueExpression expression,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks);
    std::optional<ExprResult>
    materialize_resolved_template_value_expression(
        const UnevaluatedCallResolution& resolution,
        std::string* error_out = nullptr);
    cir::TypeId current_instantiation_nested_record_type(
        cir::TypeId resolved,
        const PatternInstantiationCallbacks& callbacks,
        bool& nested_in_self);
    bool populate_exact_template_parameter_bindings(
        const TemplateInfo& info,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks) const;
    std::optional<std::vector<cir::TypeRef>>
    substitute_pattern_function_parameter_pack(
        cir::TypeRef pattern,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks);
    cir::TypeRef substitute_pattern_type_ref(
        cir::TypeRef type,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks);
    cir::TypeRef substitute_builtin_pack_element_type(
        const cir::BuiltinPackElementTypePayload& pack_element,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks);
    enum class PackPatternExpansionStatus : uint8_t {
        Expanded,
        StillDependent,
        NoPacks,
        LengthMismatch,
        Failure,
    };
    PackPatternExpansionStatus expand_template_argument_pack_pattern(
        const TemplateArgument& argument,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        std::vector<TemplateArgument>* destination,
        std::vector<cir::TemplateValuePackReference>*
            discovered_references = nullptr);
    bool append_substituted_template_argument(
        const TemplateArgument& argument,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        std::vector<TemplateArgument>& destination,
        bool reject_unresolved_template_parameter,
        std::string* error_out = nullptr);
    bool type_pack_pattern_lengths_mismatch(
        cir::TypeId type,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks);
    void collect_type_pack_pattern_references(
        cir::TypeId type,
        const TemplateArgumentBindings& argument_bindings,
        const PatternInstantiationCallbacks& callbacks,
        std::vector<cir::TemplateValuePackReference>& references,
        std::unordered_set<uint32_t>& visited_types) const;
    bool substitute_template_value_argument(
        TemplateArgument& argument,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        std::string* error_out = nullptr,
        const std::unordered_set<uint32_t>*
            already_substituted_nodes = nullptr);
    bool substitute_template_template_argument(
        TemplateArgument& argument,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        std::string* error_out = nullptr);
    bool compose_constraint_parameter_mappings(
        NormalizedConstraint& form,
        uint32_t root,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        std::string* error_out = nullptr);
    bool template_arguments_equivalent(const TemplateArgument& lhs,
                                       const TemplateArgument& rhs) const;
    bool template_value_arguments_equivalent(
        const TemplateArgument& lhs,
        const TemplateArgument& rhs) const;
    bool constraint_atoms_identical(
        const ConstraintAtomIdentity& lhs,
        const ConstraintAtomIdentity& rhs) const;
    bool normalized_constraints_equivalent(
        const NormalizedConstraint& lhs,
        const NormalizedConstraint& rhs,
        uint32_t lhs_root = NormalizedConstraint::no_node,
        uint32_t rhs_root = NormalizedConstraint::no_node,
        bool declaration_equivalence = false) const;
    bool constraint_atoms_declaration_equivalent(
        const ConstraintAtomIdentity& lhs,
        const ConstraintAtomIdentity& rhs) const;
    bool normalized_constraint_contains_concept_dependent(
        const NormalizedConstraint& form,
        uint32_t root = NormalizedConstraint::no_node) const;
    bool normalized_constraint_subsumes(
        const NormalizedConstraint& lhs,
        const NormalizedConstraint& rhs,
        uint32_t lhs_root = NormalizedConstraint::no_node,
        uint32_t rhs_root = NormalizedConstraint::no_node) const;
    bool build_associated_constraint_normal_form(
        const std::vector<TemplateInfo::IntroducedConstraint>& constraints,
        std::optional<NormalizedConstraint>& form) const;
    void record_constraint_parameter_provenance(
        NormalizedConstraint& form) const;
    bool associated_constraints_equivalent(
        const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
        const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const;
    bool associated_constraints_eligible_for_subsumption(
        const std::vector<TemplateInfo::IntroducedConstraint>& constraints) const;
    bool associated_constraints_subsume(
        const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
        const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const;
    bool declaration_at_least_as_constrained(
        const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
        const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const;
    bool declaration_more_constrained(
        const std::vector<TemplateInfo::IntroducedConstraint>& lhs,
        const std::vector<TemplateInfo::IntroducedConstraint>& rhs) const;
    uint64_t normalized_constraint_fingerprint(
        const NormalizedConstraint& form) const;
    bool constraint_concept_pack_fold_argument_lengths_match(
        const NormalizedConstraint& form,
        uint32_t root = NormalizedConstraint::no_node,
        std::string* error_out = nullptr) const;

    ExprResult collect_functional_cast(cir::TypeId type,
                                       std::vector<ExprResult> arguments,
                                       SrcLoc loc = SrcLoc(),
                                       InitListSyntax syntax =
                                           InitListSyntax::Parenthesized,
                                       bool allow_explicit = true);

    struct AllocationSelection {
        cir::EntityId entity{};
        cir::AllocationFunctionForm form;
        cir::EntityId member_access_owner{};
        cir::RecordMemberAccess member_access =
            cir::RecordMemberAccess::Public;

        bool valid() const { return entity.valid(); }
    };

    struct DeallocationSelection {
        cir::EntityId entity{};
        cir::DeallocationFunctionForm form;
        cir::EntityId member_access_owner{};
        cir::RecordMemberAccess member_access =
            cir::RecordMemberAccess::Public;

        bool valid() const { return entity.valid(); }
    };

    struct NewExpressionInput {
        cir::TypeId allocated_type{};
        std::vector<ExprResult> placement_arguments;
        std::vector<ExprResult> initializer_arguments;
        cir::Fragment bound_fragment;
        cir::InstId runtime_outer_bound{};
        bool force_global = false;
        bool is_array = false;
        bool initializer_present = false;
        bool initializer_is_braced = false;
        bool initializer_is_parenthesized = false;
    };

    struct DeleteExpressionInput {
        ExprResult pointer;
        bool force_global = false;
        bool is_array = false;
    };

    bool is_meta_info_type(cir::TypeId type) const;
    std::optional<ConstMetaInfoValue> evaluate_splice_operand(
        ExprResult operand,
        SrcLoc loc,
        bool* dependent = nullptr);
    struct SpliceTemplateResolution {
        cir::EntityId template_entity{};
        bool dependent = false;
        bool has_error = false;
    };
    SpliceTemplateResolution resolve_splice_template_operand(
        ExprResult operand,
        SrcLoc loc);
    QualifierResolution resolve_splice_scope_operand(
        ExprResult operand,
        SrcLoc loc,
        bool* dependent = nullptr);
    ExprResult collect_splice_expr(ExprResult operand, SrcLoc loc);
    ExprResult collect_splice_qualified_expr(ExprResult operand,
                                             const std::vector<std::string>& path,
                                             SrcLoc loc);
    cir::TypeRef splice_type_operand(ExprResult operand, SrcLoc loc);
    ExprResult collect_reflect_type_expr(cir::TypeRef type, SrcLoc loc);
    ExprResult collect_reflect_global_namespace_expr(SrcLoc loc);
    ExprResult collect_reflect_name_expr(bool global_qualifier,
                                         const std::vector<std::string>& path,
                                         SrcLoc loc);
    ExprResult collect_new_expr(cir::TypeId type,
                                std::vector<ExprResult> arguments,
                                SrcLoc loc = SrcLoc());
    ExprResult collect_new_expr(NewExpressionInput input,
                                SrcLoc loc = SrcLoc());
    ExprResult collect_delete_expr(ExprResult pointer, SrcLoc loc = SrcLoc());
    ExprResult collect_delete_expr(DeleteExpressionInput input,
                                   SrcLoc loc = SrcLoc());
    cir::EntityId runtime_function(std::string_view symbol,
                                   cir::TypeId function_type,
                                   SrcLoc loc = SrcLoc());

    DeclResult declare_global_variable(std::string_view name,
                                       cir::TypeId type,
                                       SrcLoc loc);
    DeclResult declare_global_variable(std::string_view name,
                                       cir::TypeId type,
                                       std::optional<ExprResult> initializer = std::nullopt,
                                       SrcLoc loc = SrcLoc(),
                                       DeclFlags flags = {},
                                       bool assume_initializer = false);
    DeclResult finish_variable_declaration(DeclResult started,
                                           cir::TypeId completed_type,
                                           std::optional<ExprResult> initializer,
                                           SrcLoc loc,
                                           DeclFlags flags,
                                           std::string_view binding_name = {},
                                           ConstructorInitializationKind init_kind =
                                               ConstructorInitializationKind::Direct);
    DeclResult declare_local_variable(std::string_view name,
                                      cir::TypeId type,
                                      std::optional<ExprResult> initializer,
                                      SrcLoc loc = SrcLoc(),
                                      DeclFlags flags = {},
                                      bool assume_initializer = false);
    StructuredBindingStart begin_structured_binding(
        std::vector<StructuredBindingNameInput> names,
        SrcLoc loc);
    DeclResult finish_structured_binding(StructuredBindingStart start,
                                         DeclResult backing,
                                         SrcLoc loc,
                                         bool is_condition = false,
                                         StructuredBindingTupleInput tuple = {});
    void register_structured_binding_pack(
        std::string_view name,
        cir::EntityId declaration,
        const std::vector<cir::EntityId>& elements);
    DeclResult declare_typedef(std::string_view name,
                               cir::TypeId type,
                               SrcLoc loc = SrcLoc(),
                               DeclFlags flags = {});
    DeclResult declare_function(std::string_view name,
                                cir::TypeId result_type,
                                const std::vector<std::pair<std::string, cir::TypeId>>& params,
                                SrcLoc loc = SrcLoc());
    DeclResult declare_function_type(std::string_view name,
                                     cir::TypeId function_type,
                                     cir::TypeRef result_type,
                                     const std::vector<ParamInput>& params,
                                     SrcLoc loc = SrcLoc(),
                                     DeclFlags flags = {});

    FunctionDeclStart begin_function(std::string_view name,
                                     cir::TypeId result_type,
                                     const std::vector<std::pair<std::string, cir::TypeId>>& params,
                                     SrcLoc loc = SrcLoc());
    FunctionDeclStart begin_function_type(std::string_view name,
                                          cir::TypeId function_type,
                                          cir::TypeRef result_type,
                                          const std::vector<ParamInput>& params,
                                          SrcLoc loc = SrcLoc(),
                                          DeclFlags flags = {});
    FunctionDeclStart begin_function_type_on_entity(
        cir::EntityId entity,
        std::string_view name,
        cir::TypeId function_type,
        cir::TypeRef result_type,
        const std::vector<ParamInput>& params,
        SrcLoc loc = SrcLoc(),
        DeclFlags flags = {});
    void finish_function(StmtResult body, SrcLoc loc = SrcLoc());
    void begin_function_return_deduction(cir::EntityId fn_entity,
                                         cir::TypeId declared_type,
                                         SrcLoc loc = SrcLoc());
    cir::TypeId resolve_deduced_return_type(cir::EntityId fn_entity,
                                            cir::TypeId declared_type,
                                            SrcLoc loc,
                                            bool pattern_only = false);
    void patch_pattern_function_result_type(cir::EntityId fn_entity,
                                            cir::TypeId declared_type,
                                            SrcLoc loc = SrcLoc()) {
        (void)resolve_deduced_return_type(fn_entity, declared_type, loc,
                                          /*pattern_only=*/true);
    }
    DeclResult collect_decl_sequence(std::vector<DeclResult> declarations,
                                     SrcLoc loc = SrcLoc());
    ExprResult make_integer_literal(int64_t value,
                                    std::string spelling,
                                    cir::TypeId type,
                                    SrcLoc loc = SrcLoc());
    ExprResult make_integer_literal(cir::IntegerValue value,
                                    std::string spelling,
                                    cir::TypeId type,
                                    SrcLoc loc = SrcLoc());
    ExprResult make_integer_literal(int64_t value,
                                    std::string spelling,
                                    TokenType token_type,
                                    SrcLoc loc = SrcLoc());
    ExprResult make_integer_literal(int64_t value,
                                    std::string spelling,
                                    SrcLoc loc = SrcLoc());
    ExprResult make_nullptr_literal(SrcLoc loc = SrcLoc());
    ExprResult make_void_prvalue();
    ExprResult make_boolean_literal(bool value,
                                    std::string spelling,
                                    SrcLoc loc = SrcLoc());
    ExprResult make_dependent_boolean_expr(SrcLoc loc = SrcLoc());
    ExprResult make_imaginary_literal(syntax::FloatingLiteralKind kind,
                                      std::string spelling,
                                      SrcLoc loc = SrcLoc());
    ExprResult collect_complex_part_expr(ExprResult operand, bool imaginary, SrcLoc loc);
    cir::TypeId complex_element_type(cir::TypeId type) const;
    ExprResult make_floating_literal(syntax::FloatingLiteralKind kind,
                                     std::string spelling,
                                     SrcLoc loc = SrcLoc());
    ExprResult make_floating_value(cir::FloatingValue value,
                                   cir::TypeId type,
                                   std::string spelling,
                                   SrcLoc loc = SrcLoc());
    ExprResult make_character_literal(std::string decoded,
                                      LiteralPrefix prefix,
                                      std::string spelling,
                                      SrcLoc loc = SrcLoc());
    ExprResult make_string_literal(std::string value,
                                   std::string spelling = {},
                                   SrcLoc loc = SrcLoc(),
                                   LiteralPrefix prefix = LiteralPrefix::None);
    ExprResult collect_user_defined_literal(
        ExprResult literal,
        UserDefinedLiteralKind kind,
        std::string suffix,
        std::string base_spelling,
        SrcLoc loc = SrcLoc());
    ExprResult lookup_name(std::string_view name,
                           SrcLoc loc = SrcLoc(),
                           bool allow_unresolved = false);
    ExprResult expr_result_for_binding(const cir::Binding& binding,
                                       std::string_view name,
                                       SrcLoc loc = SrcLoc());
    cir::InstId materialize_implicit_object_place(
        const char* label,
        cir::Fragment* fragment_out,
        SrcLoc loc = SrcLoc());
    ExprResult structured_binding_expr_result(cir::EntityId binding,
                                              std::string_view name,
                                              SrcLoc loc = SrcLoc());
    cir::InstId structured_binding_projection_place(cir::EntityId binding,
                                                     SrcLoc loc = SrcLoc());
    ExprResult make_entity_reference(cir::EntityId entity,
                                     std::string_view name,
                                     SrcLoc loc = SrcLoc(),
                                     bool qualified_name = false);
    ExprResult lookup_name_fallback(std::string_view name,
                                    SrcLoc loc = SrcLoc(),
                                    bool allow_unresolved = false);
    ExprResult collect_sizeof_type(cir::TypeId type,
                                   SrcLoc loc = SrcLoc(),
                                   cir::Fragment vla_bounds = {});
    ExprResult collect_sizeof_pack(std::string_view name,
                                   SrcLoc loc = SrcLoc());
    bool variably_modified_type(cir::TypeId type) const;
    ExprResult collect_alignof_type(cir::TypeId type, SrcLoc loc = SrcLoc());
    bool typeid_operand_is_potentially_evaluated(const ExprResult& operand) const;
    ExprResult collect_typeid_expr(ExprResult operand, SrcLoc loc = SrcLoc());
    ExprResult collect_typeid_type(cir::TypeId type, SrcLoc loc = SrcLoc());
    ExprResult collect_unary_expr(syntax::UnaryOperator op,
                                  ExprResult operand,
                                  SrcLoc loc = SrcLoc());
    ExprResult collect_cast_expr(cir::TypeId target_type,
                                 ExprResult operand,
                                 SrcLoc loc = SrcLoc());
    ExprResult collect_cast_to_union(cir::TypeId target_type,
                                     cir::TypeId union_type,
                                     ExprResult operand,
                                     SrcLoc loc = SrcLoc());
    ExprResult collect_cpp_named_cast(CppNamedCastKind kind,
                                      cir::TypeId target_type,
                                      ExprResult operand,
                                      SrcLoc loc = SrcLoc());
    ExprResult collect_generic_selection(ExprResult controlling,
                                         std::vector<GenericAssociation> associations,
                                         SrcLoc loc = SrcLoc());
    void collect_static_assert(ExprResult condition,
                               bool value_dependent,
                               std::string message,
                               bool has_message,
                               LifetimeBoundary boundary,
                               SrcLoc loc = SrcLoc());
    cir::FunctionExceptionSpec evaluate_noexcept_spec(
        const ExprResult& operand,
        SrcLoc loc = SrcLoc());
    void collect_file_scope_asm(std::string asm_string, SrcLoc loc = SrcLoc());
    void ensure_vla_stack_slot(SrcLoc loc = SrcLoc());
    cir::TypeId substitute_vla_parameter_bounds(
        cir::TypeId type,
        const std::unordered_map<std::string, cir::InstId>& parameter_values);
    cir::Fragment chain(cir::Fragment first, cir::Fragment second, SrcLoc loc = SrcLoc());
    bool types_compatible(cir::TypeRef lhs, cir::TypeRef rhs,
                          bool ignore_top_qualifiers = false) const;
    bool same_type_identity(cir::TypeRef lhs, cir::TypeRef rhs) const;
    enum class QualificationTargetKind : uint8_t {
        Concrete,
        TypePattern,
        ReferenceCompatible,
    };
    struct QualificationConversionAnalysis {
        bool similar = false;
        bool allowed = false;
        bool has_indirection = false;
    };
    QualificationConversionAnalysis analyze_qualification_conversion(
        cir::TypeRef source,
        cir::TypeRef target,
        QualificationTargetKind target_kind =
            QualificationTargetKind::Concrete) const;
    bool transparent_union_accepts(cir::TypeRef union_ref, cir::TypeRef other) const;
    ExprResult wrap_in_transparent_union(ExprResult member_value,
                                         cir::TypeId union_type,
                                         const cir::RecordFieldFact& field,
                                         SrcLoc loc);
    cir::EntityId string_literal_entity(cir::InstId literal_inst, SrcLoc loc = SrcLoc());
    ExprResult collect_conditional_expr(ExprResult condition,
                                        std::optional<ExprResult> true_expr,
                                        ExprResult false_expr,
                                        SrcLoc loc = SrcLoc());
    ExprResult collect_init_list_expr(
        std::vector<InitElementInput> elements,
        SrcLoc loc = SrcLoc(),
        InitListSyntax syntax = InitListSyntax::Braced);
    ExprResult collect_initialized_prvalue(cir::TypeId type,
                                           ExprResult initializer,
                                           SrcLoc loc = SrcLoc());
    ExprResult collect_compound_literal_expr(cir::TypeId type,
                                             ExprResult initializer,
                                             SrcLoc loc = SrcLoc());
    ExprResult collect_unsupported_expr(std::string message,
                                        std::vector<ExprResult> children = {},
                                        SrcLoc loc = SrcLoc());
    ExprResult collect_binary_expr_builtin(syntax::BinaryOperator op,
                                           ExprResult lhs,
                                           ExprResult rhs,
                                           SrcLoc loc = SrcLoc());
    ExprResult make_dependent_binary_operator_expr(
        syntax::BinaryOperator op,
        ExprResult lhs,
        ExprResult rhs,
        SrcLoc loc = SrcLoc());
    ExprResult make_dependent_fold_expression(
        cir::TemplateValueFoldKind fold_kind,
        syntax::BinaryOperator op,
        ExprResult pattern,
        std::optional<ExprResult> initializer,
        std::vector<cir::TemplateValuePackReference> pack_references,
        SrcLoc loc = SrcLoc());
    enum class ComparisonCategoryKind : uint8_t {
        Strong,
        Weak,
        Partial,
    };
    struct ComparisonCategory {
        ComparisonCategoryKind kind = ComparisonCategoryKind::Strong;
        cir::TypeId type{};
        cir::EntityId less{};
        cir::EntityId equivalent{};
        cir::EntityId greater{};
        cir::EntityId unordered{};
    };
    std::optional<ComparisonCategory> resolve_comparison_category(
        ComparisonCategoryKind kind,
        SrcLoc loc,
        bool diagnose = true);
    ExprResult collect_builtin_three_way_compare(ExprResult lhs,
                                                 ExprResult rhs,
                                                 SrcLoc loc);
    ExprResult collect_synthesized_three_way_compare(
        ExprResult lhs,
        ExprResult rhs,
        const ComparisonCategory& result_category,
        bool allow_fallback,
        SrcLoc loc);
    void plan_and_synthesize_defaulted_comparisons(cir::EntityId record,
                                                    bool synthesize_bodies,
                                                    SrcLoc loc);
    void synthesize_defaulted_friend_comparison(cir::EntityId function,
                                                cir::EntityId record,
                                                bool has_explicit_exception_spec,
                                                SrcLoc loc);
    bool defaulted_comparison_function_potentially_throws(
        cir::FunctionId function);
    void publish_defaulted_comparison_properties(
        cir::EntityId function,
        bool implicitly_constexpr,
        bool compute_implicit_exception_spec,
        bool potentially_throwing);
    ExprResult collect_defaulted_array_equality(cir::InstId lhs_place,
                                                cir::InstId rhs_place,
                                                cir::TypeId array_type,
                                                SrcLoc loc);
    ExprResult collect_defaulted_array_three_way(
        cir::InstId lhs_place,
        cir::InstId rhs_place,
        cir::TypeId array_type,
        const ComparisonCategory& result_category,
        bool allow_fallback,
        SrcLoc loc);
    ExprResult collect_binary_expr(syntax::BinaryOperator op,
                                   ExprResult lhs,
                                   ExprResult rhs,
                                   SrcLoc loc = SrcLoc());
    ExprResult collect_binary_expr_impl(syntax::BinaryOperator op,
                                        ExprResult lhs,
                                        ExprResult rhs,
                                        SrcLoc loc,
                                        bool allow_comparison_rewrites);
    ExprResult fold_immediate_invocation(ExprResult call, SrcLoc loc);
    ExprResult fold_immediate_constructor_invocation(
        ExprResult object,
        cir::InstId destination,
        cir::EntityId constructor,
        SrcLoc loc);
    ExprResult collect_call_expr_impl(ExprResult callee,
                                      std::vector<ExprResult> args,
                                      SrcLoc loc);
    ExprResult collect_call_expr(ExprResult callee,
                                 std::vector<ExprResult> args,
                                 SrcLoc loc = SrcLoc());
    ExprResult collect_va_arg_expr(ExprResult va_list,
                                   cir::TypeId arg_type,
                                   SrcLoc loc = SrcLoc());
    ExprResult collect_atomic_builtin(std::string_view name,
                                      BuiltinKind kind,
                                      std::vector<ExprResult> args,
                                      SrcLoc loc);
    ExprResult collect_source_location_builtin(SrcLoc loc);
    ExprResult collect_builtin_call(std::string_view name,
                                    BuiltinKind kind,
                                    std::vector<ExprResult> args,
                                    SrcLoc loc = SrcLoc());
    ExprResult collect_builtin_convertvector_expr(ExprResult vector,
                                                  cir::TypeRef target_type,
                                                  SrcLoc loc = SrcLoc());
    ExprResult collect_builtin_bit_cast_expr(cir::TypeRef target_type,
                                             ExprResult source,
                                             SrcLoc loc = SrcLoc());
    ExprResult collect_builtin_types_compatible_expr(cir::TypeId lhs,
                                                     cir::TypeId rhs,
                                                     SrcLoc loc = SrcLoc());
    ExprResult collect_builtin_type_trait_expr(BuiltinKind kind,
                                               std::vector<cir::TypeRef> type_args,
                                               std::vector<bool> pack_expansions,
                                               SrcLoc loc = SrcLoc());
    static std::optional<cir::BuiltinTypeTraitKind>
    builtin_type_trait_kind(BuiltinKind kind);
    static std::optional<BuiltinKind> builtin_kind_for_type_trait(
        cir::BuiltinTypeTraitKind kind);
    std::optional<bool> evaluate_builtin_type_trait(
        BuiltinKind kind,
        const std::vector<cir::TypeRef>& type_args,
        SrcLoc loc = SrcLoc());
    ExprResult collect_builtin_choose_expr(ExprResult condition,
                                           ExprResult true_expr,
                                           ExprResult false_expr,
                                           SrcLoc loc = SrcLoc());
    ExprResult collect_offsetof_expr(cir::TypeId type,
                                     std::vector<InitDesignator> designators,
                                     SrcLoc loc = SrcLoc());
    ExprResult collect_array_subscript_expr(ExprResult base,
                                            ExprResult index,
                                            SrcLoc loc = SrcLoc());
    struct MemberAccessBase {
        ExprResult base_place;
        cir::TypeId record_type{};
    };
    MemberAccessBase collect_member_access_base(ExprResult base,
                                                bool is_arrow,
                                                SrcLoc loc);
    const TemplateInfo* member_template_info_for_access(
        const ExprResult& base,
        std::string_view member_name,
        bool is_arrow) const;
    ExprResult collect_qualified_member_access_expr(ExprResult base,
                                                    cir::TypeId qualifier_type,
                                                    std::string_view member_name,
                                                    bool is_arrow,
                                                    SrcLoc loc,
                                                    std::vector<cir::EntityId>
                                                        resolved_methods = {});
    ExprResult collect_resolved_member_function_access_expr(
        ExprResult base,
        cir::EntityId method,
        std::string_view member_name,
        bool is_arrow,
        SrcLoc loc = SrcLoc());
    ExprResult collect_resolved_member_function_access_expr(
        ExprResult base,
        std::vector<cir::EntityId> methods,
        std::string_view member_name,
        bool is_arrow,
        SrcLoc loc = SrcLoc());
    ExprResult collect_conversion_function_id_access_expr(
        ExprResult base,
        cir::TypeRef target_type,
        bool is_arrow,
        SrcLoc loc = SrcLoc(),
        cir::TypeId qualifier_type = {});
    ExprResult materialize_qualified_data_member(ExprResult expr,
                                                 SrcLoc loc);
    ExprResult collect_bound_member_function_access_expr(
        MemberAccessBase access,
        std::vector<cir::EntityId> candidates,
        std::string_view member_name,
        SrcLoc loc = SrcLoc(),
        const MemberLookupResult* lookup = nullptr);
    ExprResult collect_member_access_expr(ExprResult base,
                                          std::string_view member_name,
                                          bool is_arrow,
                                          SrcLoc loc = SrcLoc());
    ExprResult collect_explicit_destructor_call(
        ExprResult base,
        cir::TypeId named_type,
        cir::TypeId qualifier_type,
        bool is_arrow,
        bool is_qualified,
        SrcLoc loc = SrcLoc());
    cir::TypeId complete_initializer_type(cir::TypeId type,
                                          const ExprResult& initializer,
                                          SrcLoc loc = SrcLoc());
    bool evaluate_integer_constant(const ExprResult& expr,
                                   int64_t& value,
                                   SrcLoc loc = SrcLoc(),
                                   std::string_view diagnostic =
                                       "expression is not an integer constant expression");
    bool try_evaluate_integer_constant(
        const ExprResult& expr,
        int64_t& value,
        cir::EntityId* dependency = nullptr);
    bool try_evaluate_integer_constant_value(
        const ExprResult& expr,
        cir::IntegerValue& value,
        cir::EntityId* dependency = nullptr);
    bool try_evaluate_required_integer_constant(const ExprResult& expr,
                                                int64_t& value,
                                                SrcLoc loc);
    ConstEvalContext make_consteval_context(LangOptions options) const;
    bool evaluate_constraint_expression(ExprResult expr,
                                        bool value_dependent,
                                        std::optional<bool>& value,
                                        SrcLoc loc = SrcLoc());
    struct TemplateValueConstant {
        cir::TemplateValueKind kind = cir::TemplateValueKind::None;
        cir::TemplateNullKind null_kind = cir::TemplateNullKind::None;
        cir::IntegerValue integer_value;
        cir::FloatingValue floating_value;
        cir::EntityId entity{};
        cir::ClosureIdentityId closure_identity{};
        int64_t byte_offset = 0;
        std::vector<TemplateArgument> elements;
        cir::MetaInfoKind meta_kind = cir::MetaInfoKind::Null;
        cir::TypeRef meta_type{};
    };
    bool evaluate_template_value_constant(
        ExprResult expr,
        cir::TypeId expected_type,
        TemplateValueConstant& value,
        SrcLoc loc = SrcLoc(),
        std::string_view diagnostic =
            "template argument is not a constant expression");
    bool template_value_constant_from_entity(
        cir::EntityId entity,
        TemplateValueConstant& value) const;
    bool build_template_value_argument(
        cir::TypeId expected_type,
        const TemplateValueConstant& constant,
        TemplateArgument& argument,
        std::string* error_out = nullptr) const;
    bool build_generated_integer_pack(
        cir::TypeId value_type,
        ExprResult count,
        TemplateArgument& dependent_pack,
        std::vector<TemplateArgument>& concrete_arguments,
        SrcLoc loc = SrcLoc(),
        std::string* error_out = nullptr);
    bool append_substituted_generated_pack(
        const TemplateArgument& generated_pack,
        const TemplateArgumentBindings& argument_bindings,
        PatternInstantiationCallbacks& callbacks,
        std::vector<TemplateArgument>& destination,
        bool reject_unresolved_template_parameter,
        std::string* error_out = nullptr);
    ExprResult require_value(ExprResult expr,
                             UseContext context = UseContext::RValue,
                             SrcLoc loc = SrcLoc());
    ExprResult require_place(ExprResult expr,
                             UseContext context = UseContext::LValue,
                             SrcLoc loc = SrcLoc());
    ExprResult convert_to(ExprResult expr,
                          cir::TypeId type,
                          UseContext context,
                          SrcLoc loc = SrcLoc());
    ExprResult materialize_list_initialization(ExprResult expr,
                                               cir::TypeId type,
                                               UseContext context,
                                               SrcLoc loc = SrcLoc(),
                                               cir::StorageDuration
                                                   backing_duration =
                                                       cir::StorageDuration::Temporary);
    std::optional<ExprResult> try_materialize_fixed_enum_direct_list(
        ExprResult& expr,
        cir::TypeId type,
        UseContext context,
        SrcLoc loc = SrcLoc());
    ExprResult convert_function_designator_to_target(ExprResult expr,
                                                     cir::TypeId target_type,
                                                     SrcLoc loc = SrcLoc());
    ExprResult convert_member_pointer_designator_to_target(ExprResult expr,
                                                           cir::TypeId target_type,
                                                           SrcLoc loc = SrcLoc());
    ExprResult convert_overload_designator_to_target(ExprResult expr,
                                                     cir::TypeId target_type,
                                                     SrcLoc loc = SrcLoc());
    ExprResult call_conversion_function(ExprResult expr,
                                        cir::EntityId conversion_function,
                                        cir::TypeId target_type,
                                        SrcLoc loc = SrcLoc());
    void discard_value(ExprResult expr, SrcLoc loc = SrcLoc());

    bool array_type_has_const_element(cir::TypeId type) const;
    bool is_reference_type(cir::TypeId type) const;
    bool is_null_pointer_constant(const ExprResult& expr) const;
    ExprResult deref_reference_lvalue(ExprResult expr, SrcLoc loc = SrcLoc());
    ExprResult bind_to_reference(ExprResult expr,
                                 cir::TypeId reference_type,
                                 SrcLoc loc = SrcLoc(),
                                 UserConversionContext conversion_context =
                                     UserConversionContext::CopyInitialization);
    ExprResult materialize_deferred_entity_place(
        ExprResult expr,
        bool allow_non_odr_constant,
        SrcLoc loc = SrcLoc());
    cir::EntityId current_function_entity() const;
    bool is_cross_function_local(cir::EntityId entity) const;
    bool is_default_argument_local(cir::EntityId entity) const;
    bool lambda_capture_source_usable(cir::EntityId entity) const;
    bool note_potential_lambda_capture(cir::EntityId entity, SrcLoc loc);

    StmtResult collect_decl_stmt(DeclResult decl, SrcLoc loc = SrcLoc());
    StmtResult collect_expr_stmt(ExprResult expr,
                                 SrcLoc loc = SrcLoc(),
                                 const FullExpressionWatermark* mark = nullptr);
    StmtResult collect_return_stmt(
        std::optional<ExprResult> expr,
        SrcLoc loc,
        LifetimeBoundary boundary);
    StmtResult collect_return_stmt(std::optional<ExprResult> expr,
                                   SrcLoc loc = SrcLoc()) {
        return collect_return_stmt(std::move(expr), loc, LifetimeBoundary{});
    }
    ExprResult collect_await_expr(ExprResult operand, SrcLoc loc);
    ExprResult collect_yield_expr(ExprResult operand, SrcLoc loc);
    StmtResult collect_co_return_stmt(std::optional<ExprResult> operand,
                                      SrcLoc loc,
                                      LifetimeBoundary boundary);
    struct CoroutinePromiseResolution {
        cir::TypeId traits_specialization{};
        cir::TypeId promise_type{};
        cir::TypeId handle_type{};
    };
    using CoroutinePromiseCallback =
        std::function<CoroutinePromiseResolution(
            const std::vector<cir::TypeRef>& traits_arguments, SrcLoc loc)>;
    CoroutinePromiseCallback set_coroutine_promise_callback(
        CoroutinePromiseCallback callback);
    StmtResult collect_compound_stmt(std::vector<StmtResult> children, SrcLoc loc = SrcLoc());
    void begin_control_flow_limited_statement();
    void end_control_flow_limited_statement();
    struct ExpansionControlSummary {
        bool has_break = false;
        bool has_continue = false;
    };
    void begin_expansion_statement(cir::BlockId continue_target,
                                   cir::BlockId break_target);
    ExpansionControlSummary end_expansion_statement();
    cir::BlockId create_statement_target(std::string name);
    StmtResult collect_statement_target(cir::BlockId target,
                                        SrcLoc loc = SrcLoc());
    StmtResult collect_expansion_element(DeclResult declaration,
                                         StmtResult body,
                                         StmtResult normal_cleanups,
                                         cir::BlockId continue_target,
                                         SrcLoc loc = SrcLoc());
    StmtResult collect_expansion_sequence(std::vector<StmtResult> children,
                                          cir::BlockId break_target,
                                          SrcLoc loc = SrcLoc());
    void begin_expansion_label_region();
    void end_expansion_label_region();
    bool identifier_labels_forbidden() const {
        return expansion_label_region_depth_ != 0;
    }
    StmtResult declare_local_labels(std::vector<std::string> names, SrcLoc loc = SrcLoc());
    StmtResult collect_label_stmt(std::string_view name, StmtResult child, SrcLoc loc = SrcLoc());
    StmtResult collect_goto_stmt(std::string_view name, SrcLoc loc = SrcLoc());
    StmtResult collect_computed_goto_stmt(ExprResult target, SrcLoc loc = SrcLoc());
    StmtResult collect_asm_stmt(std::string asm_string,
                                std::vector<AsmOperand> outputs,
                                std::vector<AsmOperand> inputs,
                                std::vector<std::string> clobbers,
                                std::vector<std::string> goto_labels,
                                bool is_volatile,
                                bool is_inline,
                                bool is_goto,
                                SrcLoc loc = SrcLoc());
    StmtResult collect_break_stmt(SrcLoc loc = SrcLoc());
    StmtResult collect_scope_cleanups(SrcLoc loc = SrcLoc());
    StmtResult collect_continue_stmt(SrcLoc loc = SrcLoc());
    ExprResult collect_label_address_expr(std::string_view name, SrcLoc loc = SrcLoc());
    ExprResult collect_statement_expr(StmtResult body, SrcLoc loc = SrcLoc());
    ExprResult collect_block_literal_expr(SrcLoc loc = SrcLoc());
    BlockLiteralStart begin_block_literal(std::vector<ParamInput> params,
                                          const std::vector<std::string>& body_identifiers,
                                          SrcLoc loc);
    ExprResult finish_block_literal(BlockLiteralStart start,
                                    StmtResult body,
                                    SrcLoc loc);
    class ClosureAbiContextScope {
    public:
        ClosureAbiContextScope() = default;
        ClosureAbiContextScope(const ClosureAbiContextScope&) = delete;
        ClosureAbiContextScope& operator=(const ClosureAbiContextScope&) =
            delete;
        ClosureAbiContextScope(ClosureAbiContextScope&& other) noexcept
            : session_(other.session_) {
            other.session_ = nullptr;
        }
        ClosureAbiContextScope& operator=(
            ClosureAbiContextScope&& other) noexcept {
            if (this != &other) {
                close();
                session_ = other.session_;
                other.session_ = nullptr;
            }
            return *this;
        }
        ~ClosureAbiContextScope() { close(); }

    private:
        friend class Session;
        explicit ClosureAbiContextScope(Session* session)
            : session_(session) {}
        void close();
        Session* session_ = nullptr;
    };
    ClosureAbiContextScope enter_variable_initializer_closure_context(
        std::string_view variable_name);
    LambdaClosureStart begin_lambda_closure(std::vector<ParamInput> params,
                                            cir::TypeId trailing_return_type,
                                            LambdaSpecifiers specifiers,
                                            LambdaCaptureDefault capture_default,
                                            std::vector<LambdaCaptureItem> explicit_captures,
                                            SrcLoc loc);
    ExprResult finish_lambda_closure(LambdaClosureStart start,
                                     StmtResult body,
                                     SrcLoc loc);
    LambdaClosureStart begin_generic_lambda_closure(
        std::vector<ParamInput> params,
        cir::TypeId trailing_return_type,
        LambdaSpecifiers specifiers,
        LambdaCaptureDefault capture_default,
        std::vector<LambdaCaptureItem> explicit_captures,
        TemplateInfo& info,
        SrcLoc loc);
    ExprResult finish_generic_lambda_closure(LambdaClosureStart start,
                                             TemplateInfo info,
                                             SrcLoc loc);
    void push_lambda_instantiation_frame(cir::EntityId method);
    void pop_lambda_instantiation_frame();
    bool in_lambda_body() const { return !lambda_stack_.empty(); }
    void set_in_default_argument_replay(bool active,
                                        SrcLoc call_site = SrcLoc()) {
        if (active) {
            if (default_argument_replay_depth_ == 0) {
                default_argument_boundary_function_ =
                    current_function_entity();
            }
            ++default_argument_replay_depth_;
            default_argument_call_sites_.push_back(call_site);
        } else if (default_argument_replay_depth_ > 0) {
            --default_argument_replay_depth_;
            if (!default_argument_call_sites_.empty()) {
                default_argument_call_sites_.pop_back();
            }
            if (default_argument_replay_depth_ == 0) {
                default_argument_boundary_function_ = {};
            }
        }
    }
    bool in_default_argument_replay() const {
        return default_argument_replay_depth_ > 0;
    }
    SrcLoc default_argument_call_site() const {
        return default_argument_call_sites_.empty()
            ? SrcLoc()
            : default_argument_call_sites_.front();
    }
    cir::EntityId enclosing_record_for_context(
        cir::DeclContextId context) const {
        while (context.valid() && file_.valid(context)) {
            const cir::DeclContext& decl_context = file_.decl_context(context);
            if (decl_context.kind == cir::DeclContextKind::Record &&
                decl_context.owner.valid()) {
                return decl_context.owner;
            }
            context = decl_context.parent;
        }
        return {};
    }
    cir::EntityId override_member_access_record(cir::EntityId record) {
        cir::EntityId previous = current_member_record_;
        current_member_record_ = record;
        return previous;
    }
    cir::EntityId override_member_access_function(cir::EntityId function) {
        cir::EntityId previous = member_access_function_override_;
        member_access_function_override_ = function;
        return previous;
    }
    struct CompleteClassInitializerScope {
        cir::EntityId previous_record{};
        cir::InstId previous_object_place{};
        bool previous_collecting_initializer = false;
    };
    CompleteClassInitializerScope begin_complete_class_initializer(
        cir::EntityId record,
        cir::InstId object_place);
    void finish_complete_class_initializer(
        CompleteClassInitializerScope scope);
    cir::EntityId extern_runtime_global(std::string_view symbol, SrcLoc loc);
    ExprResult collect_throw_expr(std::optional<ExprResult> operand,
                                  SrcLoc loc = SrcLoc());
    bool expression_potentially_throws(const ExprResult& expr,
                                       bool* dependent = nullptr);
    ExprResult collect_noexcept_expr(ExprResult operand,
                                     bool potentially_throwing,
                                     bool dependent,
                                     SrcLoc loc);
    cir::EntityId typeinfo_entity_for_type(cir::TypeRef type, SrcLoc loc);
    cir::TypeId resolve_std_type_info_type(SrcLoc loc);
    cir::EntityId class_typeinfo_entity(cir::EntityId record_entity,
                                        const cir::RecordFacts& facts,
                                        SrcLoc loc);
    cir::TypeId block_header_record_type(SrcLoc loc);
    void begin_local_label_scope();
    void end_local_label_scope(SrcLoc loc = SrcLoc());

    StmtResult collect_if_stmt(ExprResult condition,
                               StmtResult then_result,
                               std::optional<StmtResult> else_result,
                               SrcLoc loc,
                               LifetimeBoundary condition_boundary);

    WhileControl begin_while(SrcLoc loc = SrcLoc());
    void begin_while_body(WhileControl& control,
                          ExprResult condition,
                          LifetimeBoundary condition_boundary);
    StmtResult finish_while(WhileControl& control, const StmtResult& body_result);
    ForControl begin_for(SrcLoc loc = SrcLoc());
    RangeEndpointPlan plan_range_endpoints(const ExprResult& range_object,
                                           bool allow_array,
                                           bool diagnose_missing,
                                           SrcLoc loc = SrcLoc());
    ExprResult collect_range_endpoint(const RangeEndpointPlan& plan,
                                      ExprResult range_object,
                                      bool begin,
                                      SrcLoc loc = SrcLoc());
    void begin_for_body(ForControl& control,
                        std::optional<StmtResult> init,
                        std::optional<ExprResult> condition,
                        std::optional<ExprResult> step,
                        LifetimeBoundary condition_boundary,
                        LifetimeBoundary step_boundary);
    StmtResult finish_for(ForControl& control, const StmtResult& body_result);
    DoWhileControl begin_do_while(SrcLoc loc = SrcLoc());
    StmtResult finish_do_while(DoWhileControl& control,
                               ExprResult condition,
                               const StmtResult& body_result,
                               LifetimeBoundary condition_boundary);
    SwitchControl begin_switch(ExprResult condition,
                               SrcLoc loc,
                               LifetimeBoundary condition_boundary);
    StmtResult collect_case_stmt(std::vector<SwitchLabelInput> labels,
                                 StmtResult child,
                                 SrcLoc loc = SrcLoc());
    StmtResult finish_switch(SwitchControl& control, const StmtResult& body_result);

    TryControl begin_try(
        SrcLoc loc = SrcLoc(),
        TryRegionKind kind = TryRegionKind::Statement);
    void finish_try_body(TryControl& control, StmtResult body);
    void begin_catch_handler(TryControl& control,
                             std::optional<cir::TypeRef> catch_type,
                             std::string_view param_name,
                             SrcLoc loc = SrcLoc());
    void finish_catch_handler(TryControl& control,
                              StmtResult body,
                              SrcLoc loc = SrcLoc());
    StmtResult finish_try(TryControl& control, SrcLoc loc = SrcLoc());

private:
    struct ObjCState {
        bool initialized = false;
        cir::TypeId object_record_type{};
        cir::TypeId class_record_type{};
        cir::TypeId selector_record_type{};
        cir::TypeId id_type{};
        cir::TypeId class_type{};
        cir::TypeId sel_type{};
        std::unordered_map<std::string, cir::EntityId> classes;
        std::unordered_map<std::string, cir::EntityId> protocols;
        std::vector<std::vector<std::string>> type_param_stack;
        struct PoolEntry {
            cir::EntityId interface{};
            bool is_class_method = false;
        };
        std::unordered_map<uint32_t, std::vector<PoolEntry>> method_pool;
        cir::EntityId current_interface{};
        bool in_class_method = false;
        cir::ObjCMethodFamily current_method_family =
            cir::ObjCMethodFamily::None;
        cir::EntityId strong_destroy_helper{};
    };
    ObjCState objc_;
    bool arc_enabled() const {
        return lang_opts_.is_objc_arc() && objc_.initialized;
    }
    bool arc_retainable_type(cir::TypeId type) const;
    cir::ObjCOwnership arc_ownership_of(cir::EntityId entity) const;
    cir::ObjCOwnership arc_ownership_of_ref(cir::TypeRef ref) const;
    cir::EntityId arc_strong_destroy_helper(SrcLoc loc);
    cir::EntityId arc_weak_destroy_function(SrcLoc loc);
    cir::LifetimeId register_arc_cleanup(cir::EntityId entity,
                                         cir::TypeId type,
                                         cir::EntityId cleanup_function,
                                         SrcLoc loc,
                                         bool full_expression_temporary = false);
    ExprResult arc_retain_value(ExprResult value, SrcLoc loc);
    ExprResult arc_release_discarded(ExprResult value, SrcLoc loc);
    void arc_finish_local_declaration(DeclResult& started,
                                      bool zero_initialize,
                                      SrcLoc loc);
    ExprResult arc_adjust_return_value(ExprResult value, SrcLoc loc);
    cir::InstId arc_null_object(SrcLoc loc);
    bool expr_reads_objc_self(const ExprResult& expr) const;
    struct ArcPendingRelease {
        uint64_t token = 0;
        uint64_t boundary = 0;
        cir::InstId value{};
        bool claimed = false;
    };
    void arc_schedule_pending_release(ExprResult& expr);
    void arc_claim_plus_one(const ExprResult& expr);
    cir::Fragment arc_flush_boundary_releases(uint64_t boundary_id,
                                              SrcLoc loc);
    void arc_drop_boundary_releases(uint64_t boundary_id);
    void initialize_objc_mode();
    cir::EntityId objc_interface_for_object_type(cir::TypeId object_type) const;
    ExprResult collect_objc_ivar_access(ExprResult base,
                                        cir::EntityId interface,
                                        std::string_view ivar_name,
                                        SrcLoc loc);
    ExprResult collect_objc_property_reference(ExprResult base,
                                               cir::EntityId interface,
                                               std::string_view name,
                                               SrcLoc loc);
    ExprResult resolve_objc_property_load(ExprResult expr, SrcLoc loc);
    ExprResult collect_objc_subscript_reference(ExprResult base,
                                                ExprResult index,
                                                SrcLoc loc);
    const cir::ObjCMethodFact* find_objc_method(cir::EntityId interface,
                                                cir::SelectorId selector,
                                                bool class_method) const;
    cir::ObjCMethodFact* find_objc_method_mut(cir::EntityId interface,
                                              cir::SelectorId selector,
                                              bool class_method);
    cir::TypeId objc_object_pointer_type(cir::EntityId interface);
    cir::ObjCMethodFact build_objc_method_fact(cir::EntityId interface,
                                               ObjCMethodInput& method,
                                               cir::EntityId method_entity);

    enum class TagLookupMode {
        CurrentOnly,
        Visible
    };

    struct TagLookupResult {
        const cir::Binding* binding = nullptr;
        cir::EntityId entity{};
        cir::TypeId type{};
        const cir::RecordFacts* facts = nullptr;
        bool found = false;
        bool kind_mismatch = false;
    };

    struct ConstructorCallMaterialization {
        cir::EntityId constructor{};
        std::vector<cir::InstId> argument_values;
        cir::Fragment argument_fragment;
        bool has_error = false;
        bool ambiguous = false;
    };
    ConstructorCallMaterialization materialize_constructor_call(
        cir::TypeId record_type,
        std::vector<ExprResult> arguments,
        SrcLoc loc,
        ConstructorInitializationKind init_kind =
            ConstructorInitializationKind::Direct);
    ConstructorCallMaterialization materialize_selected_constructor_call(
        cir::EntityId constructor,
        std::vector<ExprResult> arguments,
        SrcLoc loc,
        cir::TypeId direct_constructor_target = {});
    ExprResult materialize_constructor_parameter_argument(
        ExprResult argument,
        cir::TypeId parameter_type,
        SrcLoc loc);
    cir::EntityId synthesize_inherited_variadic_call_constructor(
        cir::EntityId constructor,
        const std::vector<cir::TypeRef>& argument_types,
        SrcLoc loc);
    ExprResult inherited_constructor_forwarding_argument(
        const ParamInput& parameter,
        SrcLoc loc);

    struct ScopeFrame {
        ScopeId parent = InvalidScopeId;
        ScopeFlags flags = ScopeFlags::None;
        cir::DeclContextId context{};
        std::vector<RecordBaseInput> pending_bases;
        std::vector<std::pair<std::string, cir::EntityId>>
            structured_binding_packs;
    };

    struct CleanupRecord {
        cir::LifetimeId lifetime{};
        cir::EntityId variable{};
        cir::TypeId variable_type{};
        cir::EntityId function{};
        SrcLoc loc{};
        LifetimeOwnerKind owner = LifetimeOwnerKind::LexicalScope;
        uint64_t owner_id = 0;
        cir::BlockId normal_unwind_target{};
    };
    struct LifetimeRecord {
        cir::InstId start{};
        cir::EntityId variable{};
        cir::TypeId variable_type{};
    };
    struct CleanupScope {
        size_t control_depth_at_entry = 0;
        std::vector<CleanupRecord> records;
        cir::BlockId entry_unwind_target{};
        std::vector<LifetimeRecord> lifetime_records;
        bool suppress_lifetimes = false;
    };
    struct EhCleanupStep {
        cir::LifetimeId lifetime{};
        cir::EntityId variable{};
        cir::InstId landing_pad{};
        cir::BlockId pad_block{};
        cir::BlockId code_block{};
        cir::InstId destroy_inst{};
    };

    struct DestructorCleanupStep {
        RecordLifecycleStep lifecycle;
        cir::InstId landing_pad{};
        cir::BlockId pad_block{};
        cir::BlockId action_block{};
    };

    struct DestructorLifecycleRegion {
        bool active = false;
        cir::BlockId outer_unwind_target{};
        cir::BlockId body_unwind_target{};
        std::vector<DestructorCleanupStep> steps;
    };

    struct LifetimeObligation {
        cir::LifetimeId id{};
        cir::EntityId entity{};
        cir::TypeId type{};
        cir::EntityId cleanup_function{};
        SrcLoc loc{};
        LifetimeOwnerKind owner = LifetimeOwnerKind::LexicalScope;
        uint64_t owner_id = 0;
        bool requires_runtime_destroy = false;
    };

    struct NrvoReturnCandidate {
        cir::EntityId source{};
        cir::InstId transfer{};
        std::vector<cir::InstId> normal_cleanups;
    };

    enum class ControlKind : uint8_t {
        Loop,
        Switch,
        Expansion
    };

    struct ControlTargets {
        ControlKind kind = ControlKind::Loop;
        cir::BlockId continue_target{};
        cir::BlockId break_target{};
        bool observed_break = false;
        bool observed_continue = false;
    };

    struct SwitchCaseTarget {
        int64_t low = 0;
        int64_t high = 0;
        cir::BlockId target{};
        SrcLoc loc{};
    };

    struct SwitchContext {
        ExprResult condition;
        cir::BlockId dispatch_block{};
        cir::BlockId continuation_block{};
        cir::BlockId default_target{};
        std::vector<SwitchCaseTarget> cases;
        bool has_default = false;
        bool has_error = false;
        SrcLoc loc{};
        size_t control_depth_at_entry = 0;
        std::vector<uint64_t> control_flow_regions;
    };

    struct LabelReference {
        SrcLoc loc{};
        std::vector<uint64_t> control_flow_regions;
    };

    struct LabelInfo {
        std::string name;
        cir::BlockId block{};
        bool declared_local = false;
        bool defined = false;
        bool referenced = false;
        SrcLoc loc{};
        SrcLoc first_reference{};
        std::vector<uint64_t> control_flow_regions;
        std::vector<LabelReference> references;
    };

    struct DiscardedControlFlowEvent {
        enum class Kind : uint8_t {
            LabelDefinition,
            LabelReference
        };
        Kind kind = Kind::LabelReference;
        std::string name;
        SrcLoc loc{};
        cir::FunctionId function{};
        std::vector<uint64_t> control_flow_regions;
        bool declared_local = false;
    };

    using LabelMap = std::unordered_map<std::string, LabelInfo>;

    struct RecordLayoutInfo {
        std::vector<cir::RecordFieldFact> fields;
        size_t size_bits = 0;
        size_t alignment = 1;
        bool has_flexible_array_member = false;
        bool has_error = false;
    };

    struct FieldPathLookupResult {
        std::vector<cir::EntityId> entities;
        cir::TypeId type{};
        bool found = false;
        bool ambiguous = false;
    };

    struct RollbackAction {
        std::string label;
        std::function<void()> undo;
    };

    struct LambdaFrameRollbackState {
        size_t captures_size = 0;
        std::unordered_map<uint64_t, size_t> capture_memo;
        size_t this_capture = SIZE_MAX;
    };

    struct SpeculativeSnapshot {
        cir::File::TransactionId file_transaction = 0;
        cir::Builder::Checkpoint builder_checkpoint;
        uint64_t constraint_environment_revision = 0;
        size_t scopes_size = 0;
        ScopeId current_scope = InvalidScopeId;
        std::vector<ControlTargets> control_stack;
        size_t switch_stack_size = 0;
        size_t switch_contexts_size = 0;
        std::vector<uint64_t> control_flow_regions;
        size_t lambda_stack_size = 0;
        std::vector<LambdaFrameRollbackState> lambda_frame_states;
        size_t lambda_context_stack_size = 0;
        uint32_t anonymous_record_counter = 0;
        cir::Fragment current_prologue;
        cir::TypeId current_result_type{};
        cir::FunctionId current_function{};
        size_t unevaluated_operand_depth = 0;
        size_t typeid_capture_discovery_depth = 0;
        cir::EntityId default_argument_boundary_function{};
        uint32_t compound_literal_counter = 0;
        uint32_t global_init_counter = 0;
        size_t global_init_functions_size = 0;
        LabelMap function_labels;
        std::vector<LabelMap> local_label_scopes;
        std::vector<cir::BlockId> pending_orphan_label_blocks;
        std::vector<CleanupScope> cleanup_scopes;
        std::vector<EhCleanupStep> eh_cleanup_steps;
        DestructorLifecycleRegion destructor_lifecycle_region;
        std::vector<LifetimeObligation> lifetime_obligations;
        std::vector<uint64_t> active_lifetime_boundaries;
        std::vector<cir::DeclContextId> active_try_move_boundaries;
        std::vector<NrvoReturnCandidate> nrvo_return_candidates;
        bool nrvo_has_incompatible_return = false;
        uint32_t active_catch_handlers = 0;
        uint32_t active_constructor_function_try_handlers = 0;
        size_t discarded_statement_validation_depth = 0;
        size_t expansion_label_region_depth = 0;
        bool collecting_pattern = false;
        bool pattern_usable = true;
        uint64_t pattern_taint = 0;
        bool member_pattern_active = false;
        uint64_t member_pattern_taint_start = 0;
        size_t member_pattern_holes_start = 0;
        size_t member_pattern_events_start = 0;
        std::vector<PatternHole> pattern_holes;
        std::vector<PatternScopeEvent> pattern_events;
        std::vector<MemberPattern> pattern_members;
        std::unordered_set<uint64_t> pattern_holed_locals;
        std::unordered_set<std::string> function_parameter_pack_names;
        std::unordered_map<std::string,
                           std::vector<FunctionParameterPackElement>>
            function_parameter_pack_elements;
        std::unordered_map<std::string, uint32_t>
            function_parameter_pack_template_indices;
        std::vector<FunctionParameterPackScopeState>
            function_parameter_pack_scope_stack;
        size_t access_captures_size = 0;
        size_t active_access_captures_size = 0;
        std::vector<size_t> active_access_obligation_sizes;
        std::vector<RollbackAction> memo_rollbacks;
    };
    ScopeEnterResult enter_scope_impl(ScopeFlags flags,
                                      cir::EntityId owner = {},
                                      SrcLoc loc = SrcLoc());
    cir::DeclContextKind context_kind_for_scope_flags(ScopeFlags flags) const;
    void bump_lookup_generation();
    uint64_t current_point_lookup_generation() const;
    SrcLoc record_method_owner_point_loc(cir::EntityId method) const;
    uint64_t record_method_owner_point_lookup_generation(
        cir::EntityId method) const;
    uint64_t record_template_instantiation_request(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        uint64_t point_lookup_generation,
        TemplateInstantiationRequestKind kind);
    uint64_t record_template_instantiation_request_with_identity(
        const TemplateInfo& info,
        std::string memo_key,
        std::string display_name,
        SrcLoc loc,
        uint64_t point_lookup_generation,
        TemplateInstantiationRequestKind kind);
    const TemplateInstantiationRequest*
    template_instantiation_request_by_id(uint64_t request_id) const;
    size_t active_template_instantiation_request_depth() const;
    bool check_template_replay_guard_depth(SrcLoc loc);
    bool check_template_instantiation_request_depth(SrcLoc loc);
    void report_template_instantiation_depth_limit(SrcLoc loc);
    struct TemplateArgumentCompletionScope {
        bool active = false;
    };
    TemplateArgumentCompletionScope begin_template_argument_completion(
        const TemplateInfo& info,
        const TemplateArgumentBindings& bindings,
        SrcLoc loc,
        uint64_t point_lookup_generation);
    void finish_template_argument_completion(
        TemplateArgumentCompletionScope scope);
    std::string template_argument_identity_key(
        const TemplateArgument& argument) const;
    void append_template_argument_identity_key(
        std::string& key,
        const TemplateArgument& argument) const;
    std::string template_argument_display(
        const TemplateArgument& argument) const;
    std::string template_argument_completion_memo_key(
        const TemplateInfo& info,
        const TemplateArgumentBindings& bindings) const;
    std::string template_argument_completion_display(
        const TemplateInfo& info,
        const TemplateArgumentBindings& bindings) const;
    std::string template_argument_list_parsing_memo_key(
        const TemplateInfo& info,
        SrcLoc loc) const;
    std::string template_argument_list_parsing_display(
        const TemplateInfo& info) const;
    void mark_record_method_required_at(cir::EntityId method,
                                        SrcLoc loc,
                                        uint64_t lookup_generation);
    cir::EntityId class_template_member_pattern_entity(
        cir::EntityId member,
        const TemplateInfo& info) const;
    cir::InstId emit_construct_in_place(cir::InstId place,
                                        cir::EntityId constructor,
                                        const std::vector<cir::InstId>& args,
                                        SrcLoc loc = SrcLoc());
    cir::InstId emit_destroy(cir::InstId place,
                             cir::EntityId destructor = {},
                             SrcLoc loc = SrcLoc());
    cir::InstId emit_structor_call(cir::EntityId structor,
                                   cir::TypeId result_type,
                                   const std::vector<cir::InstId>& args,
                                   SrcLoc loc = SrcLoc());
    void mark_static_initializer_relocations_required(
        const std::vector<cir::StaticInitializerRelocation>& relocations,
        SrcLoc loc);
    uint64_t binding_entity_lookup_generation(const cir::Binding& binding,
                                              size_t index) const;
    bool binding_entity_visible_at_generation(const cir::Binding& binding,
                                              size_t index,
                                              uint64_t ceiling) const;
    uint64_t template_instantiation_point_generation(
        uint64_t point_lookup_generation) const;
    cir::EntityId bind_template_template_parameter_placeholder(
        const TemplateParameter& parameter,
        SrcLoc loc);
    void bind_template_instantiation_parameters(
        const TemplateInfo& info,
        const std::vector<TemplateArgument>& arguments,
        SrcLoc loc,
        const TemplateArgumentBindings* exact_bindings = nullptr);
    const cir::Binding* lookup_ordinary_binding(std::string_view name,
                                                bool include_parents = true) const;
    const cir::Binding* lookup_type_name_binding(std::string_view name,
                                                 bool include_parents = true) const;
    cir::TypeRef lookup_active_template_header_type_parameter(
        std::string_view name) const;
    cir::TypeRef lookup_record_scope_type_before_outer_template_parameters(
        std::string_view name,
        bool* found_name = nullptr) const;
    struct UnqualifiedQualifierLookup {
        const cir::Binding* binding = nullptr;
        cir::TypeRef type{};
        bool found_name = false;
    };
    UnqualifiedQualifierLookup lookup_unqualified_qualifier(
        std::string_view name) const;
    const cir::Binding* lookup_template_name_binding(
        std::string_view name,
        bool include_parents = true) const;
    const cir::Binding* lookup_tag_binding(std::string_view name,
                                           bool include_parents = true) const;
    bool namespace_lookup_reaches_context(
        cir::DeclContextId nominated,
        cir::DeclContextId target) const;
    void diagnose_template_parameter_hiding(std::string_view name,
                                            SrcLoc loc,
                                            cir::DeclContextId context);
    void register_function_default_arguments(
        cir::EntityId entity,
        const std::vector<ParamInput>& params,
        const cir::Binding* previous_binding,
        SrcLoc loc);
    cir::EntityId hidden_friend_class_template_entity(
        std::string_view name,
        const std::vector<TemplateParameter>& parameters,
        const std::vector<TemplateInfo::IntroducedConstraint>&
            introduced_constraints,
        cir::DeclContextId context) const;
    cir::EntityId hidden_friend_record_entity(
        std::string_view name,
        cir::DeclContextId context,
        cir::ModuleAttachmentId module_attachment = {}) const;
    cir::EntityId hidden_friend_function_template_entity(
        std::string_view name,
        const std::vector<TemplateParameter>& parameters,
        cir::TypeId pattern_type,
        const std::vector<TemplateInfo::IntroducedConstraint>&
            introduced_constraints,
        cir::DeclContextId context,
        cir::ModuleAttachmentId module_attachment = {},
        cir::EntityId signature_owner = {}) const;
    cir::EntityId friend_function_entity(std::string_view name,
                                         cir::TypeId type,
                                         cir::DeclContextId context,
                                         cir::ModuleAttachmentId
                                             module_attachment = {},
                                         cir::EntityId signature_owner = {}) const;
    cir::BindingId bind_entity(std::string_view name,
                               cir::LookupNamespace lookup_namespace,
                               cir::EntityId entity,
                               cir::TypeId type,
                               bool is_type_name = false,
                               bool is_template_name = false,
                               bool is_definition = false,
                               cir::InstId place = {},
                               SrcLoc loc = SrcLoc());
    TagLookupResult lookup_record_tag(std::string_view name,
                                      cir::RecordKind kind,
                                      TagLookupMode mode) const;
    RecordDeclResult create_record_tag(cir::RecordKind kind,
                                       std::string tag,
                                       SrcLoc loc,
                                       bool bind_tag = true);
    cir::TypeId make_aarch64_va_list_type();
    cir::TypeId make_x86_64_va_list_type();
    cir::TypeId create_enum_tag(std::string tag,
                                SrcLoc loc,
                                bool bind_tag = true,
                                bool is_definition = false,
                                cir::TypeRef underlying = {},
                                bool is_scoped = false,
                                bool has_fixed_underlying_type = false);
    std::string anonymous_record_name(cir::RecordKind kind);
    bool complete_anonymous_union_object(
        cir::TypeId union_type,
        cir::EntityId object,
        cir::AnonymousUnionObjectKind kind,
        cir::DeclContextId parent_context,
        SrcLoc loc);
    void bind_anonymous_union_promotions(
        cir::TypeId union_type,
        cir::InstId object_place,
        SrcLoc loc);
    RecordLayoutInfo compute_record_layout(cir::RecordKind kind,
                                           bool is_packed,
                                           size_t requested_alignment,
                                           size_t pack_alignment,
                                           const std::vector<cir::RecordFieldFact>& fields,
                                           SrcLoc loc);
    std::optional<std::pair<size_t, size_t>> size_align_of_type(cir::TypeId type, SrcLoc loc);
    std::optional<size_t> size_of_type(cir::TypeId type, SrcLoc loc);
    std::optional<size_t> align_of_type(cir::TypeId type, SrcLoc loc);
    const cir::RecordFieldFact* lookup_field(cir::TypeId record_type,
                                             std::string_view member_name) const;
    const cir::RecordStaticDataMemberFact* static_data_member_fact(
        cir::EntityId entity) const;
    bool is_namespace_scope_static_entity(cir::EntityId entity) const;
    // The [class.member.lookup] ABI invariant retains exact base-subobject paths
    // so repeated non-virtual bases remain distinct while virtual bases coalesce.
    using MemberLookupBaseStep = AccessBaseStep;

    struct MemberLookupDeclaration {
        cir::EntityId entity{};
        cir::TypeRef designated_type{};
        cir::TypeId declaring_class{};
        cir::TypeId implicit_object_class{};
        cir::EntityId access_owner{};
        cir::EntityId importing_class{};
        uint32_t using_fact_index =
            std::numeric_limits<uint32_t>::max();
        cir::RecordMemberAccess declared_access =
            cir::RecordMemberAccess::Public;
        bool has_declared_access = false;
        bool found_through_using = false;
        std::vector<std::vector<cir::EntityId>> object_paths;
        std::vector<std::vector<MemberLookupBaseStep>> base_paths;
        std::vector<cir::EntityId> member_path;
    };

    struct MemberLookupSubobject {
        cir::TypeId type{};
        std::vector<cir::EntityId> path;
    };

    struct MemberLookupResult {
        bool found_name = false;
        bool ambiguous = false;
        bool has_dependent_bases = false;
        std::vector<MemberLookupDeclaration> declarations;
        std::vector<MemberLookupSubobject> subobjects;
    };
    MemberLookupResult lookup_member_name(cir::TypeId record_type,
                                          std::string_view name,
                                          bool type_only = false) const;
    std::optional<cir::AllocationFunctionForm> classify_allocation_function(
        cir::EntityId entity,
        bool is_array) const;
    std::optional<cir::DeallocationFunctionForm>
    classify_deallocation_function(cir::EntityId entity,
                                   bool is_array) const;
    AllocationSelection select_allocation_function(
        cir::TypeId allocated_object_type,
        bool is_array,
        bool force_global,
        const std::vector<ExprResult>& arguments,
        SrcLoc loc,
        bool diagnose = true);
    DeallocationSelection select_deallocation_function(
        cir::TypeId deleted_object_type,
        bool is_array,
        bool force_global,
        bool placement_matching,
        const AllocationSelection* allocation,
        const std::vector<ExprResult>& placement_arguments,
        SrcLoc loc,
        bool diagnose = true,
        bool check_access = true);
    cir::EntityId implicit_allocation_operator(
        bool is_array,
        bool aligned,
        SrcLoc loc);
    cir::EntityId implicit_deallocation_operator(
        bool is_array,
        bool sized,
        bool aligned,
        SrcLoc loc);
    cir::InstId emit_deallocation_call(
        const DeallocationSelection& selection,
        cir::InstId pointer,
        cir::TypeId object_type,
        SrcLoc loc,
        cir::InstId explicit_size = {},
        const std::vector<cir::InstId>& placement_arguments = {});
    ExprResult collect_array_new_expr(NewExpressionInput input,
                                      SrcLoc loc);
    cir::Fragment dynamic_array_construct_fragment(
        cir::InstId leaf_pointer,
        cir::TypeId leaf_type,
        cir::InstId first,
        cir::InstId count,
        cir::InstId progress_place,
        SrcLoc loc,
        bool* had_error);
    cir::Fragment dynamic_array_zero_fragment(cir::InstId leaf_pointer,
                                              cir::TypeId leaf_type,
                                              cir::InstId first,
                                              cir::InstId count,
                                              SrcLoc loc);
    cir::Fragment dynamic_array_destroy_fragment(cir::InstId leaf_pointer,
                                                 cir::TypeId leaf_type,
                                                 cir::InstId count,
                                                 cir::InstId progress_place,
                                                 SrcLoc loc);
    std::vector<cir::EntityId> expand_function_template_candidates(
        const std::vector<cir::EntityId>& candidates,
        const std::vector<ExprResult>& arguments,
        SrcLoc loc);
    bool check_member_lookup_access(
        const MemberLookupDeclaration& declaration,
        SrcLoc loc,
        cir::TypeId designating_class = {});
    bool exact_class_friend_access_depends_on_current_instantiation(
        cir::EntityId member_owner) const;
    bool check_member_lookup_base_access(
        const MemberLookupDeclaration& declaration,
        cir::TypeId derived_type,
        SrcLoc loc);
    const MemberCandidateObjectPaths* member_candidate_paths_for_selected(
        const std::vector<MemberCandidateObjectPaths>& candidates,
        cir::EntityId selected) const;
    bool check_selected_member_candidate_access(
        const MemberCandidateObjectPaths& candidate,
        cir::EntityId selected,
        SrcLoc loc,
        cir::TypeId designating_class = {});
    FieldPathLookupResult lookup_field_path(cir::TypeId record_type,
                                            std::string_view member_name) const;
    cir::BlockId begin_fragment_block(std::string_view name);
    cir::Fragment finish_fragment_block(cir::BlockId block, cir::BlockId previous);
    cir::Fragment adopt_or_create_fragment_entry(cir::Fragment fragment, std::string_view name);
    StmtResult make_stmt_result(cir::Fragment fragment,
                                bool always_returns = false,
                                bool has_error = false) const;
    LabelInfo& function_label(std::string_view name, SrcLoc loc);
    LabelInfo* find_local_label(std::string_view name);
    LabelInfo& label_for_reference(std::string_view name, SrcLoc loc);
    LabelInfo& label_for_definition(std::string_view name, SrcLoc loc);
    void record_label_reference(LabelInfo& label,
                                std::string_view name,
                                SrcLoc loc);
    void validate_label_control_flow(const LabelInfo& label,
                                     const LabelReference& reference);
    void ensure_label_block(LabelInfo& label);
    void diagnose_unresolved_label(LabelInfo& label, SrcLoc fallback_loc);
    std::optional<int64_t> try_evaluate_asm_immediate(const ExprResult& expr) const;
    cir::TypeId object_type_from_place(cir::InstId place) const;
    cir::TypeId floating_literal_type(syntax::FloatingLiteralKind kind);
    cir::TypeId integer_literal_type(TokenType token_type,
                                     std::string_view spelling,
                                     uint64_t value);
    cir::TypeId character_literal_type(LiteralPrefix prefix);
    bool is_void_type(cir::TypeId type) const;
    bool is_nullptr_type(cir::TypeId type) const;
    bool is_bool_type(cir::TypeId type) const;
    bool is_integer_type(cir::TypeId type) const;
    bool is_scoped_enum_type(cir::TypeId type) const;
    bool is_floating_type(cir::TypeId type) const;
    bool is_arithmetic_type(cir::TypeId type) const;
    bool is_scalar_type(cir::TypeId type) const;
    bool is_pointer_type(cir::TypeId type) const;
    bool is_vector_type(cir::TypeId type) const;
    bool is_complex_type(cir::TypeId type) const;
    bool is_literal_type(cir::TypeId type) const;
    bool type_equal(cir::TypeId lhs, cir::TypeId rhs) const;
    cir::TypeId integer_promotion_type(cir::TypeId type) const;
    cir::TypeId bitfield_promoted_type(cir::TypeId declared_type,
                                       uint32_t bit_width) const;
    cir::TypeId default_argument_promotion_type(cir::TypeId type) const;
    cir::TypeId usual_arithmetic_conversion_type(cir::TypeId lhs,
                                                 cir::TypeId rhs) const;
    cir::TypeId unsigned_counterpart(cir::TypeId type) const;
    ExprResult cast_if_needed(ExprResult expr,
                              cir::TypeId type,
                              std::string_view cast_kind,
                              SrcLoc loc);
    ExprResult convert_to_arithmetic_type(ExprResult expr,
                                          cir::TypeId type,
                                          SrcLoc loc);
    ExprResult convert_to_condition(ExprResult expr, SrcLoc loc);
    ExprResult convert_nullptr_to_bool(ExprResult expr,
                                       cir::TypeId target_type,
                                       std::string_view reason,
                                       SrcLoc loc);
    ExprResult apply_default_argument_promotion(ExprResult expr, SrcLoc loc);
    ExprResult convert_call_argument_to_parameter(ExprResult expr,
                                                  cir::TypeId parameter_type,
                                                  SrcLoc loc);
    ExprResult collect_data_member_pointer_expr(syntax::BinaryOperator op,
                                                ExprResult lhs,
                                                ExprResult rhs,
                                                SrcLoc loc);
    ExprResult collect_vector_binary_expr(syntax::BinaryOperator op,
                                          ExprResult lhs,
                                          ExprResult rhs,
                                          SrcLoc loc);
    void diagnose_if_not_scalar(cir::TypeId type,
                                SrcLoc loc,
                                std::string_view context);
    void diagnose_if_not_arithmetic(cir::TypeId type,
                                    SrcLoc loc,
                                    std::string_view context);
    void diagnose_if_not_integer(cir::TypeId type,
                                 SrcLoc loc,
                                 std::string_view context);
    cir::UnaryOpKind unary_op_kind(syntax::UnaryOperator op) const;
    cir::BinaryOpKind binary_op_kind(syntax::BinaryOperator op) const;
    cir::TypeId binary_result_type(syntax::BinaryOperator op,
                                   cir::TypeId lhs,
                                   cir::TypeId rhs,
                                   SrcLoc loc);
    cir::TypeId binary_result_type(syntax::BinaryOperator op) const;
    bool is_aggregate_type(cir::TypeId type) const;
    bool list_initializes_aggregate_from_single_class_element(
        cir::TypeId target_type,
        const ExprResult& initializer) const;
    cir::TypeId aggregate_child_type(cir::TypeId type, size_t index, SrcLoc loc) const;

    struct InitPath {
        std::vector<size_t> indices;
        cir::TypeId target_type{};
    };
    bool diagnose_braced_narrowing(cir::TypeId target_type,
                                   const ExprResult& value,
                                   SrcLoc loc);
    bool try_evaluate_floating_constant(const ExprResult& expr,
                                        cir::FloatingValue& value);

    struct InitAssignment {
        std::vector<InitPath> paths;
        ExprResult value;
        SrcLoc loc{};
    };

    std::optional<std::vector<uint8_t>> string_literal_initializer_bytes(
        cir::TypeId type,
        const ExprResult& initializer,
        SrcLoc loc);
    InferredArrayBound infer_array_initializer_bound(
        cir::TypeId array_type,
        const ExprResult& initializer,
        SrcLoc loc);
    bool eval_integer_constant(const ExprResult& expr, int64_t& value, SrcLoc loc);
    bool eval_integer_constant(const ExprResult& expr,
                               int64_t& value,
                               SrcLoc loc,
                               std::string_view diagnostic);
    bool resolve_initializer_designators(const std::vector<InitDesignator>& designators,
                                         cir::TypeId base_type,
                                         std::vector<InitPath>& paths,
                                         size_t& outer_end,
                                         bool& has_range);
    void collect_init_assignments(cir::TypeId type,
                                  std::vector<InitElementInput>& elements,
                                  std::vector<InitAssignment>& assignments,
                                  std::vector<size_t> prefix,
                                  InitListSyntax syntax,
                                  SrcLoc loc);
    void collect_init_value_assignment(cir::TypeId target_type,
                                       ExprResult value,
                                       std::vector<InitPath> paths,
                                       std::vector<InitAssignment>& assignments,
                                       SrcLoc loc,
                                       InitListSyntax syntax =
                                           InitListSyntax::Braced);
    cir::Fragment emit_zero_initializer(cir::InstId place, cir::TypeId type, SrcLoc loc);
    bool aggregate_has_default_member_initializer(cir::TypeId type) const;
    cir::Fragment emit_initializer_for_place(cir::InstId place,
                                             cir::TypeId type,
                                             ExprResult initializer,
                                             SrcLoc loc,
                                             UseContext context =
                                                 UseContext::Init,
                                             const std::function<cir::InstId(
                                                 SrcLoc)>* action_place =
                                                 nullptr);
    cir::InstId place_for_init_path(cir::InstId base_place,
                                    cir::TypeId base_type,
                                    const std::vector<size_t>& path,
                                    SrcLoc loc,
                                    cir::Fragment& fragment);
    std::optional<std::vector<uint8_t>> static_initializer_bytes(cir::TypeId type,
                                                                 ExprResult initializer,
                                                                 SrcLoc loc,
                                                                 std::vector<cir::StaticInitializerRelocation>* relocations = nullptr);
    bool template_value_constant_from_static_bytes(cir::TypeId type,
                                                   const std::vector<uint8_t>& bytes,
                                                   size_t offset,
                                                   const std::vector<cir::StaticInitializerRelocation>* relocations,
                                                   TemplateValueConstant& value,
                                                   SrcLoc loc);
    bool template_value_constant_from_const_value(cir::TypeId type,
                                                  const ConstValue& constant,
                                                  TemplateValueConstant& value,
                                                  SrcLoc loc);
    bool validate_template_parameter_object_copy(cir::TypeId type,
                                                 const ExprResult& candidate,
                                                 const ConstValue& candidate_value,
                                                 SrcLoc loc);
    cir::EntityId materialize_template_parameter_object(
        cir::TypeId type,
        const TemplateArgument& argument,
        std::string_view parameter_name,
        SrcLoc loc);
    std::optional<std::vector<uint8_t>>
    template_argument_static_initializer_bytes(
        cir::TypeId type,
        const TemplateArgument& argument,
        SrcLoc loc,
        std::vector<cir::StaticInitializerRelocation>* relocations = nullptr);
    bool write_template_argument_static_value(
        std::vector<uint8_t>& bytes,
        size_t offset,
        cir::TypeId type,
        const TemplateArgument& argument,
        SrcLoc loc,
        std::vector<cir::StaticInitializerRelocation>* relocations = nullptr);
    bool write_member_pointer_static_value(
        std::vector<uint8_t>& bytes,
        size_t offset,
        cir::TypeId type,
        cir::EntityId member,
        int64_t data_member_offset,
        bool is_null,
        SrcLoc loc,
        std::vector<cir::StaticInitializerRelocation>* relocations = nullptr);
    bool write_static_zero(std::vector<uint8_t>& bytes,
                           size_t offset,
                           cir::TypeId type,
                           SrcLoc loc);
    bool write_static_value(std::vector<uint8_t>& bytes,
                            size_t offset,
                            cir::TypeId type,
                            const ExprResult& value,
                            SrcLoc loc,
                            std::vector<cir::StaticInitializerRelocation>* relocations = nullptr);
    bool write_static_path(std::vector<uint8_t>& bytes,
                           cir::TypeId base_type,
                           const std::vector<size_t>& path,
                           const ExprResult& value,
                           SrcLoc loc,
                           std::vector<cir::StaticInitializerRelocation>* relocations = nullptr);

    LangOptions lang_opts_;
    cir::File file_;
    cir::Builder builder_;
    std::shared_ptr<SourceManager> source_manager_;
    struct PendingWeakPragma {
        std::string alias;
        std::string target;
        SrcLoc loc{};
    };
    std::vector<PendingWeakPragma> pending_weak_pragmas_;
    bool try_apply_weak_pragma(std::string_view alias_name,
                               std::string_view target_name,
                               SrcLoc loc);
    struct DeferredIncompleteTentativeDef {
        cir::EntityId entity{};
        SrcLoc loc{};
    };
    std::vector<DeferredIncompleteTentativeDef>
        deferred_incomplete_tentative_defs_;
    void check_deferred_incomplete_tentative_defs();
    std::vector<ScopeFrame> scopes_;
    ScopeId current_scope_ = InvalidScopeId;
    cir::DeclContextId translation_unit_context_{};
    struct ModuleState {
        cir::ModuleAttachmentId unit{};
        bool seen_module_declaration = false;
        bool seen_private_fragment = false;
    };
    ModuleState module_state_;
    aburi::modules::ModuleLoader* module_loader_ = nullptr;
    ModuleUnitReplayCallback module_unit_replay_callback_;
    ModuleUnitRegisterCallback module_unit_register_callback_;
    std::vector<std::unique_ptr<std::vector<Token>>> imported_unit_tokens_;
    std::unordered_map<std::string, cir::ModuleAttachmentId> imported_units_;
    struct ModuleVisibilityFrame {
        cir::ModuleAttachmentId unit{};
        std::vector<uint32_t> visible_unit_indexes;
    };
    std::vector<ModuleVisibilityFrame> module_visibility_stack_;
    std::unordered_map<uint32_t, ModuleVisibilityFrame>
        unit_visibility_frames_;
    ModuleVisibilityFrame& active_module_visibility_frame();
    void sync_module_visibility();
    void make_module_unit_visible(cir::ModuleAttachmentId unit);
    cir::ModuleAttachmentId replay_imported_unit(
        const aburi::modules::LoadedModuleUnit& loaded, SrcLoc loc);
    uint64_t lookup_generation_ = 1;
    std::vector<bool> linkage_spec_stack_;
    std::vector<bool> linkage_spec_extern_storage_stack_;
    std::unordered_map<std::string, cir::EntityId> c_language_entities_;
    std::unordered_map<std::string, cir::EntityId> c_language_definitions_;
    void register_c_language_entity(cir::EntityId entity,
                                    std::string_view name,
                                    bool is_definition,
                                    SrcLoc loc);
    void mark_generated_abi_entity(cir::EntityId entity,
                                   cir::EntityId owner,
                                   cir::GeneratedSymbolRole role);
    cir::InstId current_this_place_{};
    cir::EntityId current_member_record_{};
    cir::TypeId member_declarator_this_type_{};
    bool member_declarator_this_active_ = false;
    cir::InstId current_complete_class_object_place_{};
    bool collecting_default_member_initializer_ = false;
    cir::EntityId member_access_function_override_{};
    std::unordered_map<uint64_t, cir::RecordMemberAccess>
        record_member_access_by_context_;
    std::vector<AccessCapture> access_captures_;
    std::vector<uint32_t> active_access_captures_;
    size_t template_argument_access_exemption_depth_ = 0;
    cir::InstId current_structor_flag_{};
    cir::InstId current_structor_vtt_place_{};
    std::unique_ptr<CoroutineState> coroutine_state_;
    CoroutinePromiseCallback coroutine_promise_callback_;
    CoroutineState* ensure_coroutine_context(std::string_view construct,
                                             SrcLoc loc);
    void diagnose_coroutine_codegen_gate(CoroutineState& coro, SrcLoc loc);
    void emit_coroutine_preamble(CoroutineState& coro, SrcLoc loc);
    ExprResult emit_await(CoroutineState& coro,
                          ExprResult awaitable,
                          cir::CoroSaveKind kind,
                          SrcLoc loc,
                          std::vector<cir::BlockId>* resume_blocks_out =
                              nullptr);
    ExprResult collect_promise_member_call(CoroutineState& coro,
                                           std::string_view member,
                                           std::vector<ExprResult> args,
                                           SrcLoc loc);
    void emit_coroutine_parameter_copies(CoroutineState& coro,
                                         cir::Fragment& body_fragment,
                                         SrcLoc loc);
    void emit_coroutine_promise_init(CoroutineState& coro, SrcLoc loc);
    ExprResult collect_coro_handle_builtin(BuiltinKind kind,
                                           std::vector<ExprResult> args,
                                           SrcLoc loc);
    StmtResult finish_coroutine_function(CoroutineState& coro,
                                         StmtResult body,
                                         SrcLoc loc);
    SrcLoc first_plain_return_loc_{};
    bool has_plain_return_ = false;
    std::unordered_map<std::string, cir::EntityId> runtime_functions_;
    std::unordered_map<std::string, cir::EntityId>
        implicit_allocation_functions_;
    std::unordered_map<uint64_t, cir::AllocationFunctionForm>
        implicit_allocation_forms_;
    std::unordered_map<uint64_t, cir::DeallocationFunctionForm>
        implicit_deallocation_forms_;
    std::unordered_map<std::string, cir::EntityId> vtable_thunks_;
    std::unordered_map<uint64_t, cir::EntityId> array_destroy_helpers_;
    std::unordered_map<uint64_t, std::vector<ParamInput::DefaultArgument>>
        function_default_arguments_;
    DefaultArgumentReplayCallback default_argument_replay_callback_;
    DefaultMemberInitializerReplayCallback
        default_member_initializer_replay_callback_;
    std::unordered_map<uint64_t, cir::EntityId> structor_complete_variants_;
    std::unordered_map<uint64_t, cir::EntityId> structor_base_variants_;
    std::unordered_map<uint64_t, cir::EntityId> structor_variant_impls_;
    std::unordered_map<std::string, cir::EntityId>
        inherited_variadic_call_constructors_;
    void suppress_entity_for_explicit_instantiation_declaration(
        cir::EntityId entity);
    void suppress_record_methods_for_explicit_instantiation_declaration(
        cir::EntityId record_entity);
    static constexpr size_t template_instantiation_depth_limit_ = 128;
    static constexpr size_t template_replay_guard_depth_limit_ = 64;
    size_t template_replay_guard_depth_ = 0;
    bool reported_instantiation_depth_limit_ = false;
    struct ActiveInstantiation {
        uint64_t template_entity_index = 0;
        SrcLoc point{};
        uint64_t point_lookup_generation = 0;
        uint64_t request_id = 0;
        std::string display_name;
        bool duplicate_request = false;
    };
    std::vector<ActiveInstantiation> active_instantiations_;
    bool in_template_definition_ = false;
    bool substitution_hard_error_ = false;
    TemplateReplayOutcome* template_replay_outcome_ = nullptr;
    bool binding_out_of_line_member_head_ = false;
    const TemplateInfo* validating_template_info_ = nullptr;
    std::vector<const TemplateInfo*> validating_template_info_stack_;
    bool collecting_pattern_ = false;
    bool pattern_usable_ = true;
    uint64_t pattern_taint_ = 0;
    uint64_t lookup_generation_ceiling_ = 0;
    std::vector<PatternScopeEvent> pattern_events_;
    bool member_pattern_active_ = false;
    MemberPattern current_member_pattern_;
    uint64_t member_pattern_taint_start_ = 0;
    size_t member_pattern_holes_start_ = 0;
    size_t member_pattern_events_start_ = 0;
    struct PatternCollectionState {
        bool collecting = false;
        bool usable = true;
        uint64_t taint = 0;
        std::vector<PatternHole> holes;
        std::vector<PatternScopeEvent> events;
        std::unordered_set<uint64_t> holed_locals;
        std::vector<MemberPattern> members;
        bool member_active = false;
        MemberPattern current_member;
        uint64_t member_taint_start = 0;
        size_t member_holes_start = 0;
        size_t member_events_start = 0;
    };
    std::vector<PatternCollectionState> pattern_collection_stack_;
    const TemplateInfo* active_template_header_info_ = nullptr;
    void populate_enclosing_instantiation_bindings(TemplateInfo& info);
    ExprResult function_parameter_pack_element_expr_result(
        std::string_view name,
        const FunctionParameterPackElement& element,
        SrcLoc loc);
    bool closure_field_pack_element(
        const FunctionParameterPackElement& element) const;
    ExprResult closure_field_pack_element_expr_result(
        std::string_view name,
        const FunctionParameterPackElement& element,
        SrcLoc loc);
    ExprResult value_parameter_pack_element_expr_result(
        std::string_view name,
        const TemplateArgument& argument,
        SrcLoc loc);
    struct TemplateState;
    std::unique_ptr<TemplateState> template_state_;
    TemplateState& tstate() { return *template_state_; }
    const TemplateState& tstate() const { return *template_state_; }
    std::vector<ControlTargets> control_stack_;
    std::vector<size_t> switch_stack_;
    std::vector<SwitchContext> switch_contexts_;
    std::vector<uint64_t> control_flow_regions_;
    size_t expansion_label_region_depth_ = 0;
    uint64_t next_control_flow_region_ = 1;
    LabelMap function_labels_;
    std::vector<LabelMap> local_label_scopes_;
    std::vector<cir::BlockId> pending_orphan_label_blocks_;
    uint32_t anonymous_record_counter_ = 0;
    cir::Fragment current_prologue_;
    cir::TypeId current_result_type_{};
    cir::FunctionId current_function_{};
    size_t local_static_counter_ = 0;
    size_t dead_branch_depth_ = 0;
    size_t discarded_statement_validation_depth_ = 0;
    std::vector<DiscardedControlFlowEvent> discarded_control_flow_events_;
    size_t decltype_operand_depth_ = 0;
    size_t unevaluated_operand_depth_ = 0;
    size_t typeid_capture_discovery_depth_ = 0;
    cir::InstId vla_sp_slot_place_{};
    uint32_t compound_literal_counter_ = 0;
    uint32_t source_location_counter_ = 0;
    uint32_t global_init_counter_ = 0;
    std::vector<cir::EntityId> global_init_functions_;
    std::unordered_map<uint64_t, cir::EntityId> thread_init_functions_;
    uint32_t block_literal_counter_ = 0;
    bool deduce_return_type_ = false;
public:
    struct CoroutineState {
        cir::TypeId traits_specialization{};
        cir::TypeId promise_type{};
        cir::TypeId handle_type{};
        SrcLoc first_keyword_loc{};
        bool discovery_failed = false;
        bool codegen_gate_diagnosed = false;
        bool has_return_void = false;
        bool has_return_value = false;
        bool has_await_transform = false;
        bool has_get_return_object_on_allocation_failure = false;
        cir::Fragment preamble_fragment;
        cir::InstId frame_pointer{};
        cir::InstId promise_place{};
        struct PromiseCtorArg {
            cir::InstId place{};
            cir::TypeId type{};
            bool is_reference = false;
        };
        std::vector<PromiseCtorArg> promise_ctor_args;
        bool promise_ctor_args_complete = true;
        cir::InstId object_param_place{};
        cir::TypeId object_param_type{};
        uint32_t next_user_suspend_index = 2;
        struct ParameterCopy {
            cir::InstId place{};
            cir::TypeId type{};
        };
        std::vector<ParameterCopy> parameter_copies;
        cir::BlockId alloc_failure_block{};
        cir::BlockId final_suspend_block{};
        cir::BlockId cleanup_block{};
        bool emission_failed = false;
    };

    enum class LambdaCaptureKind : uint8_t {
        Entity,
        Init,
        ThisPointer,
        ThisObject,
    };
    struct LambdaCapture {
        LambdaCaptureKind kind = LambdaCaptureKind::Entity;
        cir::EntityId source_entity{};
        cir::EntityId field_entity{};
        cir::TypeId field_type{};
        bool by_ref = false;
        SrcLoc loc{};
        cir::Fragment init_fragment;
        cir::InstId init_value{};
        cir::InstId init_place{};
        std::vector<cir::LifetimeId> init_lifetimes;
    };
    struct LambdaFrame {
        cir::EntityId closure_record{};
        cir::EntityId call_operator{};
        cir::EntityId capture_origin_function{};
        uint32_t entity_watermark = 0;
        bool is_mutable = false;
        LambdaCaptureDefault capture_default = LambdaCaptureDefault::None;
        std::vector<LambdaCapture> captures;
        std::unordered_map<uint64_t, size_t> capture_memo;
        size_t this_capture = SIZE_MAX;
        cir::InstId enclosing_this_place{};
        cir::EntityId enclosing_member_record{};
        uint32_t closure_index = 0;
    };

    struct BlockContextState {
        cir::FunctionId function{};
        cir::TypeId result_type{};
        size_t decltype_operand_depth = 0;
        size_t unevaluated_operand_depth = 0;
        size_t typeid_capture_discovery_depth = 0;
        cir::Fragment prologue;
        LabelMap labels;
        std::vector<LabelMap> local_label_scopes;
        std::vector<cir::BlockId> orphan_blocks;
        cir::InstId vla_slot{};
        std::vector<ControlTargets> control_stack;
        std::vector<SwitchContext> switch_contexts;
        std::vector<uint64_t> control_flow_regions;
        std::vector<CleanupScope> cleanup_scopes;
        std::vector<EhCleanupStep> eh_cleanup_steps;
        DestructorLifecycleRegion destructor_lifecycle_region;
        std::vector<uint64_t> active_lifetime_boundaries;
        std::vector<cir::DeclContextId> active_try_move_boundaries;
        std::vector<NrvoReturnCandidate> nrvo_return_candidates;
        bool nrvo_has_incompatible_return = false;
        uint32_t active_catch_handlers = 0;
        uint32_t active_constructor_function_try_handlers = 0;
        std::unordered_map<uint32_t, cir::BlockId> eh_code_targets;
        std::vector<cir::InstId> eh_pads_in_flight;
        bool deduce_return = false;
        cir::InstId this_place{};
        cir::EntityId member_record{};
        cir::TypeId member_declarator_this_type{};
        bool member_declarator_this_active = false;
        cir::InstId complete_class_object_place{};
        bool collecting_default_member_initializer = false;
        cir::InstId structor_flag{};
        cir::InstId structor_vtt_place{};
        std::unique_ptr<CoroutineState> coroutine_state;
        SrcLoc first_plain_return_loc{};
        bool has_plain_return = false;
        bool suspended_lambda_context = false;
        std::vector<LambdaFrame> lambda_frames;
        cir::Builder::Checkpoint builder_checkpoint;
    };
private:
    std::vector<std::unique_ptr<BlockContextState>> block_context_stack_;
    std::vector<LambdaFrame> lambda_stack_;
    std::vector<std::unique_ptr<BlockContextState>> lambda_context_stack_;
    struct ActiveClosureAbiContext {
        cir::ClosureAbiContextKind kind =
            cir::ClosureAbiContextKind::TranslationUnit;
        cir::NameId name{};
        cir::DeclContextId declaration_context{};
    };
    std::vector<ActiveClosureAbiContext> closure_abi_context_stack_;
    uint32_t lambda_closure_counter_ = 0;
    int default_argument_replay_depth_ = 0;
    cir::EntityId default_argument_boundary_function_{};
    size_t add_lambda_capture(cir::EntityId source,
                              bool by_ref,
                              SrcLoc loc);
    size_t add_lambda_this_capture(bool object, bool implicit, SrcLoc loc);
    ExprResult lambda_capture_access(ExprResult result,
                                     std::string_view name,
                                     SrcLoc loc);
    ExprResult lambda_enclosing_this_value(SrcLoc loc);
    cir::InstId lambda_capture_source_place(const LambdaCapture& capture,
                                            SrcLoc loc);
    void register_explicit_lambda_captures(
        LambdaClosureStart& start,
        std::vector<LambdaCaptureItem> explicit_captures,
        SrcLoc loc);
    void publish_lambda_closure(LambdaClosureStart& start,
                                const LambdaFrame& frame,
                                std::vector<RecordMethodInput> extra_methods,
                                SrcLoc loc);
    ExprResult materialize_lambda_closure(const LambdaClosureStart& start,
                                          LambdaFrame& frame,
                                          SrcLoc loc);
    cir::TypeId lambda_invoker_function_type(cir::TypeId method_type);
    cir::EntityId synthesize_lambda_invoker(cir::TypeId closure_type,
                                            cir::EntityId call_operator,
                                            cir::TypeId declared_fn_type,
                                            const std::string& name,
                                            SrcLoc loc);
    void finalize_variable_initializer_closure_linkage(
        cir::EntityId variable);
    ExprResult convert_generic_lambda_to_function_pointer(ExprResult expr,
                                                          cir::TypeId target_type,
                                                          bool* handled,
                                                          SrcLoc loc);
    std::unordered_map<uint64_t, cir::EntityId> lambda_invoker_memo_;

public:
    std::unique_ptr<BlockContextState> save_function_context(
        bool preserve_lambda_context = false);
    void restore_function_context(std::unique_ptr<BlockContextState> saved);

private:
    cir::EntityId extern_runtime_function(std::string_view symbol,
                                          cir::TypeId function_type,
                                          SrcLoc loc);
    cir::EntityId synthesize_block_helper(
        std::string_view name,
        bool has_destination,
        const std::function<void(cir::InstId destination, cir::InstId source)>&
            emit_body,
        SrcLoc loc);
    struct ByrefCellInfo {
        cir::EntityId cell_entity{};
        cir::TypeId cell_record{};
        cir::InstId cell_place{};
        bool wants_helpers = false;
    };
    bool make_block_byref_access(cir::EntityId entity,
                                 ExprResult& result,
                                 SrcLoc loc);
    std::unordered_map<uint64_t, ByrefCellInfo> block_byref_cells_;
    std::unordered_map<std::string, cir::EntityId> runtime_globals_;
    std::unordered_map<std::string, cir::EntityId> typeinfo_entities_;
    cir::TypeId block_header_record_{};
    cir::TypeId block_descriptor_record_{};
    cir::TypeId block_descriptor_helpers_record_{};
    std::vector<CleanupScope> cleanup_scopes_;
    std::vector<LifetimeObligation> lifetime_obligations_{1};
    uint32_t next_lifetime_generation_ = 1;
    uint64_t next_lifetime_boundary_id_ = 1;
    std::vector<uint64_t> active_lifetime_boundaries_;
    std::vector<ArcPendingRelease> arc_pending_releases_;
    uint64_t arc_pending_next_token_ = 1;
    std::vector<EhCleanupStep> eh_cleanup_steps_;
    DestructorLifecycleRegion current_destructor_lifecycle_region_;
    std::unordered_map<uint32_t, cir::BlockId> eh_code_targets_;
    std::vector<cir::InstId> eh_pads_in_flight_;
    std::vector<cir::DeclContextId> active_try_move_boundaries_;
    std::vector<NrvoReturnCandidate> nrvo_return_candidates_;
    bool nrvo_has_incompatible_return_ = false;
    uint32_t active_catch_handlers_ = 0;
    uint32_t active_constructor_function_try_handlers_ = 0;
    void begin_noexcept_body_region(cir::TypeId fn_type, SrcLoc loc);
    void emit_unwind_continue(cir::BlockId from,
                              cir::InstId exn,
                              cir::InstId sel,
                              cir::BlockId enclosing_pad,
                              SrcLoc loc);
    void register_cleanup_attr(cir::EntityId entity,
                               cir::TypeId type,
                               const AttributeList& attrs,
                               SrcLoc loc);
    cir::Fragment emit_cleanup_calls_from_depth(
        size_t min_control_depth,
        SrcLoc loc,
        cir::EntityId nrvo_candidate = {},
        std::vector<cir::InstId>* nrvo_cleanups = nullptr);
    cir::Fragment emit_normal_cleanup_records(
        const std::vector<CleanupRecord>& records,
        SrcLoc loc,
        cir::EntityId nrvo_candidate = {},
        std::vector<cir::InstId>* nrvo_cleanups = nullptr);
    void install_subobject_rollback(
        const RecordLifecycleStep& step,
        SrcLoc loc,
        const std::function<cir::InstId(SrcLoc)>& action_place);
    void begin_destructor_lifecycle_region(SrcLoc loc);
    void finalize_nrvo_for_current_function();
    void emit_active_catch_ends(SrcLoc loc);
    void note_local_lifetime_start(cir::EntityId entity,
                                   cir::TypeId type,
                                   cir::InstId place,
                                   const DeclFlags& flags,
                                   SrcLoc loc);
    void suppress_open_scope_lifetimes();
    size_t statement_expr_depth_ = 0;
    std::vector<std::string> pragma_visibility_stack_;
    void declare_sve_builtin_types();
    void apply_pragma_visibility_default(cir::EntityId entity);
    std::unordered_map<uint64_t, cir::EntityId> string_literal_entities_;
    uint32_t string_entity_counter_ = 0;
    std::vector<SrcLoc> default_argument_call_sites_;
    std::vector<SpeculativeSnapshot> speculative_snapshots_;
};

// Attributes accumulate across redeclarations: the union of every declaration
// applies to the entity, so callers merging a prior declaration's facts use
// this rather than overwriting.
void merge_entity_attribute_facts(cir::EntityAttributeFacts& into,
                                  const cir::EntityAttributeFacts& from);

cir::File collect_translation_unit(const syntax::Tree& tree,
                                     const std::vector<Token>& tokens,
                                     const LangOptions& lang_opts);

} // namespace aburi::collect

#endif // ABURI_COLLECT_COLLECT_H
