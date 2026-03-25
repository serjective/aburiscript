#ifndef ABURI_LOOKUP_ENGINE_H
#define ABURI_LOOKUP_ENGINE_H

#include <memory>
#include <string>
#include <vector>
#include "decl_context.h"
#include "../ast/symbols.h"

class LookupEngine {
public:
    struct LookupTrace {
        std::vector<std::string> steps;

        void add_step(std::string step) { steps.push_back(std::move(step)); }
    };

    enum class OrdinaryFilter : uint8_t {
        Any,
        TypedefOnly
    };

    enum class NamespaceReachability : uint8_t {
        DirectOnly,
        InlineVisible,
        FullyVisible
    };

    enum class QualifiedLookupStatus : uint8_t {
        Found,
        NotFound,
        Unsupported
    };

    struct QualifiedLookupResult {
        QualifiedLookupStatus status = QualifiedLookupStatus::NotFound;
        const DeclBinding* binding = nullptr;
        std::shared_ptr<Symbol> symbol = nullptr;
        std::shared_ptr<DeclBinding> owned_binding = nullptr;
        std::string unsupported_reason;
    };

    struct QualifiedNameSpec {
        bool has_global_qualifier = false;
        std::vector<std::string> qualifiers;
        std::string terminal_name;
    };

    struct QualifiedOrdinaryBindingMatch {
        const DeclBinding* binding = nullptr;
        const DeclContext* owner_context = nullptr;
        std::shared_ptr<Scope> owner_scope = nullptr;
    };

    struct LookupEnvironmentFrame {
        std::shared_ptr<Scope> scope;
        const DeclContext* decl_context = nullptr;
        uint64_t lookup_position = 0;
        size_t scope_depth = 0;
    };

    struct LookupEnvironment {
        std::vector<LookupEnvironmentFrame> frames;

        bool empty() const { return frames.empty(); }
    };

    static LookupEnvironment build_unqualified_environment(
        const std::shared_ptr<Scope>& start_scope,
        bool look_parents,
        LookupTrace* trace = nullptr);

    static std::shared_ptr<Symbol> lookup_unqualified_ordinary(
        const std::string& name,
        const std::shared_ptr<Scope>& start_scope,
        bool look_parents,
        OrdinaryFilter filter = OrdinaryFilter::Any,
        LookupTrace* trace = nullptr);

    static const DeclBinding* lookup_unqualified_template_binding(
        const std::string& name,
        const std::shared_ptr<Scope>& start_scope,
        bool look_parents,
        LookupNamespace lookup_namespace,
        LookupTrace* trace = nullptr);

    static std::vector<QualifiedOrdinaryBindingMatch>
    lookup_qualified_ordinary_bindings(
        const std::string& name,
        const DeclContext* start_decl_context,
        const std::shared_ptr<Scope>& start_scope = nullptr,
        OrdinaryFilter filter = OrdinaryFilter::Any,
        NamespaceReachability reachability =
            NamespaceReachability::FullyVisible);

    static QualifiedLookupResult lookup_qualified(
        const std::string& name,
        const DeclContext* start_decl_context,
        LookupNamespace lookup_namespace = LookupNamespace::Ordinary,
        OrdinaryFilter filter = OrdinaryFilter::Any);

    static QualifiedLookupResult lookup_qualified_name(
        const QualifiedNameSpec& name_spec,
        const DeclContext* start_decl_context,
        LookupNamespace lookup_namespace = LookupNamespace::Ordinary,
        OrdinaryFilter filter = OrdinaryFilter::Any);

    static std::vector<std::shared_ptr<Symbol>> lookup_unqualified_function_candidates(
        const std::string& name,
        const std::shared_ptr<Scope>& start_scope,
        bool look_parents,
        LookupTrace* trace = nullptr);

    static TagDecl* lookup_tag_decl(const std::string& tag,
                                    const std::shared_ptr<Scope>& start_scope,
                                    bool look_parents,
                                    LookupTrace* trace = nullptr);

    static std::shared_ptr<CType> lookup_tag_type(const std::string& tag,
                                                  const std::shared_ptr<Scope>& start_scope,
                                                  bool look_parents,
                                                  LookupTrace* trace = nullptr);

    static bool lookup_label(const std::string& label,
                             const std::shared_ptr<Scope>& start_scope,
                             bool look_parents,
                             LookupTrace* trace = nullptr);
};

#endif // ABURI_LOOKUP_ENGINE_H
