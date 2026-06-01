#ifndef ABURI_PARSER_ANNOTATION_STORE_H
#define ABURI_PARSER_ANNOTATION_STORE_H

#include "tentative_syntax_probe.h"

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

class ParserAnnotationStore {
public:
    enum class ResultKind : uint8_t {
        TypeName,
        Declarator,
        CxxConstrainedPlaceholder,
        CppQualifiedIdStart,
        CppQualifiedDeclarator,
        CppTemplateNameArgumentPrefix,
        ParenthesizedTypeName,
        Count
    };

    enum class SemanticKind : uint8_t {
        CppNamedTypeSpecifierLookahead,
        CppTypeConstructionClassification,
        CppScope,
        CppTemplateId,
        Count
    };

    struct SemanticKey {
        uint32_t syntax_key = 0;
        uint64_t lookup_generation = 0;
        const void* scope = nullptr;
        const void* decl_context = nullptr;

        bool operator==(const SemanticKey& other) const {
            return syntax_key == other.syntax_key &&
                   lookup_generation == other.lookup_generation &&
                   scope == other.scope &&
                   decl_context == other.decl_context;
        }
    };

    enum class AnnotationKind : uint8_t {
        SyntaxResult,
        Semantic,
        TemplateId,
        QualifiedId,
        TemplateArgument,
        ParenthesizedTypeId,
        DeclaratorParenSuffix,
        QualifiedDeclaratorPrefix,
        TypeScope,
        TemplateArgumentListScan,
        TypeConstructionScan,
        ParameterClauseShape,
        Count
    };

    struct AnnotationHandle {
        size_t token_idx = 0;
        AnnotationKind kind = AnnotationKind::SyntaxResult;
        uint8_t context = 0;
        bool valid = false;

        explicit operator bool() const {
            return valid;
        }
    };

    struct AnnotationHeader {
        AnnotationHandle handle;
        size_t start_token_idx = 0;
        size_t end_token_idx = 0;
        size_t terminal_token_idx = 0;
        uint32_t syntax_key = 0;
        SemanticKey semantic_key;
        bool uses_semantic_key = false;
        bool dependent_or_ambiguous = false;

        explicit operator bool() const {
            return static_cast<bool>(handle);
        }
    };

    struct SemanticAnnotation {
        size_t end_token_idx = 0;
        uint8_t value = 0;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CppTemplateIdKind : uint8_t {
        NoMatch,
        NoTemplate,
        TypeTemplateId,
        NonTypeTemplateId,
        TemplateName,
        DependentOrAmbiguous,
        Inconclusive
    };

    struct CppTemplateIdAnnotation {
        size_t end_token_idx = 0;
        size_t terminal_identifier_token_idx = 0;
        size_t terminal_template_argument_list_begin_token_idx = 0;
        size_t terminal_template_argument_list_end_token_idx = 0;
        const void* resolved_template = nullptr;
        CppTemplateIdKind kind = CppTemplateIdKind::NoMatch;
        bool has_global_qualifier = false;
        bool has_scope = false;
        bool has_any_template_argument_list = false;
        bool terminal_has_template_argument_list = false;
        bool terminal_preceded_by_template_keyword = false;
        bool plain_qualified_name = false;
        bool at_template_argument_boundary = false;
        bool followed_by_ellipsis = false;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CppQualifiedIdKind : uint8_t {
        NoMatch,
        QualifiedId,
        Inconclusive,
        Error
    };

    struct CppQualifiedIdAnnotation {
        size_t end_token_idx = 0;
        size_t terminal_token_idx = 0;
        uint16_t component_count = 0;
        CppQualifiedIdKind kind = CppQualifiedIdKind::NoMatch;
        bool has_global_qualifier = false;
        bool has_scope = false;
        bool starts_with_decltype = false;
        bool has_template_id_component = false;
        bool terminal_preceded_by_template_keyword = false;
        bool terminal_is_operator_id = false;
        bool followed_by_left_paren = false;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CppTemplateArgumentKind : uint8_t {
        NoMatch,
        Type,
        TemplateName,
        Expression,
        TypedBraced,
        DependentOrAmbiguous,
        Inconclusive,
        Error
    };

    struct CppTemplateArgumentAnnotation {
        size_t end_token_idx = 0;
        CppTemplateArgumentKind kind = CppTemplateArgumentKind::NoMatch;
        bool followed_by_ellipsis = false;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CxxParenthesizedTypeIdKind : uint8_t {
        NoMatch,
        TypeId,
        Inconclusive,
        Error
    };

    struct CxxParenthesizedTypeIdAnnotation {
        size_t close_token_idx = 0;
        size_t end_token_idx = 0;
        CxxParenthesizedTypeIdKind kind =
            CxxParenthesizedTypeIdKind::NoMatch;
        bool followed_by_cast_operand = false;
        bool followed_by_left_brace = false;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CxxDeclaratorParenSuffixKind : uint8_t {
        NoMatch,
        EmptyParameterClause,
        EllipsisParameterClause,
        DefiniteParameterClause,
        DefiniteDirectInitializer,
        Ambiguous,
        Inconclusive,
        Error
    };

    struct CxxDeclaratorParenSuffixAnnotation {
        size_t end_token_idx = 0;
        CxxDeclaratorParenSuffixKind kind =
            CxxDeclaratorParenSuffixKind::NoMatch;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CppQualifiedDeclaratorPrefixKind : uint8_t {
        NoMatch,
        QualifiedDeclarator,
        Inconclusive,
        Error
    };

    struct CppQualifiedDeclaratorPrefixAnnotation {
        size_t end_token_idx = 0;
        CppQualifiedDeclaratorPrefixKind kind =
            CppQualifiedDeclaratorPrefixKind::NoMatch;
        bool has_global_qualifier = false;
        bool has_template_id_component = false;
        bool terminal_is_operator_id = false;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    enum class CppTypeScopeContext : uint8_t {
        DeclSpecifier,
        TemplateArgument,
        TypeConstruction,
        QualifiedDeclarator,
        Constraint,
        TypeRequirement,
        TypeId,
        DeclaratorParameter,
        Count
    };

    enum class CppTypeScopeKind : uint8_t {
        NoMatch,
        NonType,
        TypeName,
        TypeTemplateId,
        ScopeOnly,
        DependentType,
        DependentScope,
        PlaceholderConstraint,
        Inconclusive,
        Error
    };

    struct CppTypeScopeAnnotation {
        size_t end_token_idx = 0;
        size_t terminal_token_idx = 0;
        const void* resolved_type = nullptr;
        const void* typedef_symbol = nullptr;
        const void* resolved_template = nullptr;
        CppTypeScopeKind kind = CppTypeScopeKind::NoMatch;
        bool has_global_qualifier = false;
        bool has_scope = false;
        bool has_template_id = false;
        bool starts_with_typename = false;
        bool starts_with_decltype = false;
        bool dependent_or_ambiguous = false;
        AnnotationHeader annotation;
    };

    ParserAnnotationStore() = default;
    explicit ParserAnnotationStore(size_t token_count) {
        reset(token_count);
    }

    void reset(size_t token_count) {
        slots_.clear();
        slots_.resize(token_count);
    }

    static uint32_t make_config_key(const tentative_syntax_probe::Config& cfg) {
        uint32_t key = 0;
        if (cfg.cxx_mode) {
            key |= 1u << 0;
        }
        if (cfg.blocks_enabled) {
            key |= 1u << 1;
        }
        return key;
    }

    static AnnotationHeader make_syntax_header(size_t token_idx,
                                               AnnotationKind kind,
                                               uint32_t key,
                                               size_t end_token_idx,
                                               size_t terminal_token_idx,
                                               bool dependent_or_ambiguous,
                                               uint8_t context = 0) {
        AnnotationHeader header;
        header.handle = AnnotationHandle{token_idx, kind, context, true};
        header.start_token_idx = token_idx;
        header.end_token_idx = end_token_idx;
        header.terminal_token_idx = terminal_token_idx;
        header.syntax_key = key;
        header.uses_semantic_key = false;
        header.dependent_or_ambiguous = dependent_or_ambiguous;
        return header;
    }

    static AnnotationHeader make_semantic_header(size_t token_idx,
                                                 AnnotationKind kind,
                                                 const SemanticKey& key,
                                                 size_t end_token_idx,
                                                 size_t terminal_token_idx,
                                                 bool dependent_or_ambiguous,
                                                 uint8_t context = 0) {
        AnnotationHeader header;
        header.handle = AnnotationHandle{token_idx, kind, context, true};
        header.start_token_idx = token_idx;
        header.end_token_idx = end_token_idx;
        header.terminal_token_idx = terminal_token_idx;
        header.semantic_key = key;
        header.uses_semantic_key = true;
        header.dependent_or_ambiguous = dependent_or_ambiguous;
        return header;
    }

    std::optional<tentative_syntax_probe::Result>
    lookup_result(size_t token_idx, ResultKind kind, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->results[static_cast<size_t>(kind)];
        if (!entry.valid || entry.key != key) {
            return std::nullopt;
        }
        return entry.value;
    }

    void store_result(size_t token_idx,
                      ResultKind kind,
                      uint32_t key,
                      tentative_syntax_probe::Result value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        auto& entry = slot->results[static_cast<size_t>(kind)];
        entry.valid = true;
        entry.key = key;
        entry.value = value;
    }

    std::optional<tentative_syntax_probe::TemplateArgumentListScan>
    lookup_template_argument_list_scan(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot || !slot->template_argument_list_scan.valid ||
            slot->template_argument_list_scan.key != key) {
            return std::nullopt;
        }
        return slot->template_argument_list_scan.value;
    }

    void store_template_argument_list_scan(
        size_t token_idx,
        uint32_t key,
        tentative_syntax_probe::TemplateArgumentListScan value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        slot->template_argument_list_scan.valid = true;
        slot->template_argument_list_scan.key = key;
        slot->template_argument_list_scan.value = value;
    }

    std::optional<tentative_syntax_probe::CxxTypeConstructionScan>
    lookup_type_construction_scan(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot || !slot->type_construction_scan.valid ||
            slot->type_construction_scan.key != key) {
            return std::nullopt;
        }
        return slot->type_construction_scan.value;
    }

    void store_type_construction_scan(
        size_t token_idx,
        uint32_t key,
        tentative_syntax_probe::CxxTypeConstructionScan value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        slot->type_construction_scan.valid = true;
        slot->type_construction_scan.key = key;
        slot->type_construction_scan.value = value;
    }

    std::optional<tentative_syntax_probe::CxxParameterClauseShape>
    lookup_parameter_clause_shape(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot || !slot->parameter_clause_shape.valid ||
            slot->parameter_clause_shape.key != key) {
            return std::nullopt;
        }
        return slot->parameter_clause_shape.value;
    }

    void store_parameter_clause_shape(
        size_t token_idx,
        uint32_t key,
        tentative_syntax_probe::CxxParameterClauseShape value) {
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return;
        }
        slot->parameter_clause_shape.valid = true;
        slot->parameter_clause_shape.key = key;
        slot->parameter_clause_shape.value = value;
    }

    std::optional<SemanticAnnotation>
    lookup_semantic_annotation(size_t token_idx,
                               SemanticKind kind,
                               const SemanticKey& key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry =
            slot->semantic[static_cast<size_t>(kind)];
        if (!entry.valid || !(entry.key == key)) {
            return std::nullopt;
        }
        return entry.value;
    }

    SemanticAnnotation store_semantic_annotation(size_t token_idx,
                                                 SemanticKind kind,
                                                 const SemanticKey& key,
                                                 SemanticAnnotation value) {
        value.annotation = make_semantic_header(
            token_idx,
            AnnotationKind::Semantic,
            key,
            value.end_token_idx,
            value.end_token_idx,
            value.dependent_or_ambiguous,
            static_cast<uint8_t>(kind));
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->semantic[static_cast<size_t>(kind)];
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CppTemplateIdAnnotation>
    lookup_cpp_template_id_annotation(size_t token_idx,
                                      const SemanticKey& key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->cpp_template_id;
        if (!entry.valid || !(entry.key == key)) {
            return std::nullopt;
        }
        return entry.value;
    }

    CppTemplateIdAnnotation
    store_cpp_template_id_annotation(size_t token_idx,
                                     const SemanticKey& key,
                                     CppTemplateIdAnnotation value) {
        value.annotation = make_semantic_header(
            token_idx,
            AnnotationKind::TemplateId,
            key,
            value.end_token_idx,
            value.terminal_identifier_token_idx,
            value.dependent_or_ambiguous);
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cpp_template_id;
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CppQualifiedIdAnnotation>
    lookup_cpp_qualified_id_annotation(size_t token_idx, uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->cpp_qualified_id;
        if (!entry.valid || entry.key != key) {
            return std::nullopt;
        }
        return entry.value;
    }

    CppQualifiedIdAnnotation
    store_cpp_qualified_id_annotation(size_t token_idx,
                                      uint32_t key,
                                      CppQualifiedIdAnnotation value) {
        value.annotation = make_syntax_header(
            token_idx,
            AnnotationKind::QualifiedId,
            key,
            value.end_token_idx,
            value.terminal_token_idx,
            value.dependent_or_ambiguous);
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cpp_qualified_id;
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CppTemplateArgumentAnnotation>
    lookup_cpp_template_argument_annotation(size_t token_idx,
                                            const SemanticKey& key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->cpp_template_argument;
        if (!entry.valid || !(entry.key == key)) {
            return std::nullopt;
        }
        return entry.value;
    }

    CppTemplateArgumentAnnotation store_cpp_template_argument_annotation(
        size_t token_idx,
        const SemanticKey& key,
        CppTemplateArgumentAnnotation value) {
        value.annotation = make_semantic_header(
            token_idx,
            AnnotationKind::TemplateArgument,
            key,
            value.end_token_idx,
            value.end_token_idx,
            value.dependent_or_ambiguous);
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cpp_template_argument;
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CxxParenthesizedTypeIdAnnotation>
    lookup_cxx_parenthesized_type_id_annotation(
        size_t token_idx,
        const SemanticKey& key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->cxx_parenthesized_type_id;
        if (!entry.valid || !(entry.key == key)) {
            return std::nullopt;
        }
        return entry.value;
    }

    CxxParenthesizedTypeIdAnnotation
    store_cxx_parenthesized_type_id_annotation(
        size_t token_idx,
        const SemanticKey& key,
        CxxParenthesizedTypeIdAnnotation value) {
        value.annotation = make_semantic_header(
            token_idx,
            AnnotationKind::ParenthesizedTypeId,
            key,
            value.end_token_idx,
            value.close_token_idx,
            value.dependent_or_ambiguous);
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cxx_parenthesized_type_id;
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CxxDeclaratorParenSuffixAnnotation>
    lookup_cxx_declarator_paren_suffix_annotation(
        size_t token_idx,
        const SemanticKey& key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->cxx_declarator_paren_suffix;
        if (!entry.valid || !(entry.key == key)) {
            return std::nullopt;
        }
        return entry.value;
    }

    CxxDeclaratorParenSuffixAnnotation
    store_cxx_declarator_paren_suffix_annotation(
        size_t token_idx,
        const SemanticKey& key,
        CxxDeclaratorParenSuffixAnnotation value) {
        value.annotation = make_semantic_header(
            token_idx,
            AnnotationKind::DeclaratorParenSuffix,
            key,
            value.end_token_idx,
            value.end_token_idx,
            value.dependent_or_ambiguous);
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cxx_declarator_paren_suffix;
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CppQualifiedDeclaratorPrefixAnnotation>
    lookup_cpp_qualified_declarator_prefix_annotation(size_t token_idx,
                                                      uint32_t key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry = slot->cpp_qualified_declarator_prefix;
        if (!entry.valid || entry.key != key) {
            return std::nullopt;
        }
        return entry.value;
    }

    CppQualifiedDeclaratorPrefixAnnotation
    store_cpp_qualified_declarator_prefix_annotation(
        size_t token_idx,
        uint32_t key,
        CppQualifiedDeclaratorPrefixAnnotation value) {
        value.annotation = make_syntax_header(
            token_idx,
            AnnotationKind::QualifiedDeclaratorPrefix,
            key,
            value.end_token_idx,
            value.end_token_idx,
            value.dependent_or_ambiguous);
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cpp_qualified_declarator_prefix;
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

    std::optional<CppTypeScopeAnnotation>
    lookup_cpp_type_scope_annotation(size_t token_idx,
                                     CppTypeScopeContext context,
                                     const SemanticKey& key) const {
        const auto* slot = slot_for(token_idx);
        if (!slot) {
            return std::nullopt;
        }
        const auto& entry =
            slot->cpp_type_scope[static_cast<size_t>(context)];
        if (!entry.valid || !(entry.key == key)) {
            return std::nullopt;
        }
        return entry.value;
    }

    CppTypeScopeAnnotation
    store_cpp_type_scope_annotation(size_t token_idx,
                                    CppTypeScopeContext context,
                                    const SemanticKey& key,
                                    CppTypeScopeAnnotation value) {
        value.annotation = make_semantic_header(
            token_idx,
            AnnotationKind::TypeScope,
            key,
            value.end_token_idx,
            value.terminal_token_idx,
            value.dependent_or_ambiguous,
            static_cast<uint8_t>(context));
        auto* slot = slot_for(token_idx);
        if (!slot) {
            return value;
        }
        auto& entry = slot->cpp_type_scope[static_cast<size_t>(context)];
        entry.valid = true;
        entry.key = key;
        entry.value = value;
        return value;
    }

private:
    struct ResultEntry {
        bool valid = false;
        uint32_t key = 0;
        tentative_syntax_probe::Result value =
            tentative_syntax_probe::Result::NoMatch;
    };

    template <typename T>
    struct Entry {
        bool valid = false;
        uint32_t key = 0;
        T value{};
    };

    struct SemanticEntry {
        bool valid = false;
        SemanticKey key;
        SemanticAnnotation value;
    };

    struct CppTemplateIdEntry {
        bool valid = false;
        SemanticKey key;
        CppTemplateIdAnnotation value;
    };

    struct CppQualifiedIdEntry {
        bool valid = false;
        uint32_t key = 0;
        CppQualifiedIdAnnotation value;
    };

    struct CppTemplateArgumentEntry {
        bool valid = false;
        SemanticKey key;
        CppTemplateArgumentAnnotation value;
    };

    struct CxxParenthesizedTypeIdEntry {
        bool valid = false;
        SemanticKey key;
        CxxParenthesizedTypeIdAnnotation value;
    };

    struct CxxDeclaratorParenSuffixEntry {
        bool valid = false;
        SemanticKey key;
        CxxDeclaratorParenSuffixAnnotation value;
    };

    struct CppQualifiedDeclaratorPrefixEntry {
        bool valid = false;
        uint32_t key = 0;
        CppQualifiedDeclaratorPrefixAnnotation value;
    };

    struct CppTypeScopeEntry {
        bool valid = false;
        SemanticKey key;
        CppTypeScopeAnnotation value;
    };

    struct TokenSlots {
        std::array<ResultEntry, static_cast<size_t>(ResultKind::Count)> results;
        Entry<tentative_syntax_probe::TemplateArgumentListScan>
            template_argument_list_scan;
        Entry<tentative_syntax_probe::CxxTypeConstructionScan>
            type_construction_scan;
        Entry<tentative_syntax_probe::CxxParameterClauseShape>
            parameter_clause_shape;
        std::array<SemanticEntry, static_cast<size_t>(SemanticKind::Count)>
            semantic;
        CppTemplateIdEntry cpp_template_id;
        CppQualifiedIdEntry cpp_qualified_id;
        CppTemplateArgumentEntry cpp_template_argument;
        CxxParenthesizedTypeIdEntry cxx_parenthesized_type_id;
        CxxDeclaratorParenSuffixEntry cxx_declarator_paren_suffix;
        CppQualifiedDeclaratorPrefixEntry cpp_qualified_declarator_prefix;
        std::array<CppTypeScopeEntry,
                   static_cast<size_t>(CppTypeScopeContext::Count)>
            cpp_type_scope;
    };

    TokenSlots* slot_for(size_t token_idx) {
        if (token_idx >= slots_.size()) {
            return nullptr;
        }
        return &slots_[token_idx];
    }

    const TokenSlots* slot_for(size_t token_idx) const {
        if (token_idx >= slots_.size()) {
            return nullptr;
        }
        return &slots_[token_idx];
    }

    std::vector<TokenSlots> slots_;
};

#endif
