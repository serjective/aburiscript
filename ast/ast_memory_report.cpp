#include "ast_memory_report.h"

#include "ast.h"
#include "ast_context.h"
#include "symbols.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <iomanip>
#include <map>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

struct KindRow {
    std::string name;
    uint64_t count = 0;
    uint64_t inline_bytes = 0;
};

constexpr auto kAllStmtKinds = std::to_array<StmtKind>({
    StmtKind::CompoundStmt,
    StmtKind::Decl2Stmt,
    StmtKind::ReturnStmt,
    StmtKind::CppTryStmt,
    StmtKind::IfStmt,
    StmtKind::CaseStmt,
    StmtKind::DefaultStmt,
    StmtKind::LabeledStmt,
    StmtKind::GoToStmt,
    StmtKind::ComputedGotoStmt,
    StmtKind::SwitchStmt,
    StmtKind::WhileStmt,
    StmtKind::DoWhileStmt,
    StmtKind::ForStmt,
    StmtKind::CppRangeForStmt,
    StmtKind::ContinueStmt,
    StmtKind::BreakStmt,
    StmtKind::EmptyStmt,
    StmtKind::ErrorStmt,
    StmtKind::AsmStmt,
    StmtKind::IntegerLiteral,
    StmtKind::FloatingLiteral,
    StmtKind::CharacterLiteral,
    StmtKind::StringLiteral,
    StmtKind::PredefinedExpr,
    StmtKind::CppThisExpr,
    StmtKind::VarRef,
    StmtKind::QualifiedVarRef,
    StmtKind::UnresolvedLookupExpr,
    StmtKind::LabelAddressExpr,
    StmtKind::FuncCall,
    StmtKind::DependentCallExpr,
    StmtKind::DependentArraySubscriptExpr,
    StmtKind::DependentUnaryExpr,
    StmtKind::DependentBinaryExpr,
    StmtKind::DependentMemberPointerAccessExpr,
    StmtKind::PackExpansionExpr,
    StmtKind::FoldExpr,
    StmtKind::CppMemberCallExpr,
    StmtKind::CppConstructExpr,
    StmtKind::CppValueInitExpr,
    StmtKind::CppFunctionStyleCastExpr,
    StmtKind::CppImmediateInvocationExpr,
    StmtKind::CondExpr,
    StmtKind::UnaryOperation,
    StmtKind::BinaryOperation,
    StmtKind::CppBuiltinThreeWayCompareExpr,
    StmtKind::CompoundAssignOperation,
    StmtKind::ImplicitCast,
    StmtKind::ExplicitCast,
    StmtKind::ArraySubscriptExpr,
    StmtKind::MemberExpr,
    StmtKind::UnresolvedMemberExpr,
    StmtKind::InitListExpr,
    StmtKind::CompoundLiteralExpr,
    StmtKind::SizeOfExpr,
    StmtKind::SizeOfPackExpr,
    StmtKind::AlignOfExpr,
    StmtKind::CppNoexceptExpr,
    StmtKind::OffsetOfExpr,
    StmtKind::GenericExpr,
    StmtKind::StmtExpr,
    StmtKind::VaArgExpr,
    StmtKind::VaStartExpr,
    StmtKind::VaEndExpr,
    StmtKind::VaCopyExpr,
    StmtKind::BuiltinCallExpr,
    StmtKind::CppTypeIdExpr,
    StmtKind::CppDynamicCastExpr,
    StmtKind::CppThrowExpr,
    StmtKind::CppNewExpr,
    StmtKind::CppDeleteExpr,
    StmtKind::CppPseudoDestructorExpr,
    StmtKind::BlockByrefAccessExpr,
    StmtKind::BlockExpr,
    StmtKind::CppLambdaExpr,
    StmtKind::ConceptSpecializationExpr,
    StmtKind::RequiresExpr,
    StmtKind::ErrorExpr,
});

constexpr auto kAllDeclKinds = std::to_array<DeclKind>({
    DeclKind::NopDecl,
    DeclKind::CppUsingDeclarationDecl,
    DeclKind::TypedefDecl,
    DeclKind::TemplateTypeParmDecl,
    DeclKind::TemplateNonTypeParmDecl,
    DeclKind::TemplateTemplateParmDecl,
    DeclKind::TranslationUnit,
    DeclKind::NamespaceDecl,
    DeclKind::AliasTemplateDecl,
    DeclKind::FunctionTemplateDecl,
    DeclKind::VariableTemplateDecl,
    DeclKind::ClassTemplateDecl,
    DeclKind::CppDeductionGuideDecl,
    DeclKind::ConceptDecl,
    DeclKind::VariableTemplatePartialSpecializationDecl,
    DeclKind::ClassTemplatePartialSpecializationDecl,
    DeclKind::TemplateExplicitSpecializationDecl,
    DeclKind::FuncDecl,
    DeclKind::CppMethodDecl,
    DeclKind::CppConstructorDecl,
    DeclKind::CppDestructorDecl,
    DeclKind::FriendDecl,
    DeclKind::VariableDecl,
    DeclKind::ParamDecl,
    DeclKind::FieldDecl,
    DeclKind::ObjectDecl,
    DeclKind::CppRecordDecl,
    DeclKind::CppAccessSpecDecl,
    DeclKind::EnumDecl,
    DeclKind::EnumConstantDecl,
    DeclKind::FileScopeAsmDecl,
    DeclKind::StaticAssertDecl,
    DeclKind::ErrorDecl,
});

const char* stmt_kind_name(StmtKind kind) {
    switch (kind) {
        case StmtKind::CompoundStmt: return "CompoundStmt";
        case StmtKind::Decl2Stmt: return "Decl2Stmt";
        case StmtKind::ReturnStmt: return "ReturnStmt";
        case StmtKind::CppTryStmt: return "CppTryStmt";
        case StmtKind::IfStmt: return "IfStmt";
        case StmtKind::CaseStmt: return "CaseStmt";
        case StmtKind::DefaultStmt: return "DefaultStmt";
        case StmtKind::LabeledStmt: return "LabeledStmt";
        case StmtKind::GoToStmt: return "GoToStmt";
        case StmtKind::ComputedGotoStmt: return "ComputedGotoStmt";
        case StmtKind::SwitchStmt: return "SwitchStmt";
        case StmtKind::WhileStmt: return "WhileStmt";
        case StmtKind::DoWhileStmt: return "DoWhileStmt";
        case StmtKind::ForStmt: return "ForStmt";
        case StmtKind::CppRangeForStmt: return "CppRangeForStmt";
        case StmtKind::ContinueStmt: return "ContinueStmt";
        case StmtKind::BreakStmt: return "BreakStmt";
        case StmtKind::EmptyStmt: return "EmptyStmt";
        case StmtKind::ErrorStmt: return "ErrorStmt";
        case StmtKind::AsmStmt: return "AsmStmt";
        case StmtKind::IntegerLiteral: return "IntegerLiteral";
        case StmtKind::FloatingLiteral: return "FloatingLiteral";
        case StmtKind::CharacterLiteral: return "CharacterLiteral";
        case StmtKind::StringLiteral: return "StringLiteral";
        case StmtKind::PredefinedExpr: return "PredefinedExpr";
        case StmtKind::CppThisExpr: return "CppThisExpr";
        case StmtKind::VarRef: return "VarRef";
        case StmtKind::QualifiedVarRef: return "QualifiedVarRef";
        case StmtKind::UnresolvedLookupExpr: return "UnresolvedLookupExpr";
        case StmtKind::LabelAddressExpr: return "LabelAddressExpr";
        case StmtKind::FuncCall: return "FuncCall";
        case StmtKind::DependentCallExpr: return "DependentCallExpr";
        case StmtKind::DependentArraySubscriptExpr:
            return "DependentArraySubscriptExpr";
        case StmtKind::DependentUnaryExpr: return "DependentUnaryExpr";
        case StmtKind::DependentBinaryExpr: return "DependentBinaryExpr";
        case StmtKind::DependentMemberPointerAccessExpr:
            return "DependentMemberPointerAccessExpr";
        case StmtKind::PackExpansionExpr: return "PackExpansionExpr";
        case StmtKind::FoldExpr: return "FoldExpr";
        case StmtKind::CppMemberCallExpr: return "CppMemberCallExpr";
        case StmtKind::CppConstructExpr: return "CppConstructExpr";
        case StmtKind::CppValueInitExpr: return "CppValueInitExpr";
        case StmtKind::CppFunctionStyleCastExpr:
            return "CppFunctionStyleCastExpr";
        case StmtKind::CppImmediateInvocationExpr:
            return "CppImmediateInvocationExpr";
        case StmtKind::ParenExpr: return "ParenExpr";
        case StmtKind::CondExpr: return "CondExpr";
        case StmtKind::UnaryOperation: return "UnaryOperation";
        case StmtKind::BinaryOperation: return "BinaryOperation";
        case StmtKind::CppBuiltinThreeWayCompareExpr:
            return "CppBuiltinThreeWayCompareExpr";
        case StmtKind::CompoundAssignOperation: return "CompoundAssignOperation";
        case StmtKind::ImplicitCast: return "ImplicitCast";
        case StmtKind::ExplicitCast: return "ExplicitCast";
        case StmtKind::ArraySubscriptExpr: return "ArraySubscriptExpr";
        case StmtKind::MemberExpr: return "MemberExpr";
        case StmtKind::UnresolvedMemberExpr: return "UnresolvedMemberExpr";
        case StmtKind::InitListExpr: return "InitListExpr";
        case StmtKind::CompoundLiteralExpr: return "CompoundLiteralExpr";
        case StmtKind::SizeOfExpr: return "SizeOfExpr";
        case StmtKind::SizeOfPackExpr: return "SizeOfPackExpr";
        case StmtKind::AlignOfExpr: return "AlignOfExpr";
        case StmtKind::CppNoexceptExpr: return "CppNoexceptExpr";
        case StmtKind::OffsetOfExpr: return "OffsetOfExpr";
        case StmtKind::GenericExpr: return "GenericExpr";
        case StmtKind::StmtExpr: return "StmtExpr";
        case StmtKind::VaArgExpr: return "VaArgExpr";
        case StmtKind::VaStartExpr: return "VaStartExpr";
        case StmtKind::VaEndExpr: return "VaEndExpr";
        case StmtKind::VaCopyExpr: return "VaCopyExpr";
        case StmtKind::BuiltinCallExpr: return "BuiltinCallExpr";
        case StmtKind::CppTypeIdExpr: return "CppTypeIdExpr";
        case StmtKind::CppDynamicCastExpr: return "CppDynamicCastExpr";
        case StmtKind::CppThrowExpr: return "CppThrowExpr";
        case StmtKind::CppNewExpr: return "CppNewExpr";
        case StmtKind::CppDeleteExpr: return "CppDeleteExpr";
        case StmtKind::CppPseudoDestructorExpr: return "CppPseudoDestructorExpr";
        case StmtKind::BlockByrefAccessExpr: return "BlockByrefAccessExpr";
        case StmtKind::BlockExpr: return "BlockExpr";
        case StmtKind::CppLambdaExpr: return "CppLambdaExpr";
        case StmtKind::ErrorExpr: return "ErrorExpr";
        default: return "UnknownStmtKind";
    }
}

const char* decl_kind_name(DeclKind kind) {
    switch (kind) {
        case DeclKind::NopDecl: return "NopDecl";
        case DeclKind::CppUsingDeclarationDecl:
            return "CppUsingDeclarationDecl";
        case DeclKind::TypedefDecl: return "TypedefDecl";
        case DeclKind::TemplateTypeParmDecl: return "TemplateTypeParmDecl";
        case DeclKind::TemplateNonTypeParmDecl: return "TemplateNonTypeParmDecl";
        case DeclKind::TemplateTemplateParmDecl: return "TemplateTemplateParmDecl";
        case DeclKind::TranslationUnit: return "TranslationUnit";
        case DeclKind::NamespaceDecl: return "NamespaceDecl";
        case DeclKind::AliasTemplateDecl: return "AliasTemplateDecl";
        case DeclKind::FunctionTemplateDecl: return "FunctionTemplateDecl";
        case DeclKind::VariableTemplateDecl: return "VariableTemplateDecl";
        case DeclKind::ClassTemplateDecl: return "ClassTemplateDecl";
        case DeclKind::CppDeductionGuideDecl: return "CppDeductionGuideDecl";
        case DeclKind::ConceptDecl: return "ConceptDecl";
        case DeclKind::VariableTemplatePartialSpecializationDecl:
            return "VariableTemplatePartialSpecializationDecl";
        case DeclKind::ClassTemplatePartialSpecializationDecl:
            return "ClassTemplatePartialSpecializationDecl";
        case DeclKind::TemplateExplicitSpecializationDecl:
            return "TemplateExplicitSpecializationDecl";
        case DeclKind::FuncDecl: return "FuncDecl";
        case DeclKind::CppMethodDecl: return "CppMethodDecl";
        case DeclKind::CppConstructorDecl: return "CppConstructorDecl";
        case DeclKind::CppDestructorDecl: return "CppDestructorDecl";
        case DeclKind::FriendDecl: return "FriendDecl";
        case DeclKind::VariableDecl: return "VariableDecl";
        case DeclKind::ParamDecl: return "ParamDecl";
        case DeclKind::FieldDecl: return "FieldDecl";
        case DeclKind::ObjectDecl: return "ObjectDecl";
        case DeclKind::CppRecordDecl: return "CppRecordDecl";
        case DeclKind::CppAccessSpecDecl: return "CppAccessSpecDecl";
        case DeclKind::EnumDecl: return "EnumDecl";
        case DeclKind::EnumConstantDecl: return "EnumConstantDecl";
        case DeclKind::FileScopeAsmDecl: return "FileScopeAsmDecl";
        case DeclKind::StaticAssertDecl: return "StaticAssertDecl";
        case DeclKind::ErrorDecl: return "ErrorDecl";
        default: return "UnknownDeclKind";
    }
}

std::string format_bytes(uint64_t bytes) {
    static constexpr uint64_t kib = 1024;
    static constexpr uint64_t mib = 1024 * kib;
    static constexpr uint64_t gib = 1024 * mib;

    std::ostringstream oss;
    oss << bytes << " B";
    if (bytes >= gib) {
        oss << " (" << std::fixed << std::setprecision(2)
            << static_cast<double>(bytes) / static_cast<double>(gib) << " GiB)";
    } else if (bytes >= mib) {
        oss << " (" << std::fixed << std::setprecision(2)
            << static_cast<double>(bytes) / static_cast<double>(mib) << " MiB)";
    } else if (bytes >= kib) {
        oss << " (" << std::fixed << std::setprecision(2)
            << static_cast<double>(bytes) / static_cast<double>(kib) << " KiB)";
    }
    return oss.str();
}

uint64_t estimate_string_heap_bytes(const std::string& value) {
    if (value.empty()) {
        return 0;
    }
    return static_cast<uint64_t>(value.capacity()) + 1;
}

template <typename T>
uint64_t vector_backing_bytes(const std::vector<T>& value) {
    return static_cast<uint64_t>(value.capacity()) * sizeof(T);
}

template <typename T, typename Hash, typename Eq, typename Alloc>
uint64_t unordered_set_bucket_bytes(const std::unordered_set<T, Hash, Eq, Alloc>& value) {
    return static_cast<uint64_t>(value.bucket_count()) * sizeof(void*);
}

template <typename K, typename V, typename Comp, typename Alloc>
uint64_t map_node_storage_lower_bound_bytes(const std::map<K, V, Comp, Alloc>& value) {
    return static_cast<uint64_t>(value.size()) * sizeof(typename std::map<K, V, Comp, Alloc>::value_type);
}

class ASTMemoryAnalyzer {
public:
    explicit ASTMemoryAnalyzer(const ASTContext& ast_ctx) : ast_ctx_(ast_ctx) {}

    void analyze(const Decl* root) {
        visit_decl(root);
    }

    const std::array<uint64_t, static_cast<size_t>(StmtKind::LastExpr) + 1>& stmt_counts() const {
        return stmt_counts_;
    }

    const std::array<uint64_t, static_cast<size_t>(StmtKind::LastExpr) + 1>& stmt_inline_bytes() const {
        return stmt_inline_bytes_;
    }

    const std::array<uint64_t, static_cast<size_t>(DeclKind::ErrorDecl) + 1>& decl_counts() const {
        return decl_counts_;
    }

    const std::array<uint64_t, static_cast<size_t>(DeclKind::ErrorDecl) + 1>& decl_inline_bytes() const {
        return decl_inline_bytes_;
    }

    uint64_t ast_string_heap_bytes() const { return ast_string_heap_bytes_; }
    uint64_t ast_vector_backing_bytes() const { return ast_vector_backing_bytes_; }
    uint64_t ast_map_storage_lower_bound_bytes() const { return ast_map_storage_lower_bound_bytes_; }
    uint64_t ast_unordered_set_bucket_bytes() const { return ast_unordered_set_bucket_bytes_; }

    uint64_t symbol_count() const { return symbol_count_; }
    uint64_t symbol_inline_bytes() const { return symbol_inline_bytes_; }
    uint64_t symbol_string_heap_bytes() const { return symbol_string_heap_bytes_; }
    uint64_t symbol_vector_backing_bytes() const { return symbol_vector_backing_bytes_; }

private:
    template <typename T>
    void record_stmt(StmtKind kind) {
        const auto idx = static_cast<size_t>(kind);
        ++stmt_counts_[idx];
        stmt_inline_bytes_[idx] += sizeof(T);
    }

    template <typename T>
    void record_decl(DeclKind kind) {
        const auto idx = static_cast<size_t>(kind);
        ++decl_counts_[idx];
        decl_inline_bytes_[idx] += sizeof(T);
    }

    void add_ast_string(const std::string& value) {
        ast_string_heap_bytes_ += estimate_string_heap_bytes(value);
    }

    void add_symbol_string(const std::string& value) {
        symbol_string_heap_bytes_ += estimate_string_heap_bytes(value);
    }

    void visit_attribute_arg(const AttributeArg& arg, bool symbol_storage) {
        if (symbol_storage) {
            add_symbol_string(arg.str_value);
            add_symbol_string(arg.key);
        } else {
            add_ast_string(arg.str_value);
            add_ast_string(arg.key);
            if (arg.expr_value) {
                visit_stmt(arg.expr_value.get());
            }
        }
    }

    void visit_parsed_attribute(const ParsedAttribute& attr, bool symbol_storage) {
        if (symbol_storage) {
            add_symbol_string(attr.ns);
            add_symbol_string(attr.name);
            symbol_vector_backing_bytes_ += vector_backing_bytes(attr.args);
        } else {
            add_ast_string(attr.ns);
            add_ast_string(attr.name);
            ast_vector_backing_bytes_ += vector_backing_bytes(attr.args);
        }
        for (const auto& arg : attr.args) {
            visit_attribute_arg(arg, symbol_storage);
        }
    }

    void visit_attribute_list(const AttributeList& attrs, bool symbol_storage) {
        if (symbol_storage) {
            symbol_vector_backing_bytes_ += vector_backing_bytes(attrs.attrs);
        } else {
            ast_vector_backing_bytes_ += vector_backing_bytes(attrs.attrs);
        }
        for (const auto& attr : attrs.attrs) {
            visit_parsed_attribute(attr, symbol_storage);
        }
    }

    void visit_node_attrs(uint32_t node_id) {
        if (!ast_ctx_.has_attrs(node_id)) {
            return;
        }
        visit_attribute_list(ast_ctx_.get_attrs(node_id), false);
    }

    void visit_template_argument(const TemplateArgument& argument) {
        add_ast_string(argument.template_name);
        add_ast_string(argument.value_spelling);
        ast_vector_backing_bytes_ +=
            vector_backing_bytes(argument.pack_expansion_parameters);
        if (argument.referenced_parameter) {
            visit_decl(argument.referenced_parameter);
        }
        for (const auto* parameter : argument.pack_expansion_parameters) {
            visit_decl(parameter);
        }
        if (argument.template_decl) {
            visit_decl(argument.template_decl);
        }
        if (argument.value_expr) {
            visit_stmt(argument.value_expr.get());
        }
    }

    void visit_template_arguments(const std::vector<TemplateArgument>& arguments) {
        ast_vector_backing_bytes_ += vector_backing_bytes(arguments);
        for (const auto& argument : arguments) {
            visit_template_argument(argument);
        }
    }

    void visit_symbol(const std::shared_ptr<Symbol>& symbol) {
        if (!symbol) {
            return;
        }
        const Symbol* raw = symbol.get();
        if (!seen_symbols_.insert(raw).second) {
            return;
        }
        ++symbol_count_;
        symbol_inline_bytes_ += sizeof(Symbol);
        add_symbol_string(symbol->uid);
        add_symbol_string(symbol->name);
        add_symbol_string(symbol->deprecated_message);
        if (symbol->asm_label.has_value()) {
            add_symbol_string(*symbol->asm_label);
        }
        visit_attribute_list(symbol->sym_attrs, true);
    }

    void visit_decl(const Decl* decl) {
        if (!decl) {
            return;
        }
        if (!seen_decls_.insert(decl).second) {
            return;
        }
        visit_node_attrs(decl->node_id);

        switch (decl->get_kind()) {
            case DeclKind::NopDecl: {
                record_decl<NopDecl>(DeclKind::NopDecl);
                return;
            }
            case DeclKind::CppUsingDeclarationDecl: {
                auto* node = static_cast<const CppUsingDeclarationDecl*>(decl);
                record_decl<CppUsingDeclarationDecl>(
                    DeclKind::CppUsingDeclarationDecl);
                for (const auto& imported : node->ordinary_symbols) {
                    add_ast_string(imported.name);
                    visit_symbol(imported.symbol);
                }
                for (const auto& imported : node->template_decls) {
                    add_ast_string(imported.name);
                    visit_decl(imported.decl);
                }
                for (const auto& imported : node->tag_decls) {
                    add_ast_string(imported.name);
                    visit_decl(imported.decl);
                }
                for (const auto& target : node->replay_targets) {
                    add_ast_string(target.name);
                    for (const auto& imported : target.ordinary_symbols) {
                        add_ast_string(imported.name);
                        visit_symbol(imported.symbol);
                    }
                    for (const auto& imported : target.template_decls) {
                        add_ast_string(imported.name);
                        visit_decl(imported.decl);
                    }
                    for (const auto& imported : target.tag_decls) {
                        add_ast_string(imported.name);
                        visit_decl(imported.decl);
                    }
                }
                return;
            }
            case DeclKind::TypedefDecl: {
                auto* node = static_cast<const TypedefDecl*>(decl);
                record_decl<TypedefDecl>(DeclKind::TypedefDecl);
                add_ast_string(node->name);
                visit_symbol(node->sym);
                return;
            }
            case DeclKind::TemplateTypeParmDecl: {
                auto* node = static_cast<const TemplateTypeParmDecl*>(decl);
                record_decl<TemplateTypeParmDecl>(DeclKind::TemplateTypeParmDecl);
                add_ast_string(node->name);
                if (const auto* default_argument =
                        get_template_parameter_default_argument(node)) {
                    visit_template_argument(*default_argument);
                }
                return;
            }
            case DeclKind::TemplateNonTypeParmDecl: {
                auto* node = static_cast<const TemplateNonTypeParmDecl*>(decl);
                record_decl<TemplateNonTypeParmDecl>(
                    DeclKind::TemplateNonTypeParmDecl);
                add_ast_string(node->name);
                if (const auto* default_argument =
                        get_template_parameter_default_argument(node)) {
                    visit_template_argument(*default_argument);
                }
                visit_symbol(node->sym);
                return;
            }
            case DeclKind::TemplateTemplateParmDecl: {
                auto* node = static_cast<const TemplateTemplateParmDecl*>(decl);
                record_decl<TemplateTemplateParmDecl>(
                    DeclKind::TemplateTemplateParmDecl);
                add_ast_string(node->name);
                if (const auto* default_argument =
                        get_template_parameter_default_argument(node)) {
                    visit_template_argument(*default_argument);
                }
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                return;
            }
            case DeclKind::TranslationUnit: {
                auto* node = static_cast<const TranslationUnit*>(decl);
                record_decl<TranslationUnit>(DeclKind::TranslationUnit);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->declarations);
                for (const auto& child : node->declarations) {
                    visit_decl(child.get());
                }
                return;
            }
            case DeclKind::NamespaceDecl: {
                auto* node = static_cast<const NamespaceDecl*>(decl);
                record_decl<NamespaceDecl>(DeclKind::NamespaceDecl);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->members);
                return;
            }
            case DeclKind::AliasTemplateDecl: {
                auto* node = static_cast<const AliasTemplateDecl*>(decl);
                record_decl<AliasTemplateDecl>(DeclKind::AliasTemplateDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_decl(node->templated_decl.get());
                return;
            }
            case DeclKind::FunctionTemplateDecl: {
                auto* node = static_cast<const FunctionTemplateDecl*>(decl);
                record_decl<FunctionTemplateDecl>(DeclKind::FunctionTemplateDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_decl(node->templated_decl.get());
                return;
            }
            case DeclKind::VariableTemplateDecl: {
                auto* node = static_cast<const VariableTemplateDecl*>(decl);
                record_decl<VariableTemplateDecl>(DeclKind::VariableTemplateDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_decl(node->templated_decl.get());
                return;
            }
            case DeclKind::ClassTemplateDecl: {
                auto* node = static_cast<const ClassTemplateDecl*>(decl);
                record_decl<ClassTemplateDecl>(DeclKind::ClassTemplateDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_decl(node->templated_decl.get());
                return;
            }
            case DeclKind::CppDeductionGuideDecl: {
                auto* node = static_cast<const CppDeductionGuideDecl*>(decl);
                record_decl<CppDeductionGuideDecl>(
                    DeclKind::CppDeductionGuideDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->guide_parameters);
                for (const auto& param : node->guide_parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->associated_constraint.get());
                visit_stmt(node->explicit_specifier.condition.get());
                return;
            }
            case DeclKind::ConceptDecl: {
                auto* node = static_cast<const ConceptDecl*>(decl);
                record_decl<ConceptDecl>(DeclKind::ConceptDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->associated_constraint.get());
                visit_stmt(node->constraint_expr.get());
                return;
            }
            case DeclKind::VariableTemplatePartialSpecializationDecl: {
                auto* node =
                    static_cast<const VariableTemplatePartialSpecializationDecl*>(decl);
                record_decl<VariableTemplatePartialSpecializationDecl>(
                    DeclKind::VariableTemplatePartialSpecializationDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                visit_template_arguments(node->specialization_arguments);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_decl(node->templated_decl.get());
                return;
            }
            case DeclKind::ClassTemplatePartialSpecializationDecl: {
                auto* node =
                    static_cast<const ClassTemplatePartialSpecializationDecl*>(decl);
                record_decl<ClassTemplatePartialSpecializationDecl>(
                    DeclKind::ClassTemplatePartialSpecializationDecl);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                visit_template_arguments(node->specialization_arguments);
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_decl(node->templated_decl.get());
                return;
            }
            case DeclKind::TemplateExplicitSpecializationDecl: {
                auto* node =
                    static_cast<const TemplateExplicitSpecializationDecl*>(decl);
                record_decl<TemplateExplicitSpecializationDecl>(
                    DeclKind::TemplateExplicitSpecializationDecl);
                visit_template_arguments(node->specialization_arguments);
                visit_template_arguments(node->owner_specialization_arguments);
                visit_decl(node->specialized_decl.get());
                return;
            }
            case DeclKind::FuncDecl: {
                auto* node = static_cast<const FuncDecl*>(decl);
                record_decl<FuncDecl>(DeclKind::FuncDecl);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                ast_unordered_set_bucket_bytes_ += unordered_set_bucket_bytes(node->stmt_labels);
                for (const auto& label : node->stmt_labels) {
                    add_ast_string(label);
                }
                if (node->asm_label) {
                    add_ast_string(*node->asm_label);
                }
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->body.get());
                return;
            }
            case DeclKind::CppMethodDecl: {
                auto* node = static_cast<const CppMethodDecl*>(decl);
                record_decl<CppMethodDecl>(DeclKind::CppMethodDecl);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                ast_unordered_set_bucket_bytes_ += unordered_set_bucket_bytes(node->stmt_labels);
                for (const auto& label : node->stmt_labels) {
                    add_ast_string(label);
                }
                if (node->asm_label) {
                    add_ast_string(*node->asm_label);
                }
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->explicit_specifier.condition.get());
                visit_stmt(node->body.get());
                return;
            }
            case DeclKind::CppConstructorDecl: {
                auto* node = static_cast<const CppConstructorDecl*>(decl);
                record_decl<CppConstructorDecl>(DeclKind::CppConstructorDecl);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                ast_unordered_set_bucket_bytes_ += unordered_set_bucket_bytes(node->stmt_labels);
                for (const auto& label : node->stmt_labels) {
                    add_ast_string(label);
                }
                if (node->asm_label) {
                    add_ast_string(*node->asm_label);
                }
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->explicit_specifier.condition.get());
                visit_stmt(node->body.get());
                return;
            }
            case DeclKind::CppDestructorDecl: {
                auto* node = static_cast<const CppDestructorDecl*>(decl);
                record_decl<CppDestructorDecl>(DeclKind::CppDestructorDecl);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                ast_unordered_set_bucket_bytes_ += unordered_set_bucket_bytes(node->stmt_labels);
                for (const auto& label : node->stmt_labels) {
                    add_ast_string(label);
                }
                if (node->asm_label) {
                    add_ast_string(*node->asm_label);
                }
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->body.get());
                return;
            }
            case DeclKind::FriendDecl: {
                auto* node = static_cast<const FriendDecl*>(decl);
                record_decl<FriendDecl>(DeclKind::FriendDecl);
                visit_decl(node->target_decl.get());
                visit_symbol(node->function_symbol);
                return;
            }
            case DeclKind::VariableDecl: {
                auto* node = static_cast<const VariableDecl*>(decl);
                record_decl<VariableDecl>(DeclKind::VariableDecl);
                add_ast_string(node->name);
                if (node->asm_label) {
                    add_ast_string(*node->asm_label);
                }
                visit_symbol(node->sym);
                if (const auto* dtor_sym =
                        ast_ctx_.get_cpp_variable_destructor_symbol(node->node_id)) {
                    visit_symbol(*dtor_sym);
                }
                visit_stmt(node->init.get());
                return;
            }
            case DeclKind::ParamDecl: {
                auto* node = static_cast<const ParamDecl*>(decl);
                record_decl<ParamDecl>(DeclKind::ParamDecl);
                add_ast_string(node->get_name());
                visit_symbol(node->sym);
                return;
            }
            case DeclKind::FieldDecl: {
                auto* node = static_cast<const FieldDecl*>(decl);
                record_decl<FieldDecl>(DeclKind::FieldDecl);
                add_ast_string(node->name);
                return;
            }
            case DeclKind::ObjectDecl: {
                auto* node = static_cast<const ObjectDecl*>(decl);
                record_decl<ObjectDecl>(DeclKind::ObjectDecl);
                add_ast_string(node->tag);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->fields);
                for (const auto& field : node->fields) {
                    visit_decl(field.get());
                }
                return;
            }
            case DeclKind::CppRecordDecl: {
                auto* node = static_cast<const CppRecordDecl*>(decl);
                record_decl<CppRecordDecl>(DeclKind::CppRecordDecl);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->bases);
                for (const auto& base : node->bases) {
                    add_ast_string(base.type_name);
                }
                ast_vector_backing_bytes_ += vector_backing_bytes(node->members);
                for (const auto& member : node->members) {
                    visit_decl(member.get());
                }
                return;
            }
            case DeclKind::CppAccessSpecDecl: {
                record_decl<CppAccessSpecDecl>(DeclKind::CppAccessSpecDecl);
                return;
            }
            case DeclKind::EnumDecl: {
                auto* node = static_cast<const EnumDecl*>(decl);
                record_decl<EnumDecl>(DeclKind::EnumDecl);
                add_ast_string(node->tag);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->constants);
                for (const auto& constant : node->constants) {
                    visit_decl(constant.get());
                }
                return;
            }
            case DeclKind::EnumConstantDecl: {
                auto* node = static_cast<const EnumConstantDecl*>(decl);
                record_decl<EnumConstantDecl>(DeclKind::EnumConstantDecl);
                add_ast_string(node->name);
                visit_symbol(node->sym);
                visit_stmt(node->init.get());
                return;
            }
            case DeclKind::FileScopeAsmDecl: {
                auto* node = static_cast<const FileScopeAsmDecl*>(decl);
                record_decl<FileScopeAsmDecl>(DeclKind::FileScopeAsmDecl);
                add_ast_string(node->asm_string);
                return;
            }
            case DeclKind::StaticAssertDecl: {
                auto* node = static_cast<const StaticAssertDecl*>(decl);
                record_decl<StaticAssertDecl>(DeclKind::StaticAssertDecl);
                add_ast_string(node->message);
                visit_stmt(node->condition.get());
                return;
            }
            case DeclKind::ErrorDecl: {
                auto* node = static_cast<const ErrorDecl*>(decl);
                record_decl<ErrorDecl>(DeclKind::ErrorDecl);
                add_ast_string(node->error_message);
                return;
            }
        }
    }

    void visit_stmt(const Stmt* stmt) {
        if (!stmt) {
            return;
        }
        if (!seen_stmts_.insert(stmt).second) {
            return;
        }
        visit_node_attrs(stmt->node_id);

        switch (stmt->get_kind()) {
            case StmtKind::CompoundStmt: {
                auto* node = static_cast<const CompoundStmt*>(stmt);
                record_stmt<CompoundStmt>(StmtKind::CompoundStmt);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->statements);
                for (const auto& child : node->statements) {
                    visit_stmt(child.get());
                }
                return;
            }
            case StmtKind::Decl2Stmt: {
                auto* node = static_cast<const Decl2Stmt*>(stmt);
                record_stmt<Decl2Stmt>(StmtKind::Decl2Stmt);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->decls);
                for (const auto& decl : node->decls) {
                    visit_decl(decl.get());
                }
                return;
            }
            case StmtKind::ReturnStmt: {
                auto* node = static_cast<const ReturnStmt*>(stmt);
                record_stmt<ReturnStmt>(StmtKind::ReturnStmt);
                visit_stmt(node->expression.get());
                return;
            }
            case StmtKind::CppTryStmt: {
                auto* node = static_cast<const CppTryStmt*>(stmt);
                record_stmt<CppTryStmt>(StmtKind::CppTryStmt);
                visit_stmt(node->try_block.get());
                ast_vector_backing_bytes_ += vector_backing_bytes(node->handlers);
                for (const auto& handler : node->handlers) {
                    add_ast_string(handler.exception_name);
                    visit_stmt(handler.handler.get());
                }
                return;
            }
            case StmtKind::IfStmt: {
                auto* node = static_cast<const IfStmt*>(stmt);
                record_stmt<IfStmt>(StmtKind::IfStmt);
                visit_stmt(node->init_stmt.get());
                visit_stmt(node->condition.declaration.get());
                visit_stmt(node->condition.expression.get());
                visit_stmt(node->then_stmt.get());
                visit_stmt(node->else_stmt.get());
                return;
            }
            case StmtKind::CaseStmt: {
                auto* node = static_cast<const CaseStmt*>(stmt);
                record_stmt<CaseStmt>(StmtKind::CaseStmt);
                visit_stmt(node->const_expr.get());
                visit_stmt(node->range_end.get());
                visit_stmt(node->stmt.get());
                return;
            }
            case StmtKind::DefaultStmt: {
                auto* node = static_cast<const DefaultStmt*>(stmt);
                record_stmt<DefaultStmt>(StmtKind::DefaultStmt);
                visit_stmt(node->stmt.get());
                return;
            }
            case StmtKind::LabeledStmt: {
                auto* node = static_cast<const LabeledStmt*>(stmt);
                record_stmt<LabeledStmt>(StmtKind::LabeledStmt);
                add_ast_string(node->name);
                visit_stmt(node->stmt.get());
                return;
            }
            case StmtKind::GoToStmt: {
                auto* node = static_cast<const GoToStmt*>(stmt);
                record_stmt<GoToStmt>(StmtKind::GoToStmt);
                add_ast_string(node->name);
                return;
            }
            case StmtKind::ComputedGotoStmt: {
                auto* node = static_cast<const ComputedGotoStmt*>(stmt);
                record_stmt<ComputedGotoStmt>(StmtKind::ComputedGotoStmt);
                visit_stmt(node->target.get());
                return;
            }
            case StmtKind::SwitchStmt: {
                auto* node = static_cast<const SwitchStmt*>(stmt);
                record_stmt<SwitchStmt>(StmtKind::SwitchStmt);
                visit_stmt(node->condition.declaration.get());
                visit_stmt(node->condition.expression.get());
                visit_stmt(node->stmt.get());
                return;
            }
            case StmtKind::WhileStmt: {
                auto* node = static_cast<const WhileStmt*>(stmt);
                record_stmt<WhileStmt>(StmtKind::WhileStmt);
                visit_stmt(node->condition.declaration.get());
                visit_stmt(node->condition.expression.get());
                visit_stmt(node->body_stmt.get());
                return;
            }
            case StmtKind::DoWhileStmt: {
                auto* node = static_cast<const DoWhileStmt*>(stmt);
                record_stmt<DoWhileStmt>(StmtKind::DoWhileStmt);
                visit_stmt(node->condition.get());
                visit_stmt(node->body_stmt.get());
                return;
            }
            case StmtKind::ForStmt: {
                auto* node = static_cast<const ForStmt*>(stmt);
                record_stmt<ForStmt>(StmtKind::ForStmt);
                visit_stmt(node->init.get());
                visit_stmt(node->cond.declaration.get());
                visit_stmt(node->cond.expression.get());
                visit_stmt(node->action.get());
                visit_stmt(node->body_stmt.get());
                return;
            }
            case StmtKind::CppRangeForStmt: {
                auto* node = static_cast<const CppRangeForStmt*>(stmt);
                record_stmt<CppRangeForStmt>(StmtKind::CppRangeForStmt);
                visit_stmt(node->init_statement.get());
                for (const auto& decl : node->range_declaration_side_decls) {
                    visit_decl(decl.get());
                }
                visit_decl(node->range_variable.get());
                visit_decl(node->begin_variable.get());
                visit_decl(node->end_variable.get());
                visit_decl(node->loop_variable.get());
                visit_stmt(node->condition.get());
                visit_stmt(node->increment.get());
                visit_stmt(node->body_stmt.get());
                return;
            }
            case StmtKind::ContinueStmt: {
                record_stmt<ContinueStmt>(StmtKind::ContinueStmt);
                return;
            }
            case StmtKind::BreakStmt: {
                record_stmt<BreakStmt>(StmtKind::BreakStmt);
                return;
            }
            case StmtKind::EmptyStmt: {
                record_stmt<EmptyStmt>(StmtKind::EmptyStmt);
                return;
            }
            case StmtKind::ErrorStmt: {
                auto* node = static_cast<const ErrorStmt*>(stmt);
                record_stmt<ErrorStmt>(StmtKind::ErrorStmt);
                add_ast_string(node->error_message);
                return;
            }
            case StmtKind::AsmStmt: {
                auto* node = static_cast<const AsmStmt*>(stmt);
                record_stmt<AsmStmt>(StmtKind::AsmStmt);
                add_ast_string(node->asm_template);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->output_operands);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->input_operands);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->clobbers);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->goto_labels);
                for (const auto& op : node->output_operands) {
                    add_ast_string(op.symbolic_name);
                    add_ast_string(op.constraint);
                    visit_stmt(op.expr.get());
                }
                for (const auto& op : node->input_operands) {
                    add_ast_string(op.symbolic_name);
                    add_ast_string(op.constraint);
                    visit_stmt(op.expr.get());
                }
                for (const auto& clobber : node->clobbers) {
                    add_ast_string(clobber);
                }
                for (const auto& label : node->goto_labels) {
                    add_ast_string(label);
                }
                return;
            }
            case StmtKind::IntegerLiteral: {
                auto* node = static_cast<const IntegerLiteral*>(stmt);
                record_stmt<IntegerLiteral>(StmtKind::IntegerLiteral);
                return;
            }
            case StmtKind::FloatingLiteral: {
                auto* node = static_cast<const FloatingLiteral*>(stmt);
                record_stmt<FloatingLiteral>(StmtKind::FloatingLiteral);
                add_ast_string(node->value);
                return;
            }
            case StmtKind::CharacterLiteral: {
                auto* node = static_cast<const CharacterLiteral*>(stmt);
                record_stmt<CharacterLiteral>(StmtKind::CharacterLiteral);
                add_ast_string(node->value);
                return;
            }
            case StmtKind::StringLiteral: {
                auto* node = static_cast<const StringLiteral*>(stmt);
                record_stmt<StringLiteral>(StmtKind::StringLiteral);
                add_ast_string(node->value);
                return;
            }
            case StmtKind::PredefinedExpr: {
                auto* node = static_cast<const PredefinedExpr*>(stmt);
                record_stmt<PredefinedExpr>(StmtKind::PredefinedExpr);
                add_ast_string(node->func_name);
                return;
            }
            case StmtKind::CppThisExpr: {
                record_stmt<CppThisExpr>(StmtKind::CppThisExpr);
                return;
            }
            case StmtKind::VarRef:
            case StmtKind::QualifiedVarRef: {
                auto* node = static_cast<const VarRef*>(stmt);
                if (stmt->get_kind() == StmtKind::QualifiedVarRef) {
                    record_stmt<QualifiedVarRef>(StmtKind::QualifiedVarRef);
                    if (const auto* qualified_info = node->get_cpp_qualified_info()) {
                        ast_vector_backing_bytes_ +=
                            vector_backing_bytes(qualified_info->qualifiers);
                        for (const auto& qualifier : qualified_info->qualifiers) {
                            add_ast_string(qualifier);
                        }
                    }
                } else {
                    record_stmt<VarRef>(StmtKind::VarRef);
                }
                visit_symbol(node->symref);
                return;
            }
            case StmtKind::UnresolvedLookupExpr: {
                auto* node = static_cast<const UnresolvedLookupExpr*>(stmt);
                record_stmt<UnresolvedLookupExpr>(StmtKind::UnresolvedLookupExpr);
                add_ast_string(node->name);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->qualifier.qualifiers);
                for (const auto& qualifier : node->qualifier.qualifiers) {
                    add_ast_string(qualifier);
                }
                if (node->explicit_template_arguments.has_value()) {
                    visit_template_arguments(*node->explicit_template_arguments);
                }
                return;
            }
            case StmtKind::LabelAddressExpr: {
                auto* node = static_cast<const LabelAddressExpr*>(stmt);
                record_stmt<LabelAddressExpr>(StmtKind::LabelAddressExpr);
                add_ast_string(node->label);
                return;
            }
            case StmtKind::FuncCall: {
                auto* node = static_cast<const FuncCall*>(stmt);
                record_stmt<FuncCall>(StmtKind::FuncCall);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->args);
                visit_stmt(node->func.get());
                for (const auto& arg : node->args) {
                    visit_stmt(arg.get());
                }
                return;
            }
            case StmtKind::DependentCallExpr: {
                auto* node = static_cast<const DependentCallExpr*>(stmt);
                record_stmt<DependentCallExpr>(StmtKind::DependentCallExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->args);
                visit_stmt(node->callee.get());
                for (const auto& arg : node->args) {
                    visit_stmt(arg.get());
                }
                return;
            }
            case StmtKind::DependentArraySubscriptExpr: {
                auto* node =
                    static_cast<const DependentArraySubscriptExpr*>(stmt);
                record_stmt<DependentArraySubscriptExpr>(
                    StmtKind::DependentArraySubscriptExpr);
                visit_stmt(node->array.get());
                visit_stmt(node->index.get());
                return;
            }
            case StmtKind::DependentUnaryExpr: {
                auto* node = static_cast<const DependentUnaryExpr*>(stmt);
                record_stmt<DependentUnaryExpr>(StmtKind::DependentUnaryExpr);
                visit_stmt(node->operand.get());
                return;
            }
            case StmtKind::DependentBinaryExpr: {
                auto* node = static_cast<const DependentBinaryExpr*>(stmt);
                record_stmt<DependentBinaryExpr>(
                    StmtKind::DependentBinaryExpr);
                visit_stmt(node->left.get());
                visit_stmt(node->right.get());
                return;
            }
            case StmtKind::DependentMemberPointerAccessExpr: {
                auto* node =
                    static_cast<const DependentMemberPointerAccessExpr*>(stmt);
                record_stmt<DependentMemberPointerAccessExpr>(
                    StmtKind::DependentMemberPointerAccessExpr);
                visit_stmt(node->base.get());
                visit_stmt(node->member_pointer.get());
                return;
            }
            case StmtKind::CppMemberCallExpr: {
                auto* node = static_cast<const CppMemberCallExpr*>(stmt);
                record_stmt<CppMemberCallExpr>(StmtKind::CppMemberCallExpr);
                add_ast_string(node->member_name);
                visit_stmt(node->lowered_call.get());
                return;
            }
            case StmtKind::CppConstructExpr: {
                auto* node = static_cast<const CppConstructExpr*>(stmt);
                record_stmt<CppConstructExpr>(StmtKind::CppConstructExpr);
                visit_symbol(node->ctor_sym);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->args);
                for (const auto& arg : node->args) {
                    visit_stmt(arg.get());
                }
                return;
            }
            case StmtKind::CppValueInitExpr:
                record_stmt<CppValueInitExpr>(StmtKind::CppValueInitExpr);
                return;
            case StmtKind::CppFunctionStyleCastExpr: {
                auto* node =
                    static_cast<const CppFunctionStyleCastExpr*>(stmt);
                record_stmt<CppFunctionStyleCastExpr>(
                    StmtKind::CppFunctionStyleCastExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->args);
                for (const auto& arg : node->args) {
                    visit_stmt(arg.get());
                }
                return;
            }
            case StmtKind::CppImmediateInvocationExpr: {
                auto* node =
                    static_cast<const CppImmediateInvocationExpr*>(stmt);
                record_stmt<CppImmediateInvocationExpr>(
                    StmtKind::CppImmediateInvocationExpr);
                visit_stmt(node->invocation.get());
                return;
            }
            case StmtKind::ParenExpr: {
                auto* node = static_cast<const ParenExpr*>(stmt);
                record_stmt<ParenExpr>(StmtKind::ParenExpr);
                visit_stmt(node->subexpr.get());
                return;
            }
            case StmtKind::CondExpr: {
                auto* node = static_cast<const CondExpr*>(stmt);
                record_stmt<CondExpr>(StmtKind::CondExpr);
                visit_stmt(node->condition.get());
                visit_stmt(node->true_expr.get());
                visit_stmt(node->false_expr.get());
                return;
            }
            case StmtKind::UnaryOperation: {
                auto* node = static_cast<const UnaryOperation*>(stmt);
                record_stmt<UnaryOperation>(StmtKind::UnaryOperation);
                visit_stmt(node->exp.get());
                return;
            }
            case StmtKind::BinaryOperation: {
                auto* node = static_cast<const BinaryOperation*>(stmt);
                record_stmt<BinaryOperation>(StmtKind::BinaryOperation);
                visit_stmt(node->left.get());
                visit_stmt(node->right.get());
                return;
            }
            case StmtKind::CppBuiltinThreeWayCompareExpr: {
                auto* node =
                    static_cast<const CppBuiltinThreeWayCompareExpr*>(stmt);
                record_stmt<CppBuiltinThreeWayCompareExpr>(
                    StmtKind::CppBuiltinThreeWayCompareExpr);
                visit_stmt(node->left.get());
                visit_stmt(node->right.get());
                visit_symbol(node->less_member);
                visit_symbol(node->equivalent_member);
                visit_symbol(node->greater_member);
                visit_symbol(node->unordered_member);
                return;
            }
            case StmtKind::CompoundAssignOperation: {
                auto* node = static_cast<const CompoundAssignOperation*>(stmt);
                record_stmt<CompoundAssignOperation>(StmtKind::CompoundAssignOperation);
                visit_stmt(node->left.get());
                visit_stmt(node->right.get());
                return;
            }
            case StmtKind::ImplicitCast: {
                auto* node = static_cast<const ImplicitCast*>(stmt);
                record_stmt<ImplicitCast>(StmtKind::ImplicitCast);
                visit_stmt(node->expr.get());
                return;
            }
            case StmtKind::ExplicitCast: {
                auto* node = static_cast<const ExplicitCast*>(stmt);
                record_stmt<ExplicitCast>(StmtKind::ExplicitCast);
                visit_stmt(node->expr.get());
                return;
            }
            case StmtKind::ArraySubscriptExpr: {
                auto* node = static_cast<const ArraySubscriptExpr*>(stmt);
                record_stmt<ArraySubscriptExpr>(StmtKind::ArraySubscriptExpr);
                visit_stmt(node->array.get());
                visit_stmt(node->index.get());
                return;
            }
            case StmtKind::MemberExpr: {
                auto* node = static_cast<const MemberExpr*>(stmt);
                record_stmt<MemberExpr>(StmtKind::MemberExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->field_path);
                visit_stmt(node->base.get());
                return;
            }
            case StmtKind::UnresolvedMemberExpr: {
                auto* node = static_cast<const UnresolvedMemberExpr*>(stmt);
                record_stmt<UnresolvedMemberExpr>(StmtKind::UnresolvedMemberExpr);
                add_ast_string(node->member_name);
                if (node->explicit_template_arguments.has_value()) {
                    visit_template_arguments(*node->explicit_template_arguments);
                }
                visit_stmt(node->base.get());
                return;
            }
            case StmtKind::InitListExpr: {
                auto* node = static_cast<const InitListExpr*>(stmt);
                record_stmt<InitListExpr>(StmtKind::InitListExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->elements);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->actions);
                ast_map_storage_lower_bound_bytes_ += map_node_storage_lower_bound_bytes(node->mappings);

                for (const auto& elem : node->elements) {
                    ast_vector_backing_bytes_ += vector_backing_bytes(elem.designators);
                    visit_stmt(elem.value.get());
                    for (const auto& designator : elem.designators) {
                        add_ast_string(designator.field_name);
                        visit_stmt(designator.index.get());
                        visit_stmt(designator.range_end.get());
                    }
                }
                for (const auto& action : node->actions) {
                    ast_vector_backing_bytes_ += vector_backing_bytes(action.paths);
                    for (const auto& path : action.paths) {
                        ast_vector_backing_bytes_ += vector_backing_bytes(path);
                    }
                    visit_stmt(action.value.get());
                }
                for (const auto& kv : node->mappings) {
                    visit_stmt(kv.second.get());
                }
                return;
            }
            case StmtKind::CompoundLiteralExpr: {
                auto* node = static_cast<const CompoundLiteralExpr*>(stmt);
                record_stmt<CompoundLiteralExpr>(StmtKind::CompoundLiteralExpr);
                visit_stmt(node->init.get());
                return;
            }
            case StmtKind::PackExpansionExpr: {
                auto* node = static_cast<const PackExpansionExpr*>(stmt);
                record_stmt<PackExpansionExpr>(StmtKind::PackExpansionExpr);
                visit_stmt(node->pattern.get());
                return;
            }
            case StmtKind::FoldExpr: {
                auto* node = static_cast<const FoldExpr*>(stmt);
                record_stmt<FoldExpr>(StmtKind::FoldExpr);
                visit_stmt(node->pattern.get());
                visit_stmt(node->init.get());
                return;
            }
            case StmtKind::SizeOfExpr: {
                auto* node = static_cast<const SizeOfExpr*>(stmt);
                record_stmt<SizeOfExpr>(StmtKind::SizeOfExpr);
                visit_stmt(node->expr_operand.get());
                return;
            }
            case StmtKind::SizeOfPackExpr: {
                auto* node = static_cast<const SizeOfPackExpr*>(stmt);
                record_stmt<SizeOfPackExpr>(StmtKind::SizeOfPackExpr);
                add_ast_string(node->pack_name);
                return;
            }
            case StmtKind::AlignOfExpr: {
                auto* node = static_cast<const AlignOfExpr*>(stmt);
                record_stmt<AlignOfExpr>(StmtKind::AlignOfExpr);
                visit_stmt(node->expr_operand.get());
                return;
            }
            case StmtKind::CppNoexceptExpr: {
                auto* node = static_cast<const CppNoexceptExpr*>(stmt);
                record_stmt<CppNoexceptExpr>(StmtKind::CppNoexceptExpr);
                visit_stmt(node->operand.get());
                return;
            }
            case StmtKind::OffsetOfExpr: {
                auto* node = static_cast<const OffsetOfExpr*>(stmt);
                record_stmt<OffsetOfExpr>(StmtKind::OffsetOfExpr);
                add_ast_string(node->member_name);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->designator_path);
                for (const auto& comp : node->designator_path) {
                    add_ast_string(comp.field_name);
                }
                return;
            }
            case StmtKind::GenericExpr: {
                auto* node = static_cast<const GenericExpr*>(stmt);
                record_stmt<GenericExpr>(StmtKind::GenericExpr);
                visit_stmt(node->controlling_expr.get());
                ast_vector_backing_bytes_ += vector_backing_bytes(node->associations);
                for (const auto& assoc : node->associations) {
                    visit_stmt(assoc.expr.get());
                }
                return;
            }
            case StmtKind::StmtExpr: {
                auto* node = static_cast<const StmtExpr*>(stmt);
                record_stmt<StmtExpr>(StmtKind::StmtExpr);
                visit_stmt(node->compound_stmt.get());
                return;
            }
            case StmtKind::VaArgExpr: {
                auto* node = static_cast<const VaArgExpr*>(stmt);
                record_stmt<VaArgExpr>(StmtKind::VaArgExpr);
                visit_stmt(node->va_list_expr.get());
                return;
            }
            case StmtKind::VaStartExpr: {
                auto* node = static_cast<const VaStartExpr*>(stmt);
                record_stmt<VaStartExpr>(StmtKind::VaStartExpr);
                visit_stmt(node->va_list_expr.get());
                visit_stmt(node->last_param.get());
                return;
            }
            case StmtKind::VaEndExpr: {
                auto* node = static_cast<const VaEndExpr*>(stmt);
                record_stmt<VaEndExpr>(StmtKind::VaEndExpr);
                visit_stmt(node->va_list_expr.get());
                return;
            }
            case StmtKind::VaCopyExpr: {
                auto* node = static_cast<const VaCopyExpr*>(stmt);
                record_stmt<VaCopyExpr>(StmtKind::VaCopyExpr);
                visit_stmt(node->dest.get());
                visit_stmt(node->src.get());
                return;
            }
            case StmtKind::BuiltinCallExpr: {
                auto* node = static_cast<const BuiltinCallExpr*>(stmt);
                record_stmt<BuiltinCallExpr>(StmtKind::BuiltinCallExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->args);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->type_args);
                for (const auto& arg : node->args) {
                    visit_stmt(arg.get());
                }
                return;
            }
            case StmtKind::ConceptSpecializationExpr: {
                auto* node = static_cast<const ConceptSpecializationExpr*>(stmt);
                record_stmt<ConceptSpecializationExpr>(
                    StmtKind::ConceptSpecializationExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->arguments);
                add_ast_string(node->concept_name);
                return;
            }
            case StmtKind::RequiresExpr: {
                auto* node = static_cast<const RequiresExpr*>(stmt);
                record_stmt<RequiresExpr>(StmtKind::RequiresExpr);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->parameters);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->requirements);
                for (const auto& parameter : node->parameters) {
                    visit_decl(parameter.get());
                }
                for (const auto& requirement : node->requirements) {
                    visit_stmt(requirement.expr.get());
                    if (requirement.return_type_constraint) {
                        add_ast_string(
                            requirement.return_type_constraint->concept_name);
                        visit_template_arguments(
                            requirement.return_type_constraint
                                ->template_arguments);
                    }
                }
                return;
            }
            case StmtKind::CppTypeIdExpr: {
                auto* node = static_cast<const CppTypeIdExpr*>(stmt);
                record_stmt<CppTypeIdExpr>(StmtKind::CppTypeIdExpr);
                visit_stmt(node->expr_operand.get());
                return;
            }
            case StmtKind::CppDynamicCastExpr: {
                auto* node = static_cast<const CppDynamicCastExpr*>(stmt);
                record_stmt<CppDynamicCastExpr>(StmtKind::CppDynamicCastExpr);
                visit_stmt(node->expr.get());
                return;
            }
            case StmtKind::CppThrowExpr: {
                auto* node = static_cast<const CppThrowExpr*>(stmt);
                record_stmt<CppThrowExpr>(StmtKind::CppThrowExpr);
                visit_stmt(node->thrown_expr.get());
                return;
            }
            case StmtKind::CppNewExpr: {
                auto* node = static_cast<const CppNewExpr*>(stmt);
                record_stmt<CppNewExpr>(StmtKind::CppNewExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->placement_args);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->constructor_args);
                for (const auto& arg : node->placement_args) {
                    visit_stmt(arg.get());
                }
                visit_stmt(node->initializer.get());
                for (const auto& arg : node->constructor_args) {
                    visit_stmt(arg.get());
                }
                return;
            }
            case StmtKind::CppDeleteExpr: {
                auto* node = static_cast<const CppDeleteExpr*>(stmt);
                record_stmt<CppDeleteExpr>(StmtKind::CppDeleteExpr);
                visit_stmt(node->operand.get());
                return;
            }
            case StmtKind::CppPseudoDestructorExpr: {
                auto* node = static_cast<const CppPseudoDestructorExpr*>(stmt);
                record_stmt<CppPseudoDestructorExpr>(
                    StmtKind::CppPseudoDestructorExpr);
                visit_symbol(node->destructor_sym);
                visit_stmt(node->base.get());
                return;
            }
            case StmtKind::BlockExpr: {
                auto* node = static_cast<const BlockExpr*>(stmt);
                record_stmt<BlockExpr>(StmtKind::BlockExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->semantic_info.captures);
                for (const auto& capture : node->semantic_info.captures) {
                    add_ast_string(capture.name);
                    visit_symbol(capture.symbol);
                }
                if (node->semantic_info.literal_semantic_decl) {
                    visit_decl(node->semantic_info.literal_semantic_decl.get());
                }
                if (node->semantic_info.invoke_decl) {
                    visit_decl(node->semantic_info.invoke_decl.get());
                }
                visit_stmt(node->body.get());
                return;
            }
            case StmtKind::CppLambdaExpr: {
                auto* node = static_cast<const CppLambdaExpr*>(stmt);
                record_stmt<CppLambdaExpr>(StmtKind::CppLambdaExpr);
                ast_vector_backing_bytes_ += vector_backing_bytes(node->parameters);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->closure_info.captures);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->semantic_info.capture_fields);
                ast_vector_backing_bytes_ +=
                    vector_backing_bytes(node->semantic_info.capture_initializers);
                for (const auto& capture : node->closure_info.captures) {
                    add_ast_string(capture.name);
                    visit_symbol(capture.symbol);
                }
                for (const auto& capture_init :
                     node->semantic_info.capture_initializers) {
                    visit_stmt(capture_init.get());
                }
                visit_stmt(node->semantic_info.closure_initializer.get());
                if (node->semantic_info.closure_semantic_decl) {
                    visit_decl(node->semantic_info.closure_semantic_decl.get());
                }
                if (node->semantic_info.closure_record_decl) {
                    visit_decl(node->semantic_info.closure_record_decl.get());
                }
                if (node->semantic_info.function_pointer_invoker_decl) {
                    visit_decl(node->semantic_info.function_pointer_invoker_decl.get());
                }
                for (const auto& param : node->parameters) {
                    visit_decl(param.get());
                }
                visit_stmt(node->template_requires_clause.get());
                visit_stmt(node->trailing_requires_clause.get());
                visit_stmt(node->body.get());
                return;
            }
            case StmtKind::ErrorExpr: {
                auto* node = static_cast<const ErrorExpr*>(stmt);
                record_stmt<ErrorExpr>(StmtKind::ErrorExpr);
                add_ast_string(node->error_message);
                return;
            }
            default:
                return;
        }
    }

    const ASTContext& ast_ctx_;

    std::array<uint64_t, static_cast<size_t>(StmtKind::LastExpr) + 1> stmt_counts_{};
    std::array<uint64_t, static_cast<size_t>(StmtKind::LastExpr) + 1> stmt_inline_bytes_{};
    std::array<uint64_t, static_cast<size_t>(DeclKind::ErrorDecl) + 1> decl_counts_{};
    std::array<uint64_t, static_cast<size_t>(DeclKind::ErrorDecl) + 1> decl_inline_bytes_{};

    uint64_t ast_string_heap_bytes_ = 0;
    uint64_t ast_vector_backing_bytes_ = 0;
    uint64_t ast_map_storage_lower_bound_bytes_ = 0;
    uint64_t ast_unordered_set_bucket_bytes_ = 0;

    uint64_t symbol_count_ = 0;
    uint64_t symbol_inline_bytes_ = 0;
    uint64_t symbol_string_heap_bytes_ = 0;
    uint64_t symbol_vector_backing_bytes_ = 0;

    std::unordered_set<const Stmt*> seen_stmts_;
    std::unordered_set<const Decl*> seen_decls_;
    std::unordered_set<const Symbol*> seen_symbols_;
};

std::vector<KindRow> collect_stmt_rows(const ASTMemoryAnalyzer& analyzer) {
    std::vector<KindRow> rows;
    for (StmtKind kind : kAllStmtKinds) {
        const auto idx = static_cast<size_t>(kind);
        const auto count = analyzer.stmt_counts()[idx];
        if (count == 0) {
            continue;
        }
        rows.push_back({stmt_kind_name(kind), count, analyzer.stmt_inline_bytes()[idx]});
    }
    std::sort(rows.begin(), rows.end(),
        [](const KindRow& lhs, const KindRow& rhs) {
            if (lhs.inline_bytes != rhs.inline_bytes) {
                return lhs.inline_bytes > rhs.inline_bytes;
            }
            if (lhs.count != rhs.count) {
                return lhs.count > rhs.count;
            }
            return lhs.name < rhs.name;
        });
    return rows;
}

std::vector<KindRow> collect_decl_rows(const ASTMemoryAnalyzer& analyzer) {
    std::vector<KindRow> rows;
    for (DeclKind kind : kAllDeclKinds) {
        const auto idx = static_cast<size_t>(kind);
        const auto count = analyzer.decl_counts()[idx];
        if (count == 0) {
            continue;
        }
        rows.push_back({decl_kind_name(kind), count, analyzer.decl_inline_bytes()[idx]});
    }
    std::sort(rows.begin(), rows.end(),
        [](const KindRow& lhs, const KindRow& rhs) {
            if (lhs.inline_bytes != rhs.inline_bytes) {
                return lhs.inline_bytes > rhs.inline_bytes;
            }
            if (lhs.count != rhs.count) {
                return lhs.count > rhs.count;
            }
            return lhs.name < rhs.name;
        });
    return rows;
}

void print_kind_rows(std::ostream& os, const std::vector<KindRow>& rows) {
    if (rows.empty()) {
        os << "  (none)\n";
        return;
    }
    os << "  " << std::left << std::setw(30) << "kind"
       << std::right << std::setw(12) << "count"
       << std::setw(18) << "inline bytes\n";
    for (const auto& row : rows) {
        os << "  " << std::left << std::setw(30) << row.name
           << std::right << std::setw(12) << row.count
           << std::setw(18) << row.inline_bytes << "\n";
    }
}

} // namespace

void print_ast_memory_report(std::ostream& os, const Decl* root, const ASTContext& ast_ctx) {
    ASTMemoryAnalyzer analyzer(ast_ctx);
    analyzer.analyze(root);

    const auto stmt_rows = collect_stmt_rows(analyzer);
    const auto decl_rows = collect_decl_rows(analyzer);

    uint64_t stmt_count_total = 0;
    uint64_t stmt_inline_total = 0;
    for (const auto& row : stmt_rows) {
        stmt_count_total += row.count;
        stmt_inline_total += row.inline_bytes;
    }

    uint64_t decl_count_total = 0;
    uint64_t decl_inline_total = 0;
    for (const auto& row : decl_rows) {
        decl_count_total += row.count;
        decl_inline_total += row.inline_bytes;
    }

    const uint64_t ast_inline_total = stmt_inline_total + decl_inline_total;
    const uint64_t identifier_pool_bytes = ast_ctx.identifier_pool_memory_usage_bytes();
    const uint64_t ast_dynamic_total =
        analyzer.ast_string_heap_bytes() +
        identifier_pool_bytes +
        analyzer.ast_vector_backing_bytes() +
        analyzer.ast_map_storage_lower_bound_bytes() +
        analyzer.ast_unordered_set_bucket_bytes();

    const uint64_t attr_side_table_bytes = ast_ctx.attr_table_memory_usage_bytes();
    const uint64_t bitfield_side_table_bytes = ast_ctx.bitfield_table_memory_usage_bytes();
    const uint64_t cpp_member_side_table_bytes =
        ast_ctx.cpp_member_decl_info_table_memory_usage_bytes();
    const uint64_t cpp_variable_dtor_side_table_bytes =
        ast_ctx.cpp_variable_destructor_table_memory_usage_bytes();
    const uint64_t cpp_virtual_call_side_table_bytes =
        ast_ctx.cpp_virtual_call_info_table_memory_usage_bytes();
    const uint64_t cpp_lambda_closure_side_table_bytes =
        ast_ctx.cpp_lambda_closure_decl_info_table_memory_usage_bytes();
    const uint64_t cpp_lambda_invoker_side_table_bytes =
        ast_ctx.cpp_lambda_invoker_info_table_memory_usage_bytes();
    const uint64_t side_table_total =
        attr_side_table_bytes +
        bitfield_side_table_bytes +
        cpp_member_side_table_bytes +
        cpp_variable_dtor_side_table_bytes +
        cpp_virtual_call_side_table_bytes +
        cpp_lambda_closure_side_table_bytes +
        cpp_lambda_invoker_side_table_bytes;
    const uint64_t ast_total_estimate = ast_inline_total + ast_dynamic_total + side_table_total;

    const uint64_t symbol_dynamic_total =
        analyzer.symbol_string_heap_bytes() + analyzer.symbol_vector_backing_bytes();
    const uint64_t symbol_total_estimate =
        analyzer.symbol_inline_bytes() + symbol_dynamic_total;
    const uint64_t combined_total_estimate = ast_total_estimate + symbol_total_estimate;

    os << "=== AST Memory Report (best-effort estimate) ===\n";
    os << "Notes:\n";
    os << "  - Dynamic estimates are approximate and based on container/string capacities.\n";
    os << "  - DenseMap side-table memory includes bucket storage.\n";
    os << "  - Identifier interning pool memory is estimated from pool buckets and string capacities.\n";
    os << "\n";

    os << "Stmt Nodes By Kind:\n";
    print_kind_rows(os, stmt_rows);
    os << "\n";

    os << "Decl Nodes By Kind:\n";
    print_kind_rows(os, decl_rows);
    os << "\n";

    os << "AST Totals:\n";
    os << "  stmt nodes                    : " << stmt_count_total << "\n";
    os << "  decl nodes                    : " << decl_count_total << "\n";
    os << "  node inline bytes             : " << format_bytes(ast_inline_total) << "\n";
    os << "  string heap estimate          : " << format_bytes(analyzer.ast_string_heap_bytes()) << "\n";
    os << "  identifier pool estimate      : " << format_bytes(identifier_pool_bytes) << "\n";
    os << "  vector backing estimate       : " << format_bytes(analyzer.ast_vector_backing_bytes()) << "\n";
    os << "  map storage lower bound       : " << format_bytes(analyzer.ast_map_storage_lower_bound_bytes()) << "\n";
    os << "  unordered_set bucket estimate : " << format_bytes(analyzer.ast_unordered_set_bucket_bytes()) << "\n";
    os << "  side table bytes              : " << format_bytes(side_table_total) << "\n";
    os << "  AST total estimate            : " << format_bytes(ast_total_estimate) << "\n";
    os << "\n";

    os << "ASTContext Side Tables:\n";
    os << "  attr table entries/capacity   : " << ast_ctx.attr_table_size()
       << "/" << ast_ctx.attr_table_capacity()
       << " (" << format_bytes(attr_side_table_bytes) << ")\n";
    os << "  bitfield table entries/capacity: " << ast_ctx.bitfield_table_size()
       << "/" << ast_ctx.bitfield_table_capacity()
       << " (" << format_bytes(bitfield_side_table_bytes) << ")\n";
    os << "  c++ member table entries/capacity: " << ast_ctx.cpp_member_decl_info_table_size()
       << "/" << ast_ctx.cpp_member_decl_info_table_capacity()
       << " (" << format_bytes(cpp_member_side_table_bytes) << ")\n";
    os << "  c++ dtor table entries/capacity : " << ast_ctx.cpp_variable_destructor_table_size()
       << "/" << ast_ctx.cpp_variable_destructor_table_capacity()
       << " (" << format_bytes(cpp_variable_dtor_side_table_bytes) << ")\n";
    os << "  c++ virtual call table entries/capacity: "
       << ast_ctx.cpp_virtual_call_info_table_size()
       << "/" << ast_ctx.cpp_virtual_call_info_table_capacity()
       << " (" << format_bytes(cpp_virtual_call_side_table_bytes) << ")\n";
    os << "  c++ lambda closure table entries/capacity: "
       << ast_ctx.cpp_lambda_closure_decl_info_table_size()
       << "/" << ast_ctx.cpp_lambda_closure_decl_info_table_capacity()
       << " (" << format_bytes(cpp_lambda_closure_side_table_bytes) << ")\n";
    os << "  c++ lambda invoker table entries/capacity: "
       << ast_ctx.cpp_lambda_invoker_info_table_size()
       << "/" << ast_ctx.cpp_lambda_invoker_info_table_capacity()
       << " (" << format_bytes(cpp_lambda_invoker_side_table_bytes) << ")\n";
    os << "\n";

    os << "Identifier Intern Pool:\n";
    os << "  entries                       : " << ast_ctx.identifier_pool_size() << "\n";
    os << "  string storage estimate       : " << format_bytes(ast_ctx.identifier_pool_string_storage_bytes()) << "\n";
    os << "  pool total estimate           : " << format_bytes(identifier_pool_bytes) << "\n";
    os << "\n";

    os << "Referenced Symbols (supplemental, not strictly AST):\n";
    os << "  unique symbols                : " << analyzer.symbol_count() << "\n";
    os << "  symbol inline bytes           : " << format_bytes(analyzer.symbol_inline_bytes()) << "\n";
    os << "  symbol dynamic estimate       : " << format_bytes(symbol_dynamic_total) << "\n";
    os << "  symbols total estimate        : " << format_bytes(symbol_total_estimate) << "\n";
    os << "\n";

    os << "Combined Estimate (AST + referenced symbols): "
       << format_bytes(combined_total_estimate) << "\n";
    os << "==============================================\n";
}
