#ifndef ABURI_MANGLE_H
#define ABURI_MANGLE_H

#include <string>
#include <string_view>

#include "../ast/ast.h"
#include "../ast/symbols.h"
#include "abi_policy.h"

// Preliminary Itanium mangler entry point for function symbols.
// This currently covers a narrow subset and is intended to be expanded later.
std::string mangle_function_name_itanium(const std::string& name,
                                         const QualType& function_type,
                                         const AbiPolicy& policy);

// Preliminary Itanium mangler entry point for function symbols.
// This currently covers a narrow subset and is intended to be expanded later.
std::string mangle_function_name_itanium(const FuncDecl& decl, const AbiPolicy& policy);

// Type-name encoding used by Itanium RTTI symbols (_ZTI/_ZTS).
std::string mangle_type_name_itanium(const QualType& type);

// Dispatch helper based on AbiPolicy.
std::string mangle_function_name_for_policy(const std::string& name,
                                            const QualType& function_type,
                                            const AbiPolicy& policy);

// Dispatch helper based on AbiPolicy.
std::string mangle_function_name_for_policy(const FuncDecl& decl, const AbiPolicy& policy);

struct ResolvedFunctionName {
    std::string name;
    bool from_asm_label = false;
};

ResolvedFunctionName resolve_function_linkage_name(
    const std::string& name,
    const QualType& function_type,
    LanguageLinkage language_linkage,
    const AbiPolicy& policy,
    const std::string* asm_label = nullptr);

ResolvedFunctionName resolve_function_linkage_name(const FuncDecl& decl,
                                                   const AbiPolicy& policy);

ResolvedFunctionName resolve_function_linkage_name(const Symbol& sym,
                                                   const AbiPolicy& policy,
                                                   std::string_view fallback_spelling = {});

struct ResolvedVariableName {
    std::string name;
    bool from_asm_label = false;
};

ResolvedVariableName resolve_variable_linkage_name(const VariableDecl& decl,
                                                   const AbiPolicy& policy);

ResolvedVariableName resolve_variable_linkage_name(
    const Symbol& sym,
    const AbiPolicy& policy,
    std::string_view fallback_spelling = {});

#endif // ABURI_MANGLE_H
