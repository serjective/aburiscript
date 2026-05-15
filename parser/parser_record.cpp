#include "parser.h"
#include "cpp_out_of_line_match.h"

#include "../helpers/auto_type_utils.h"
#include "../ast/ast_clone.h"
#include "../ast/expr_clone.h"
#include "../collect/lookup_engine.h"
#include "../collect/collect_templates_internal.h"
#include "../helpers/qualified_name_utils.h"
#include "../ast/special_members.h"
#include <functional>
#include <cstdint>
#include <limits>
#include <set>
#include <type_traits>

bool is_c23_family_standard(const std::string& std_name);

namespace {
std::shared_ptr<BuiltinType> fixed_enum_integer_underlying_type(
    const std::shared_ptr<CType>& type,
    const ASTContext* ast_ctx = nullptr) {
    QualType resolved = desugar_type(QualType(type), ast_ctx);
    for (int depth = 0; depth < 8 && resolved; ++depth) {
        auto transform = dyn_cast_shared<BuiltinTypeTransformType>(
            resolved.get_shared());
        if (!transform) {
            break;
        }
        resolved = desugar_type(
            apply_builtin_type_transform(
                transform->transform_kind,
                transform->operand_type,
                ast_ctx),
            ast_ctx);
    }

    auto builtin = dyn_cast_shared<BuiltinType>(resolved.get_shared());
    if (!builtin || !builtin->isInteger()) {
        return nullptr;
    }
    return builtin;
}

bool is_valid_fixed_enum_underlying_type(
    const std::shared_ptr<CType>& type,
    const ASTContext* ast_ctx = nullptr) {
    return fixed_enum_integer_underlying_type(type, ast_ctx) != nullptr;
}

bool fixed_enum_value_fits_underlying(
    int64_t value,
    const std::shared_ptr<CType>& underlying,
    const ASTContext* ast_ctx = nullptr) {
    auto builtin = fixed_enum_integer_underlying_type(underlying, ast_ctx);
    if (!builtin) {
        return false;
    }
    if (builtin->builtin_kind == BuiltinTypes::Bool) {
        return value == 0 || value == 1;
    }
    int64_t bits = builtin->getWidth();
    if (bits <= 0) {
        return false;
    }
    if (builtin->isUnsigned()) {
        if (value < 0) {
            return false;
        }
        if (bits >= 64) {
            return true;
        }
        uint64_t maxv = (uint64_t{1} << static_cast<uint64_t>(bits)) - 1;
        return static_cast<uint64_t>(value) <= maxv;
    }
    if (bits >= 64) {
        return true;
    }
    int64_t minv = -(int64_t{1} << (bits - 1));
    int64_t maxv = (int64_t{1} << (bits - 1)) - 1;
    return value >= minv && value <= maxv;
}

bool can_parse_cxx_object_initializer_syntax(QualType declared_type) {
    if (!declared_type) {
        return false;
    }
    auto placeholder_specialization =
        dyn_cast_shared<TemplateSpecializationType>(
            desugar_typedefs(declared_type).get_shared());
    if (placeholder_specialization &&
        placeholder_specialization->is_class_template_placeholder) {
        return true;
    }
    if (type_depends_on_template_parameters(declared_type)) {
        return true;
    }
    return canonical_type_kind(declared_type) == TypeKind::Object;
}

bool is_defaultable_special_member_method(
    const CppMethodDecl* method_decl,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!method_decl || !owner_type || !ast_ctx) {
        return false;
    }
    if (method_decl->storage_class == StorageClass::STATIC ||
        method_decl->name != "operator=") {
        return false;
    }
    size_t user_param_start = 0;
    if (!method_decl->parameters.empty()) {
        auto* first_param =
            dyn_cast<ParamDecl>(method_decl->parameters.front().get());
        if (first_param && first_param->get_name() == "this") {
            user_param_start = 1;
        }
    }
    if (method_decl->parameters.size() != user_param_start + 1) {
        return false;
    }
    QualType canonical_owner =
        remove_reference(owner_type, ast_ctx).without_qualifiers();
    auto* parameter_decl =
        dyn_cast<ParamDecl>(method_decl->parameters[user_param_start].get());
    QualType parameter_type =
        parameter_decl ? parameter_decl->type : QualType();
    if (!parameter_type) {
        return false;
    }
    QualType canonical_parameter =
        remove_reference(parameter_type, ast_ctx).without_qualifiers();
    return canonical_parameter.equals_unqualified(canonical_owner);
}

bool is_defaulted_comparison_operator_name(const std::string& name) {
    return name == "operator==" ||
           name == "operator!=" ||
           name == "operator<" ||
           name == "operator<=" ||
           name == "operator>" ||
           name == "operator>=" ||
           name == "operator<=>";
}

bool is_defaulted_secondary_comparison_operator_name(const std::string& name) {
    return name == "operator!=" ||
           name == "operator<" ||
           name == "operator<=" ||
           name == "operator>" ||
           name == "operator>=";
}

bool defaulted_comparison_parameter_matches_owner(
    QualType parameter_type,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!parameter_type || !owner_type || !ast_ctx) {
        return false;
    }
    QualType canonical_parameter =
        remove_reference(parameter_type, ast_ctx).without_qualifiers();
    QualType canonical_owner =
        remove_reference(owner_type, ast_ctx).without_qualifiers();
    return canonical_parameter.equals_unqualified(canonical_owner);
}

bool defaulted_comparison_return_type_is_valid(
    const std::string& name,
    QualType return_type,
    const ASTContext* ast_ctx) {
    if (!return_type || !ast_ctx) {
        return false;
    }
    QualType canonical_return = desugar_type(return_type, ast_ctx);
    auto auto_return = canonical_return.as_shared<AutoType>();
    if (name == "operator<=>") {
        return auto_return || !return_type->isVoid();
    }
    if (auto_return) {
        return false;
    }
    if (is_defaulted_secondary_comparison_operator_name(name) ||
        name == "operator==") {
        auto builtin = canonical_return.as_shared<BuiltinType>();
        return builtin && builtin->builtin_kind == BuiltinTypes::Bool;
    }
    return false;
}

bool is_defaultable_comparison_method(
    const CppMethodDecl* method_decl,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!method_decl || !owner_type || !ast_ctx ||
        !is_defaulted_comparison_operator_name(method_decl->name) ||
        method_decl->storage_class == StorageClass::STATIC) {
        return false;
    }
    auto function_type = QualType(method_decl->type).as_shared<FunctionType>();
    if (!function_type ||
        !defaulted_comparison_return_type_is_valid(
            method_decl->name,
            function_type->ret_type,
            ast_ctx)) {
        return false;
    }
    size_t user_param_start = 0;
    if (!method_decl->parameters.empty()) {
        auto* first_param =
            dyn_cast<ParamDecl>(method_decl->parameters.front().get());
        if (first_param && first_param->get_name() == "this") {
            user_param_start = 1;
        }
    }
    if (method_decl->parameters.size() != user_param_start + 1 ||
        function_type->parameters.size() != method_decl->parameters.size()) {
        return false;
    }
    if (user_param_start != 0) {
        auto this_param =
            function_type->parameters.front().as_shared<PointerType>();
        if (!this_param ||
            !defaulted_comparison_parameter_matches_owner(
                this_param->pointed_type,
                owner_type,
                ast_ctx)) {
            return false;
        }
    }
    auto* parameter_decl =
        dyn_cast<ParamDecl>(method_decl->parameters[user_param_start].get());
    return parameter_decl &&
           defaulted_comparison_parameter_matches_owner(
               parameter_decl->type,
               owner_type,
               ast_ctx);
}

bool is_defaultable_comparison_function(
    const FuncDecl* function_decl,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    if (!function_decl || !owner_type || !ast_ctx ||
        !is_defaulted_comparison_operator_name(function_decl->name)) {
        return false;
    }
    auto function_type = QualType(function_decl->type).as_shared<FunctionType>();
    if (!function_type ||
        function_type->parameters.size() != 2 ||
        function_decl->parameters.size() != 2 ||
        !defaulted_comparison_return_type_is_valid(
            function_decl->name,
            function_type->ret_type,
            ast_ctx)) {
        return false;
    }
    for (const auto& parameter : function_decl->parameters) {
        auto* parameter_decl = dyn_cast<ParamDecl>(parameter.get());
        if (!parameter_decl ||
            !defaulted_comparison_parameter_matches_owner(
                parameter_decl->type,
                owner_type,
                ast_ctx)) {
            return false;
        }
    }
    return true;
}

bool is_defaultable_method(
    const CppMethodDecl* method_decl,
    QualType owner_type,
    const ASTContext* ast_ctx) {
    return is_defaultable_special_member_method(method_decl, owner_type, ast_ctx) ||
           is_defaultable_comparison_method(method_decl, owner_type, ast_ctx);
}

std::shared_ptr<CType> choose_default_enum_underlying(
    TypeContext* type_ctx, int64_t min_value, int64_t max_value, bool prefer_smallest_width = false) {
    if (!type_ctx) {
        return nullptr;
    }

    auto fits_signed = [&](BuiltinTypes kind) -> bool {
        auto t = type_ctx->get_builtin(kind);
        if (!t) {
            return false;
        }
        int64_t bits = t->getWidth();
        if (bits <= 0) {
            return false;
        }
        if (bits >= 64) {
            return true;
        }
        int64_t minv = -(int64_t{1} << (bits - 1));
        int64_t maxv = (int64_t{1} << (bits - 1)) - 1;
        return min_value >= minv && max_value <= maxv;
    };

    auto fits_unsigned = [&](BuiltinTypes kind) -> bool {
        if (min_value < 0) {
            return false;
        }
        auto t = type_ctx->get_builtin(kind);
        if (!t) {
            return false;
        }
        int64_t bits = t->getWidth();
        if (bits <= 0) {
            return false;
        }
        if (bits >= 64) {
            return true;
        }
        uint64_t maxv = (uint64_t{1} << static_cast<uint64_t>(bits)) - 1;
        return static_cast<uint64_t>(max_value) <= maxv;
    };

    if (prefer_smallest_width) {
        if (min_value < 0) {
            if (fits_signed(BuiltinTypes::SChar)) return type_ctx->get_builtin(BuiltinTypes::SChar);
            if (fits_signed(BuiltinTypes::Short)) return type_ctx->get_builtin(BuiltinTypes::Short);
            if (fits_signed(BuiltinTypes::Int)) return type_ctx->get_builtin(BuiltinTypes::Int);
            if (fits_signed(BuiltinTypes::Long)) return type_ctx->get_builtin(BuiltinTypes::Long);
            return type_ctx->get_builtin(BuiltinTypes::LongLong);
        }

        if (fits_unsigned(BuiltinTypes::UChar)) return type_ctx->get_builtin(BuiltinTypes::UChar);
        if (fits_unsigned(BuiltinTypes::UShort)) return type_ctx->get_builtin(BuiltinTypes::UShort);
        if (fits_unsigned(BuiltinTypes::UInt)) return type_ctx->get_builtin(BuiltinTypes::UInt);
        if (fits_unsigned(BuiltinTypes::ULong)) return type_ctx->get_builtin(BuiltinTypes::ULong);
        return type_ctx->get_builtin(BuiltinTypes::ULongLong);
    }

    if (min_value < 0) {
        if (fits_signed(BuiltinTypes::Int)) return type_ctx->get_builtin(BuiltinTypes::Int);
        if (fits_signed(BuiltinTypes::Long)) return type_ctx->get_builtin(BuiltinTypes::Long);
        return type_ctx->get_builtin(BuiltinTypes::LongLong);
    }

    // Match Clang/GCC C enum compatibility on this target: non-negative enums
    // use an unsigned compatible integer type at the natural rank.
    if (fits_unsigned(BuiltinTypes::UInt)) return type_ctx->get_builtin(BuiltinTypes::UInt);
    if (fits_unsigned(BuiltinTypes::ULong)) return type_ctx->get_builtin(BuiltinTypes::ULong);
    return type_ctx->get_builtin(BuiltinTypes::ULongLong);
}

bool enum_constant_fits_int(TypeContext* type_ctx, int64_t value) {
    if (!type_ctx) {
        return false;
    }
    auto int_type = type_ctx->get_builtin(BuiltinTypes::Int);
    return fixed_enum_value_fits_underlying(value, int_type);
}

bool has_packed_attr(const std::vector<ParsedAttribute>& attrs) {
    for (const auto& attr : attrs) {
        if (attr.canonical_name() == "packed") {
            return true;
        }
    }
    return false;
}
static const char* cpp_record_kind_spelling(CppRecordKind kind) {
    switch (kind) {
        case CppRecordKind::Class: return "class";
        case CppRecordKind::Struct: return "struct";
        case CppRecordKind::Union: return "union";
    }
    return "record";
}

static RecordMemberAccess encode_cpp_access(CppAccessSpecifier access) {
    switch (access) {
        case CppAccessSpecifier::Public: return RecordMemberAccess::Public;
        case CppAccessSpecifier::Protected: return RecordMemberAccess::Protected;
        case CppAccessSpecifier::Private: return RecordMemberAccess::Private;
        case CppAccessSpecifier::None: break;
    }
    return RecordMemberAccess::Public;
}

static std::string cpp_base_specifier_name(const CppBaseSpecifier& base_spec) {
    if (!base_spec.type_name.empty()) {
        return base_spec.type_name;
    }
    return base_spec.type ? base_spec.type.to_string() : std::string();
}

static const ObjectDecl* cpp_base_record_decl_from_type(QualType base_type) {
    auto base_object = desugar_type(base_type).as_shared<ObjectType>();
    return base_object ? dyn_cast<ObjectDecl>(base_object->get_decl()) : nullptr;
}

static bool cpp_base_type_is_dependent(QualType base_type) {
    auto dependent_base_raw = desugar_type(base_type).get_shared();
    if (!dependent_base_raw) {
        return false;
    }

    if (dependent_base_raw->kind == TypeKind::TemplateTypeParm ||
        dependent_base_raw->kind == TypeKind::DependentName) {
        return true;
    }

    if (auto specialization =
            dyn_cast_shared<TemplateSpecializationType>(dependent_base_raw)) {
        return specialization->is_dependent;
    }

    return false;
}

static bool template_argument_names_template_parameter(
    const TemplateArgument& argument,
    const TemplateParameterDecl* parameter) {
    if (!parameter) {
        return false;
    }

    if (auto* type_parameter =
            dyn_cast<TemplateTypeParmDecl>(const_cast<TemplateParameterDecl*>(parameter))) {
        if (argument.kind != TemplateArgumentKind::Type) {
            return false;
        }
        auto argument_type =
            desugar_type(argument.type).as_shared<TemplateTypeParmType>();
        if (!argument_type) {
            return false;
        }
        if (argument_type->parameter_decl) {
            return argument_type->parameter_decl == type_parameter;
        }
        return argument_type->depth == type_parameter->depth &&
               argument_type->index == type_parameter->index;
    }

    if (auto* value_parameter =
            dyn_cast<TemplateNonTypeParmDecl>(const_cast<TemplateParameterDecl*>(parameter))) {
        if (argument.kind != TemplateArgumentKind::Value) {
            return false;
        }
        if (argument.referenced_parameter == value_parameter) {
            return true;
        }
        auto* value_ref = dyn_cast<VarRef>(
            Collect::strip_implicit_casts(argument.value_expr.get()));
        return value_ref &&
               value_ref->symref &&
               value_ref->symref->template_parameter_decl == value_parameter;
    }

    if (auto* template_parameter =
            dyn_cast<TemplateTemplateParmDecl>(const_cast<TemplateParameterDecl*>(parameter))) {
        return argument.kind == TemplateArgumentKind::Template &&
               argument.referenced_parameter == template_parameter;
    }

    return false;
}

static bool cpp_base_type_is_current_instantiation(QualType base_type) {
    auto specialization =
        dyn_cast_shared<TemplateSpecializationType>(
            desugar_type(base_type).get_shared());
    auto* class_template =
        specialization
            ? dyn_cast<ClassTemplateDecl>(
                  const_cast<Decl*>(specialization->primary_template))
            : nullptr;
    if (!class_template ||
        specialization->arguments.size() != class_template->parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < specialization->arguments.size(); ++idx) {
        if (!template_argument_names_template_parameter(
                specialization->arguments[idx],
                class_template->parameters[idx].get())) {
            return false;
        }
    }
    return true;
}

// Virtual slot keying: two methods occupy the same vtable slot iff they have
// the same name, cv-qualifiers on the implicit this pointer, ref-qualifiers,
// and user parameter types.  Return type is NOT part of the key because
// covariant returns are allowed and checked separately.  Variadic status IS
// part of the key.  Shared canonicalization lives in make_cpp_virtual_slot_key().
static std::string make_virtual_slot_key(
    const std::string& method_name, QualType method_type) {
    return make_cpp_virtual_slot_key(method_name, method_type);
}

static const ObjectDecl* canonical_cpp_record_decl(const ObjectDecl* decl) {
    if (!decl) {
        return nullptr;
    }
    if (auto record_type = decl->get_record_type()) {
        if (auto* canonical_decl =
                dyn_cast<ObjectDecl>(record_type->get_decl())) {
            return canonical_decl;
        }
    }
    return decl;
}

// Diamond inheritance path resolution for covariant return validation.
// Each path from derived to base is encoded as a sequence of steps
// (Normal:decl_ptr or Virtual:decl_ptr).  Key insight: when a path
// reaches a virtual base, we reset the path to just that virtual base —
// this reflects the C++ rule that all paths to a virtual base lead to
// the SAME shared subobject.  Non-virtual paths to the same base may
// lead to different subobjects (different offsets), so they are distinct.
// If more than one unique path reaches the target, the base is ambiguous.
using BasePathStep = std::pair<const ObjectDecl*, bool>; // bool = via virtual edge

static std::string encode_base_path_key(
    const std::vector<BasePathStep>& path) {
    std::string key;
    key.reserve(path.size() * 24);
    for (const auto& step : path) {
        key += step.second ? "V:" : "N:";
        key +=
            std::to_string(reinterpret_cast<uintptr_t>(step.first));
        key.push_back(';');
    }
    return key;
}

static size_t count_public_base_subobjects(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl) {
    derived_decl = canonical_cpp_record_decl(derived_decl);
    target_base_decl = canonical_cpp_record_decl(target_base_decl);
    if (!derived_decl || !target_base_decl ||
        derived_decl == target_base_decl) {
        return 0;
    }

    std::unordered_set<std::string> matched_subobjects;
    std::vector<BasePathStep> path;
    std::unordered_set<const ObjectDecl*> active_stack;
    active_stack.insert(derived_decl);

    std::function<void(const ObjectDecl*)> walk =
        [&](const ObjectDecl* current_decl) {
        current_decl = canonical_cpp_record_decl(current_decl);
        if (!current_decl) {
            return;
        }
        if (current_decl == target_base_decl) {
            if (!path.empty()) {
                matched_subobjects.insert(
                    encode_base_path_key(path));
            }
            return;
        }
        auto walk_base_edge =
            [&](const RecordSemanticState::Base& base) {
            const ObjectDecl* base_decl =
                canonical_cpp_record_decl(base.record_decl);
            if (!base_decl ||
                base.declared_access !=
                    RecordMemberAccess::Public ||
                active_stack.contains(base_decl)) {
                return;
            }

            auto saved_path = path;
            if (base.is_virtual) {
                // Shared virtual-base subobject identity.
                path.clear();
                path.emplace_back(base_decl, true);
            } else {
                path.emplace_back(base_decl, false);
            }

            active_stack.insert(base_decl);
            walk(base_decl);
            active_stack.erase(base_decl);
            path = std::move(saved_path);
        };

        if (current_decl == current_record_decl) {
            for (const auto& base : current_record_bases) {
                walk_base_edge(base);
            }
            return;
        }

        const RecordSemanticState* state =
            record_semantics_cache_lookup(current_decl);
        if (!state) {
            return;
        }

        for (const auto& base : state->bases) {
            walk_base_edge(base);
        }
    };

    walk(derived_decl);
    return matched_subobjects.size();
}

static bool has_public_unambiguous_base_path(
    const ObjectDecl* derived_decl,
    const ObjectDecl* target_base_decl,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl) {
    size_t count = count_public_base_subobjects(
        derived_decl, target_base_decl, current_record_bases,
        current_record_decl);
    return count == 1;
}

struct CovariantReturnTarget {
    enum class Kind : uint8_t {
        Invalid,
        Pointer,
        LValueReference,
        RValueReference,
    };
    Kind kind = Kind::Invalid;
    QualType object_type;
    const ObjectDecl* object_decl = nullptr;
};

static CovariantReturnTarget extract_covariant_return_target(
    QualType return_type) {
    CovariantReturnTarget target;
    if (!return_type) {
        return target;
    }
    auto canonical_return = desugar_type(return_type);
    if (auto ptr_type = canonical_return.as_shared<PointerType>()) {
        target.kind = CovariantReturnTarget::Kind::Pointer;
        target.object_type = ptr_type->pointed_type;
    } else if (auto ref_type =
                   canonical_return.as_shared<ReferenceType>()) {
        target.kind = ref_type->isRValueReference()
            ? CovariantReturnTarget::Kind::RValueReference
            : CovariantReturnTarget::Kind::LValueReference;
        target.object_type = ref_type->referred_type;
    } else {
        return target;
    }

    auto object_type =
        desugar_type(target.object_type).as_shared<ObjectType>();
    if (!object_type) {
        target.kind = CovariantReturnTarget::Kind::Invalid;
        target.object_type = QualType();
        return target;
    }
    target.object_decl =
        canonical_cpp_record_decl(dyn_cast<ObjectDecl>(object_type->get_decl()));
    if (!target.object_decl) {
        target.kind = CovariantReturnTarget::Kind::Invalid;
        target.object_type = QualType();
    }
    return target;
}

// Covariant return validation (C++ [class.virtual]/7):
//   return types must be the same indirection kind (pointer / lvalue-ref / rvalue-ref)
//   overridden return qualifiers must be a SUPERSET of the overriding qualifiers
//   if both point to class types, the overriding class must be publicly and
//   unambiguously derived from the overridden class
// Covariance enables zero-cost polymorphic factory patterns: the derived
// implementation returns the more-specific type while callers holding a
// base pointer still see the expected base return type via a thunk adjustment.
static bool returns_are_covariant(
    QualType overriding_return,
    QualType overridden_return,
    const std::vector<RecordSemanticState::Base>& current_record_bases,
    const ObjectDecl* current_record_decl) {
    if (!overriding_return || !overridden_return) {
        return false;
    }
    if (overriding_return.equals_unqualified(overridden_return)) {
        return true;
    }

    CovariantReturnTarget overriding_target =
        extract_covariant_return_target(overriding_return);
    CovariantReturnTarget overridden_target =
        extract_covariant_return_target(overridden_return);
    if (overriding_target.kind == CovariantReturnTarget::Kind::Invalid ||
        overridden_target.kind == CovariantReturnTarget::Kind::Invalid ||
        overriding_target.kind != overridden_target.kind ||
        !overriding_target.object_type ||
        !overridden_target.object_type ||
        !overriding_target.object_decl ||
        !overridden_target.object_decl) {
        return false;
    }

    if (!overridden_target.object_type.has_all_qualifiers_of(
            overriding_target.object_type)) {
        return false;
    }
    if (overriding_target.object_decl ==
        overridden_target.object_decl) {
        return true;
    }
    return has_public_unambiguous_base_path(
        overriding_target.object_decl,
        overridden_target.object_decl,
        current_record_bases,
        current_record_decl);
}

struct VirtualSlotState {
    size_t slot_index = 0;
    bool is_pure = false;
    bool is_final = false;
    bool is_destructor = false;
    std::shared_ptr<Symbol> final_symbol = nullptr;
    std::string name;
};

// Convert front-end access specifier to the record-semantic-state encoding.
RecordMemberAccess encode_member_access(CppAccessSpecifier access) {
    switch (access) {
        case CppAccessSpecifier::Public:    return RecordMemberAccess::Public;
        case CppAccessSpecifier::Protected: return RecordMemberAccess::Protected;
        case CppAccessSpecifier::Private:   return RecordMemberAccess::Private;
        case CppAccessSpecifier::None:      break;
    }
    return RecordMemberAccess::Public;
}

// Check whether a namespace-scope binding already contains a function with the
// same type (for out-of-line redeclaration matching).
bool namespace_function_prior_match(const DeclBinding* binding,
                                    QualType declared_type) {
    auto candidate_matches = [&](const std::shared_ptr<Symbol>& candidate) {
        if (!candidate || candidate->kind != SymbolKind::FUNCTION) {
            return false;
        }
        if (candidate->type && declared_type) {
            return candidate->type.equals_unqualified(declared_type);
        }
        return candidate->type.get_shared() == declared_type.get_shared();
    };
    if (!binding) {
        return false;
    }
    if (binding->has_overload_set()) {
        for (const auto& candidate : binding->overload_candidates) {
            if (candidate_matches(candidate)) {
                return true;
            }
        }
        return false;
    }
    return candidate_matches(binding->symbol);
}

// Check whether a namespace-scope binding is a variable (for redeclaration).
bool namespace_variable_prior_match(const DeclBinding* binding) {
    return binding &&
        binding->symbol &&
        binding->symbol->kind == SymbolKind::VARIABLE;
}

// Extract __attribute__((weakref("target"))) alias name from attributes.
std::optional<std::string> extract_weakref_target(
    const std::vector<ParsedAttribute>& attrs) {
    for (const auto& attr : attrs) {
        if (attr.canonical_name() != "weakref" || attr.args.empty()) {
            continue;
        }
        const auto& arg0 = attr.args[0];
        if (arg0.kind == AttributeArg::Kind::STRING ||
            arg0.kind == AttributeArg::Kind::IDENTIFIER) {
            if (!arg0.str_value.empty()) {
                return arg0.str_value;
            }
        }
    }
    return std::nullopt;
}

} // namespace

std::unique_ptr<Decl> Parser::build_cpp_record_semantic_decl(
    const CppRecordDecl& record,
    std::optional<std::string> semantic_tag_name,
    bool allow_parent_tag_lookup_for_non_definition) {
    if (is_in_template_pattern_context()) {
        return nullptr;
    }
    if (!collect_ || record.name.empty()) {
        return nullptr;
    }
    Collect::CppRecordDeferredBodyCallback deferred_body_callback =
        [this](const CppRecordDecl& deferred_record,
               const std::shared_ptr<ObjectType>& deferred_record_type,
               const RecordSemanticState& deferred_semantic_state) {
            CppRecordDeferredParseContext deferred_ctx{
                deferred_record,
                deferred_record_type,
                deferred_semantic_state};
            build_cpp_record_parse_deferred_bodies(deferred_ctx);
        };
    auto semantic_decl = collect_->collect_build_cpp_record_semantic_decl(
        record,
        std::move(semantic_tag_name),
        &cpp_transient_semantic_decls_,
        std::move(deferred_body_callback),
        allow_parent_tag_lookup_for_non_definition);
    if (!semantic_decl || !ast_ctx) {
        return semantic_decl;
    }

    const auto& record_attrs = ast_ctx->get_attrs(record.node_id).attrs;
    if (!record_attrs.empty()) {
        std::vector<ParsedAttribute> copied_attrs(
            record_attrs.begin(), record_attrs.end());
        ast_ctx->append_attrs(semantic_decl->node_id, std::move(copied_attrs));
    }
    return semantic_decl;
}

void Parser::ensure_cpp_class_placeholder_type(const std::string& name, SrcLoc loc) {
    if (!collect_ || name.empty()) {
        return;
    }
    if (auto* existing_tag_decl = collect_->collect_lookup_tag_decl(name, false)) {
        if (!dyn_cast<ObjectDecl>(existing_tag_decl)) {
            error_custloc("tag '" + name + "' was previously declared with a different kind", loc);
        }
        return;
    }

    auto placeholder_type = std::make_shared<ObjectType>(name, false, true);
    auto placeholder_decl = collect_->collect_record_declaration(name, placeholder_type, false, loc);
    if (!placeholder_decl) {
        return;
    }
    collect_->query_publish_record_semantics(placeholder_decl.get(),
                                             RecordSemanticState{});
    collect_->collect_add_tag_decl(name, placeholder_decl.get());
    cpp_transient_semantic_decls_.push_back(std::move(placeholder_decl));
}

std::unique_ptr<ObjectDecl> Parser::take_cpp_transient_semantic_object_decl(
    const std::string& tag_name) {
    if (tag_name.empty()) {
        return nullptr;
    }

    for (size_t idx = cpp_transient_semantic_decls_.size(); idx > 0; --idx) {
        auto it = cpp_transient_semantic_decls_.begin() + (idx - 1);
        auto* object_decl = dyn_cast<ObjectDecl>(it->get());
        if (!object_decl || object_decl->tag != tag_name) {
            continue;
        }

        std::unique_ptr<Decl> owned_decl = std::move(*it);
        cpp_transient_semantic_decls_.erase(it);
        return std::unique_ptr<ObjectDecl>(
            static_cast<ObjectDecl*>(owned_decl.release()));
    }

    return nullptr;
}

template <typename TemplateDeclT>
void Parser::prepare_cpp_template_pattern_record_impl(TemplateDeclT& class_template) {
    auto* record = class_template.record_decl();
    if (!is_in_template_pattern_context() || !collect_ || !record ||
        !record->is_definition || record->name.empty()) {
        return;
    }

    auto* placeholder_decl = class_template.pattern_semantic_decl();
    if (!placeholder_decl) {
        auto owned_placeholder = take_cpp_transient_semantic_object_decl(record->name);
        if (!owned_placeholder) {
            error_custloc(
                "internal error: missing class template pattern semantic owner",
                record->location);
        }
        class_template.set_pattern_semantic_decl(std::move(owned_placeholder));
        placeholder_decl = class_template.pattern_semantic_decl();
    }

    if (!placeholder_decl) {
        return;
    }
    auto record_type = placeholder_decl->get_record_type();
    if (!record_type) {
        return;
    }
    record_type->set_decl(placeholder_decl);
    auto ensure_namespace_qualifier_prefix = [&](std::string& qualifier_prefix) {
        if (!collect_) {
            return;
        }
        auto scope = collect_->collect_current_scope();
        while (scope && scope->cxx_namespace_path.empty()) {
            scope = scope->parent;
        }
        qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
            scope, qualifier_prefix);
    };
    auto append_decl_attrs_to_symbol =
        [&](const Decl* decl, const std::shared_ptr<Symbol>& sym) {
        if (!ast_ctx || !decl || !sym) {
            return;
        }
        const auto& attrs = ast_ctx->get_attrs(decl->node_id).attrs;
        sym->sym_attrs.attrs.insert(
            sym->sym_attrs.attrs.end(),
            attrs.begin(),
            attrs.end());
    };

    RecordSemanticState semantic_state;
    semantic_state.is_incomplete = false;
    semantic_state.alignment = 1;
    semantic_state.non_virtual_alignment = 1;

    std::vector<ObjectType::Field> fields;
    std::vector<RecordSemanticState::Method> methods;
    std::vector<RecordSemanticState::MethodTemplate> method_templates;
    std::vector<RecordSemanticState::Constructor> constructors;
    std::vector<RecordSemanticState::Destructor> destructors;
    std::vector<RecordSemanticState::StaticDataMember> static_data_members;
    std::vector<RecordSemanticState::NestedType> nested_types;
    std::vector<RecordSemanticState::NestedTemplate> nested_templates;
    std::vector<RecordSemanticState::Base> bases;
    fields.reserve(record->members.size());
    methods.reserve(record->members.size());
    method_templates.reserve(record->members.size());
    constructors.reserve(record->members.size());
    destructors.reserve(record->members.size());
    static_data_members.reserve(record->members.size());
    nested_types.reserve(record->members.size());
    nested_templates.reserve(record->members.size());
    bases.reserve(record->bases.size());

    RecordMemberAccess current_access =
        encode_member_access(record->default_access);
    for (const auto& base_spec : record->bases) {
        RecordSemanticState::Base semantic_base;
        std::string base_name = cpp_base_specifier_name(base_spec);
        semantic_base.name = base_name;
        semantic_base.declared_access = encode_member_access(base_spec.access);
        semantic_base.is_virtual = base_spec.is_virtual_base;
        semantic_base.spec = &base_spec;

        if (base_name.empty()) {
            error_custloc(
                "expected base class name in base-specifier",
                base_spec.location);
        }

        QualType resolved_base_type = base_spec.type;
        if (resolved_base_type &&
            !cpp_base_type_is_dependent(resolved_base_type)) {
            resolved_base_type =
                collect_->collect_try_realize_deferred_semantic_type(
                    resolved_base_type);
        }
        if (cpp_base_type_is_current_instantiation(resolved_base_type)) {
            error_custloc(
                "class '" + record->name + "' cannot derive from itself",
                base_spec.location);
        }
        auto* base_record_decl = cpp_base_record_decl_from_type(resolved_base_type);
        if (!base_record_decl && !resolved_base_type) {
            auto* base_tag_decl =
                collect_->collect_lookup_tag_decl(base_name, true);
            base_record_decl = dyn_cast<ObjectDecl>(base_tag_decl);
            if (!base_record_decl) {
                resolved_base_type =
                    collect_->collect_lookup_type_name(
                        base_name,
                        true,
                        true);
                base_record_decl =
                    cpp_base_record_decl_from_type(resolved_base_type);
            }
        }
        if (!base_record_decl) {
            if (!resolved_base_type || !cpp_base_type_is_dependent(resolved_base_type)) {
                error_custloc(
                    "base type '" + base_name +
                        "' does not name a class or struct",
                    base_spec.location);
            }
            semantic_base.type = resolved_base_type;
            bases.push_back(std::move(semantic_base));
            continue;
        }

        const ObjectDecl* canonical_base_decl = base_record_decl;
        if (base_record_decl->get_record_type()) {
            if (auto* canonical =
                    dyn_cast<ObjectDecl>(
                        base_record_decl->get_record_type()->get_decl())) {
                canonical_base_decl = canonical;
            }
        }

        if (canonical_base_decl == placeholder_decl ||
            base_name == record->name) {
            error_custloc(
                "class '" + record->name + "' cannot derive from itself",
                base_spec.location);
        }
        if (canonical_base_decl->is_union) {
            error_custloc(
                "base type '" + base_name +
                    "' is a union; only class/struct bases are supported",
                base_spec.location);
        }
        const RecordSemanticState* base_state =
            collect_->query_lookup_record_semantics(canonical_base_decl);
        if (!base_state || base_state->is_incomplete) {
            error_custloc(
                "base class '" + base_name +
                    "' is incomplete",
                base_spec.location);
        }

        semantic_base.record_decl = canonical_base_decl;
        semantic_base.type = QualType(canonical_base_decl->get_record_type());
        bases.push_back(std::move(semantic_base));
    }
    for (const auto& member : record->members) {
        if (!member) {
            continue;
        }
        if (const auto* access_spec = dyn_cast<CppAccessSpecDecl>(member.get())) {
            current_access = encode_member_access(access_spec->access);
            continue;
        }

        if (const auto* field_decl = dyn_cast<FieldDecl>(member.get())) {
            if (field_decl->is_bitfield()) {
                fields.emplace_back(field_decl->name,
                                    field_decl->type,
                                    0,
                                    0,
                                    field_decl->bitfield_width,
                                    0,
                                    current_access);
            } else {
                fields.emplace_back(field_decl->name, field_decl->type, 0, current_access);
            }
            continue;
        }

        if (const auto* static_member_decl = dyn_cast<VariableDecl>(member.get())) {
            if (static_member_decl->storage_class != StorageClass::STATIC) {
                continue;
            }
            auto* mutable_static_member_decl =
                const_cast<VariableDecl*>(static_member_decl);
            std::string static_member_prefix = record->name;
            ensure_namespace_qualifier_prefix(static_member_prefix);
            bool has_in_class_initializer = static_member_decl->init != nullptr;

            std::shared_ptr<Symbol> static_member_sym = static_member_decl->sym;
            if (!static_member_sym) {
                static_member_sym = std::make_shared<Symbol>(
                    static_member_decl->name,
                    SymbolKind::VARIABLE,
                    desugar_type(static_member_decl->type),
                    StorageClass::STATIC,
                    VariableLinkage::EXTERNAL);
                static_member_sym->is_constexpr = static_member_decl->is_constexpr;
                static_member_sym->set_language_linkage(
                    static_member_decl->get_language_linkage());
                static_member_sym->is_defined = has_in_class_initializer;
                collect_->collect_add_global_symbol(static_member_sym);
                mutable_static_member_decl->sym = static_member_sym;
            } else {
                static_member_sym->type = desugar_type(static_member_decl->type);
                static_member_sym->storage_class = StorageClass::STATIC;
                static_member_sym->is_constexpr = static_member_decl->is_constexpr;
                if (has_in_class_initializer) {
                    static_member_sym->is_defined = true;
                }
                if (static_member_sym->get_language_linkage() ==
                    LanguageLinkage::None) {
                    static_member_sym->set_language_linkage(
                        static_member_decl->get_language_linkage());
                }
                if (static_member_sym->uid.empty()) {
                    collect_->collect_add_global_symbol(static_member_sym);
                }
            }
            if (!static_member_prefix.empty()) {
                set_symbol_cxx_qualifier_prefix(
                    static_member_sym.get(), static_member_prefix);
            }
            set_symbol_owner_record_type(
                static_member_sym.get(), QualType(record_type));
            append_decl_attrs_to_symbol(static_member_decl, static_member_sym);
            RecordSemanticState::StaticDataMember static_member;
            static_member.name = static_member_decl->name;
            static_member.type = static_member_decl->type;
            static_member.declared_access = current_access;
            static_member.decl = static_member_decl;
            static_member.symbol = static_member_sym;
            static_data_members.push_back(std::move(static_member));
            continue;
        }

        if (const auto* typedef_decl = dyn_cast<TypedefDecl>(member.get())) {
            RecordSemanticState::NestedType nested_type;
            nested_type.name = typedef_decl->name;
            nested_type.type = typedef_decl->type;
            nested_type.declared_access = current_access;
            nested_type.decl = typedef_decl;
            nested_type.symbol = typedef_decl->sym;
            nested_types.push_back(std::move(nested_type));
            continue;
        }

        if (const auto* alias_template = dyn_cast<AliasTemplateDecl>(member.get())) {
            if (const auto* alias_decl = alias_template->alias_decl()) {
                RecordSemanticState::NestedTemplate nested_template;
                nested_template.name = alias_decl->name;
                nested_template.declared_access = current_access;
                nested_template.kind =
                    RecordSemanticState::NestedTemplateKind::Alias;
                nested_template.decl = alias_template;
                nested_templates.push_back(std::move(nested_template));
            }
            continue;
        }

        if (const auto* class_template = dyn_cast<ClassTemplateDecl>(member.get())) {
            if (const auto* nested_record = class_template->record_decl();
                nested_record && !nested_record->name.empty()) {
                RecordSemanticState::NestedTemplate nested_template;
                nested_template.name = nested_record->name;
                nested_template.declared_access = current_access;
                nested_template.kind =
                    RecordSemanticState::NestedTemplateKind::Class;
                nested_template.decl = class_template;
                nested_templates.push_back(std::move(nested_template));
            }
            continue;
        }

        if (const auto* ctor_decl = dyn_cast<CppConstructorDecl>(member.get())) {
            std::string ctor_prefix;
            if (auto* qualifier_prefix =
                    get_func_decl_cxx_qualifier_prefix(ctor_decl)) {
                ctor_prefix = *qualifier_prefix;
            }
            if (ctor_prefix.empty()) {
                ctor_prefix = record->name;
            }
            ensure_namespace_qualifier_prefix(ctor_prefix);
            if (!ctor_prefix.empty()) {
                set_func_decl_cxx_qualifier_prefix(ctor_decl, ctor_prefix);
            }
            set_func_decl_owner_record_type(ctor_decl, QualType(record_type));
            auto ctor_sym = collect_->collect_declare_function_symbol(
                ctor_decl->name,
                ctor_decl->type,
                ctor_decl->storage_class,
                ctor_decl->is_constexpr,
                ctor_decl->is_consteval,
                ctor_decl->is_inline,
                function_decl_defines_entity(ctor_decl),
                ctor_decl->location,
                ctor_decl->get_language_linkage(),
                true,
                ctor_decl->is_deleted,
                ctor_decl->is_defaulted,
                QualType(record_type),
                ctor_prefix);
            if (ctor_sym) {
                set_symbol_owner_record_type(ctor_sym.get(), QualType(record_type));
                if (!ctor_prefix.empty()) {
                    set_symbol_cxx_qualifier_prefix(ctor_sym.get(), ctor_prefix);
                }
                if (function_decl_defines_entity(ctor_decl)) {
                    ctor_sym->function_definition =
                        const_cast<CppConstructorDecl*>(ctor_decl);
                }
                append_decl_attrs_to_symbol(ctor_decl, ctor_sym);
            }

            RecordSemanticState::Constructor ctor;
            ctor.name = ctor_decl->name;
            ctor.type = ctor_decl->type;
            ctor.declared_access = current_access;
            ctor.is_implicit = false;
            ctor.is_explicit = ctor_decl->is_explicit;
            ctor.is_deleted = ctor_decl->is_deleted;
            ctor.is_defaulted = ctor_decl->is_defaulted;
            ctor.is_constexpr = ctor_decl->is_constexpr;
            ctor.is_consteval = ctor_decl->is_consteval;
            ctor.decl = ctor_decl;
            ctor.symbol = std::move(ctor_sym);
            constructors.push_back(std::move(ctor));
            semantic_state.definition_data.has_user_declared_constructor = true;
            continue;
        }

        if (const auto* dtor_decl = dyn_cast<CppDestructorDecl>(member.get())) {
            std::string dtor_prefix;
            if (auto* qualifier_prefix =
                    get_func_decl_cxx_qualifier_prefix(dtor_decl)) {
                dtor_prefix = *qualifier_prefix;
            }
            if (dtor_prefix.empty()) {
                dtor_prefix = record->name;
            }
            ensure_namespace_qualifier_prefix(dtor_prefix);
            if (!dtor_prefix.empty()) {
                set_func_decl_cxx_qualifier_prefix(dtor_decl, dtor_prefix);
            }
            set_func_decl_owner_record_type(dtor_decl, QualType(record_type));
            auto dtor_sym = collect_->collect_declare_function_symbol(
                dtor_decl->name,
                dtor_decl->type,
                dtor_decl->storage_class,
                dtor_decl->is_constexpr,
                dtor_decl->is_consteval,
                dtor_decl->is_inline,
                function_decl_defines_entity(dtor_decl),
                dtor_decl->location,
                dtor_decl->get_language_linkage(),
                true,
                dtor_decl->is_deleted,
                dtor_decl->is_defaulted,
                QualType(record_type),
                dtor_prefix);
            if (dtor_sym) {
                set_symbol_owner_record_type(dtor_sym.get(), QualType(record_type));
                if (!dtor_prefix.empty()) {
                    set_symbol_cxx_qualifier_prefix(dtor_sym.get(), dtor_prefix);
                }
                if (function_decl_defines_entity(dtor_decl)) {
                    dtor_sym->function_definition =
                        const_cast<CppDestructorDecl*>(dtor_decl);
                }
                append_decl_attrs_to_symbol(dtor_decl, dtor_sym);
            }

            RecordSemanticState::Destructor dtor;
            dtor.name = dtor_decl->name;
            dtor.type = dtor_decl->type;
            dtor.declared_access = current_access;
            dtor.is_implicit = false;
            dtor.is_defaulted = dtor_decl->is_defaulted;
            dtor.is_deleted = dtor_decl->is_deleted;
            dtor.is_constexpr = dtor_decl->is_constexpr;
            dtor.is_consteval = dtor_decl->is_consteval;
            dtor.is_virtual = dtor_decl->is_virtual;
            dtor.is_override = dtor_decl->is_override;
            dtor.is_final = dtor_decl->is_final;
            dtor.is_pure = dtor_decl->is_pure;
            dtor.decl = dtor_decl;
            dtor.symbol = std::move(dtor_sym);
            destructors.push_back(std::move(dtor));
            semantic_state.definition_data.has_user_declared_destructor = true;
            if (dtor_decl->is_deleted) {
                semantic_state.definition_data.has_deleted_destructor = true;
            }
            continue;
        }

        if (const auto* method_template = dyn_cast<FunctionTemplateDecl>(member.get())) {
            auto* templated_function = method_template->function_decl();
            auto* templated_method =
                dyn_cast<CppMethodDecl>(templated_function);
            auto* templated_ctor =
                dyn_cast<CppConstructorDecl>(templated_function);
            if (!templated_method && !templated_ctor) {
                continue;
            }

            std::string method_prefix;
            if (auto* qualifier_prefix =
                    get_func_decl_cxx_qualifier_prefix(templated_function)) {
                method_prefix = *qualifier_prefix;
            }
            if (method_prefix.empty()) {
                method_prefix = record->name;
            }
            ensure_namespace_qualifier_prefix(method_prefix);
            if (!method_prefix.empty()) {
                set_func_decl_cxx_qualifier_prefix(
                    templated_function,
                    method_prefix);
            }
            set_func_decl_owner_record_type(
                templated_function,
                QualType(record_type));

            RecordSemanticState::MethodTemplate method_template_state;
            method_template_state.name = templated_function->name;
            method_template_state.declared_access = current_access;
            method_template_state.is_static =
                templated_method &&
                templated_method->storage_class == StorageClass::STATIC;
            method_template_state.decl = method_template;
            method_templates.push_back(std::move(method_template_state));
            if (templated_ctor) {
                semantic_state.definition_data.has_user_declared_constructor =
                    true;
            }
            continue;
        }

        if (const auto* method_decl = dyn_cast<CppMethodDecl>(member.get())) {
            std::string method_prefix;
            if (auto* qualifier_prefix =
                    get_func_decl_cxx_qualifier_prefix(method_decl)) {
                method_prefix = *qualifier_prefix;
            }
            if (method_prefix.empty()) {
                method_prefix = record->name;
            }
            ensure_namespace_qualifier_prefix(method_prefix);
            if (!method_prefix.empty()) {
                set_func_decl_cxx_qualifier_prefix(method_decl, method_prefix);
            }
            set_func_decl_owner_record_type(method_decl, QualType(record_type));
            auto method_sym = collect_->collect_declare_function_symbol(
                method_decl->name,
                method_decl->type,
                method_decl->storage_class,
                method_decl->is_constexpr,
                method_decl->is_consteval,
                method_decl->is_inline,
                function_decl_defines_entity(method_decl),
                method_decl->location,
                method_decl->get_language_linkage(),
                true,
                method_decl->is_deleted,
                method_decl->is_defaulted,
                QualType(record_type),
                method_prefix);
            if (method_sym) {
                set_symbol_owner_record_type(method_sym.get(), QualType(record_type));
                if (!method_prefix.empty()) {
                    set_symbol_cxx_qualifier_prefix(method_sym.get(), method_prefix);
                }
                if (function_decl_defines_entity(method_decl)) {
                    method_sym->function_definition =
                        const_cast<CppMethodDecl*>(method_decl);
                }
                append_decl_attrs_to_symbol(method_decl, method_sym);
            }

            RecordSemanticState::Method method;
            method.name = method_decl->name;
            method.type = method_decl->type;
            method.declared_access = current_access;
            method.is_static = method_decl->storage_class == StorageClass::STATIC;
            method.is_deleted = method_decl->is_deleted;
            method.is_defaulted = method_decl->is_defaulted;
            method.is_constexpr = method_decl->is_constexpr;
            method.is_consteval = method_decl->is_consteval;
            method.is_explicit = method_decl->is_explicit_conversion;
            method.is_virtual = method_decl->is_virtual;
            method.is_override = method_decl->is_override;
            method.is_final = method_decl->is_final;
            method.is_pure = method_decl->is_pure;
            method.is_conversion_function = method_decl->is_conversion_function;
            method.conversion_target_type = method_decl->conversion_target_type;
            method.decl = method_decl;
            method.symbol = std::move(method_sym);
            methods.push_back(std::move(method));
            continue;
        }
    }

    size_t next_virtual_slot = 0;
    for (auto& method : methods) {
        if (!method.is_virtual || method.is_static) {
            continue;
        }
        semantic_state.is_polymorphic = true;
        method.virtual_slot_index = static_cast<int32_t>(next_virtual_slot++);
        RecordSemanticState::VirtualSlot slot;
        slot.key = method.name;
        slot.name = method.name;
        slot.is_pure = method.is_pure;
        slot.is_final = method.is_final;
        slot.final_symbol = method.symbol;
        semantic_state.virtual_slots.push_back(std::move(slot));
    }
    for (auto& dtor : destructors) {
        if (!dtor.is_virtual) {
            continue;
        }
        semantic_state.is_polymorphic = true;
        semantic_state.has_virtual_destructor = true;
        dtor.virtual_slot_index = static_cast<int32_t>(next_virtual_slot++);
        RecordSemanticState::VirtualSlot slot;
        slot.key = "<destructor>";
        slot.name = dtor.name;
        slot.is_destructor = true;
        slot.is_pure = dtor.is_pure;
        slot.is_final = dtor.is_final;
        slot.final_symbol = dtor.symbol;
        semantic_state.virtual_slots.push_back(std::move(slot));
    }
    for (const auto& slot : semantic_state.virtual_slots) {
        if (slot.is_pure) {
            semantic_state.is_abstract = true;
            break;
        }
    }

    semantic_state.fields = std::move(fields);
    semantic_state.methods = std::move(methods);
    semantic_state.method_templates = std::move(method_templates);
    semantic_state.constructors = std::move(constructors);
    semantic_state.destructors = std::move(destructors);
    semantic_state.static_data_members = std::move(static_data_members);
    semantic_state.nested_types = std::move(nested_types);
    semantic_state.nested_templates = std::move(nested_templates);
    semantic_state.bases = std::move(bases);
    if (auto* definition_data = record->get_definition_data()) {
        *definition_data = semantic_state.definition_data;
    }
    collect_->query_publish_record_semantics(placeholder_decl,
                                             std::move(semantic_state));
    const ClassTemplateDecl* current_instantiation_primary = nullptr;
    QualType current_instantiation_type;
    if constexpr (std::is_same_v<TemplateDeclT, ClassTemplateDecl>) {
        current_instantiation_primary = &class_template;
        current_instantiation_type =
            build_cpp_primary_current_instantiation_type(
                current_instantiation_primary,
                record->name,
                record->location);
    } else if constexpr (
        std::is_same_v<TemplateDeclT,
                       ClassTemplatePartialSpecializationDecl>) {
        current_instantiation_primary = class_template.primary_template();
        current_instantiation_type =
            build_cpp_current_instantiation_type(
                current_instantiation_primary,
                record->name,
                class_template.specialization_arguments);
    }

    struct DeferredInlineParserState {
        size_t token_idx = 0;
        std::shared_ptr<CType> active_func_type;
        LanguageLinkage active_decl_linkage = LanguageLinkage::None;
        std::unordered_set<std::string> active_seen_stmt_labels;
        std::unordered_set<std::string> active_stmt_labels;
        std::vector<std::unordered_map<std::string, std::string>> active_local_label_scopes;
        uint64_t active_local_label_unique_id = 0;
    };
    auto capture_deferred_inline_parser_state = [&]() -> DeferredInlineParserState {
        DeferredInlineParserState state;
        state.token_idx = get_token_idx();
        state.active_func_type = func_type;
        state.active_decl_linkage = current_language_linkage_;
        state.active_seen_stmt_labels = seen_stmt_labels;
        state.active_stmt_labels = stmt_labels;
        state.active_local_label_scopes = local_label_scopes_;
        state.active_local_label_unique_id = local_label_unique_id_;
        return state;
    };
    auto restore_deferred_inline_parser_state =
        [&](DeferredInlineParserState&& state) {
            current_language_linkage_ = state.active_decl_linkage;
            func_type = std::move(state.active_func_type);
            set_token_idx(state.token_idx);
            seen_stmt_labels = std::move(state.active_seen_stmt_labels);
            stmt_labels = std::move(state.active_stmt_labels);
            local_label_scopes_ = std::move(state.active_local_label_scopes);
            local_label_unique_id_ = state.active_local_label_unique_id;
        };

    auto parse_deferred_constructor_member_initializers =
        [&](CppConstructorDecl* ctor) {
            if (!ctor) {
                return;
            }
            size_t saved_idx = get_token_idx();
            for (auto& mem_init : ctor->ctor_initializers) {
                mem_init.member_expr.reset();
                mem_init.init_expr.reset();
                mem_init.is_base_initializer = false;

                if (mem_init.is_delegating_initializer) {
                    if (mem_init.deferred_init_end_token_idx <=
                        mem_init.deferred_init_begin_token_idx) {
                        continue;
                    }

                    set_token_idx(mem_init.deferred_init_begin_token_idx);
                    std::unique_ptr<Expr> parsed_init;
                    if (gentle_check(TokenType::LEFT_PAREN)) {
                        advance();
                        std::vector<std::unique_ptr<Expr>> args;
                        if (!gentle_check(TokenType::RIGHT_PAREN)) {
                            do {
                                args.push_back(
                                    parse_assignment_expression_with_optional_pack_expansion());
                            } while (gentle_check_and_consume(TokenType::COMMA));
                        }
                        check_and_consume(TokenType::RIGHT_PAREN);
                        mem_init.init_expr =
                            collect_->collect_member_initializer_expression(
                                std::move(args),
                                QualType(record_type),
                                false,
                                mem_init.location,
                                true);
                    } else if (gentle_check(TokenType::LEFT_BRACE)) {
                        parsed_init = parse_init_list();
                    } else {
                        error("expected '(' or '{' in constructor member initializer");
                    }

                    set_token_idx(mem_init.deferred_init_end_token_idx);
                    if (!mem_init.init_expr && parsed_init) {
                        mem_init.init_expr =
                            collect_->collect_member_initializer_expression(
                                std::move(parsed_init),
                                QualType(record_type),
                                mem_init.location);
                    }
                    continue;
                }

                auto this_expr = collect_->collect_cpp_this_expression(mem_init.location);
                mem_init.member_expr = collect_->collect_member_expression(
                    std::move(this_expr),
                    mem_init.member_name,
                    true,
                    mem_init.location);
                auto* member_expr = dyn_cast<MemberExpr>(mem_init.member_expr.get());
                if (!member_expr || !member_expr->member_type ||
                    mem_init.deferred_init_end_token_idx <=
                        mem_init.deferred_init_begin_token_idx) {
                    continue;
                }

                set_token_idx(mem_init.deferred_init_begin_token_idx);
                std::unique_ptr<Expr> parsed_init;
                if (gentle_check(TokenType::LEFT_PAREN)) {
                    advance();
                    std::vector<std::unique_ptr<Expr>> args;
                    if (!gentle_check(TokenType::RIGHT_PAREN)) {
                        do {
                            args.push_back(
                                parse_assignment_expression_with_optional_pack_expansion());
                        } while (gentle_check_and_consume(TokenType::COMMA));
                    }
                    check_and_consume(TokenType::RIGHT_PAREN);

                    if (canonical_type_kind(member_expr->member_type) ==
                            TypeKind::Object ||
                        args.empty()) {
                        mem_init.init_expr =
                            collect_->collect_member_initializer_expression(
                                std::move(args),
                                member_expr->member_type,
                                false,
                                mem_init.location);
                    } else if (args.size() > 1) {
                        diag_engine->report_error(
                            "constructor member initializer for non-class member '" +
                                mem_init.member_name +
                                "' requires a single expression",
                            mem_init.location);
                    } else {
                        parsed_init = std::move(args.front());
                    }
                } else if (gentle_check(TokenType::LEFT_BRACE)) {
                    parsed_init = parse_init_list();
                } else {
                    error("expected '(' or '{' in constructor member initializer");
                }

                set_token_idx(mem_init.deferred_init_end_token_idx);
                if (mem_init.init_expr || !parsed_init) {
                    continue;
                }
                if (canonical_type_kind(member_expr->member_type) ==
                    TypeKind::Reference) {
                    mem_init.init_expr = std::move(parsed_init);
                } else {
                    mem_init.init_expr = collect_->collect_member_initializer_expression(
                        std::move(parsed_init),
                        member_expr->member_type,
                        mem_init.location);
                }
            }
            set_token_idx(saved_idx);
        };

    auto parse_deferred_inline_member_body =
        [&](auto* member_decl,
            bool is_static_member_function,
            bool allow_ctor_mem_initializer_after_try,
            auto&& pre_body_hook) {
            if (!member_decl || !member_decl->has_deferred_inline_body() ||
                member_decl->body) {
                return;
            }

            DeferredInlineParserState saved_state =
                capture_deferred_inline_parser_state();
            seen_stmt_labels.clear();
            stmt_labels.clear();
            local_label_scopes_.clear();
            local_label_unique_id_ = 0;

            auto entered_scope = collect_->collect_enter_scope(ScopeFlags::FunctionScope);
            auto function_scope = entered_scope.scope;

            QualType previous_record_lookup_type =
                collect_->collect_current_cpp_record_lookup_type();
            QualType active_record_lookup_type = QualType(record_type);
            if (active_record_lookup_type) {
                collect_->collect_set_current_cpp_record_lookup_type(
                    active_record_lookup_type);
            }

            Collect::CppThisContext cpp_this_context;
            cpp_this_context.is_member_function = true;
            cpp_this_context.is_static_member_function = is_static_member_function;
            auto fn_type = dyn_cast_shared<FunctionType>(member_decl->type);
            if (!cpp_this_context.is_static_member_function &&
                fn_type && !fn_type->parameters.empty()) {
                cpp_this_context.this_type = fn_type->parameters.front();
            }
            if (!cpp_this_context.this_type && active_record_lookup_type) {
                cpp_this_context.this_type = QualType(
                    std::make_shared<PointerType>(active_record_lookup_type));
            } else if (cpp_this_context.this_type && current_instantiation_type) {
                uint8_t pointee_quals = QUAL_NONE;
                if (auto this_ptr =
                        cpp_this_context.this_type.as_shared<PointerType>()) {
                    pointee_quals = this_ptr->pointed_type.get_qualifiers();
                }
                QualType qualified_owner(
                    current_instantiation_type.get_shared(),
                    static_cast<uint8_t>(
                        current_instantiation_type.get_qualifiers() |
                        pointee_quals));
                cpp_this_context.this_type = QualType(
                    std::make_shared<PointerType>(qualified_owner));
            }

            func_type = member_decl->type;
            current_language_linkage_ = LanguageLinkage::None;
            collect_->collect_start_function_definition(
                member_decl->name,
                QualType(member_decl->type),
                cpp_this_context);
            Collect::ImmediateFunctionContextScope immediate_function_context_guard(
                collect_.get(), member_decl->is_consteval != 0);

            for (auto& param_decl_base : member_decl->parameters) {
                auto* param_decl = dyn_cast<ParamDecl>(param_decl_base.get());
                if (!param_decl || !param_decl->has_name() ||
                    param_decl->get_name() == "this") {
                    continue;
                }
                param_decl->sym = collect_->collect_declare_variable_symbol(
                    param_decl->get_name(),
                    param_decl->type,
                    param_decl->storage_class,
                    false,
                    false,
                    param_decl->location);
            }

            cxx_record_parse_stack_.push_back(
                CppRecordParseFrame{
                    record->record_kind,
                    record->name,
                    placeholder_decl,
                    current_instantiation_primary,
                    current_instantiation_type});
            bool pop_record_parse_frame = true;

            try {
                pre_body_hook(member_decl);
                set_token_idx(member_decl->deferred_inline_body_begin_token_idx);
                if (gentle_check(TokenType::TRY_KW)) {
                    auto try_stmt = parse_cpp_try_statement(
                        function_scope,
                        allow_ctor_mem_initializer_after_try);
                    SrcLoc body_loc = try_stmt ? try_stmt->location : SrcLoc();
                    std::vector<std::unique_ptr<Stmt>> stmts;
                    stmts.push_back(std::move(try_stmt));
                    member_decl->body = collect_->collect_compound_statement(
                        std::move(stmts), function_scope, body_loc);
                } else {
                    member_decl->body = parse_compound_stmt(function_scope);
                }
                member_decl->scope = function_scope;
                member_decl->stmt_labels.insert(
                    stmt_labels.begin(), stmt_labels.end());
                set_token_idx(member_decl->deferred_inline_body_end_token_idx);
                member_decl->clear_deferred_inline_body_token_range();
                collect_->collect_leave_scope();
                collect_->collect_finish_function_definition(function_scope);
                collect_->collect_set_current_cpp_record_lookup_type(
                    previous_record_lookup_type);
                if (pop_record_parse_frame && !cxx_record_parse_stack_.empty()) {
                    cxx_record_parse_stack_.pop_back();
                    pop_record_parse_frame = false;
                }
            } catch (...) {
                if (pop_record_parse_frame && !cxx_record_parse_stack_.empty()) {
                    cxx_record_parse_stack_.pop_back();
                    pop_record_parse_frame = false;
                }
                collect_->collect_abort_function_definition();
                collect_->collect_leave_scope();
                collect_->collect_set_current_cpp_record_lookup_type(
                    previous_record_lookup_type);
                restore_deferred_inline_parser_state(std::move(saved_state));
                throw;
            }

            restore_deferred_inline_parser_state(std::move(saved_state));
        };
    auto parse_deferred_inline_method_template_body =
        [&](FunctionTemplateDecl* method_template) {
        auto* templated_function =
            method_template ? method_template->function_decl() : nullptr;
        auto* templated_method =
            dyn_cast<CppMethodDecl>(templated_function);
        auto* templated_ctor =
            dyn_cast<CppConstructorDecl>(templated_function);
        if (!templated_method && !templated_ctor) {
            return;
        }

        collect_->collect_enter_scope(ScopeFlags::TemplateParameterScope);
        struct TemplateScopeGuard {
            Collect* collect = nullptr;
            ~TemplateScopeGuard() {
                if (collect) {
                    collect->collect_leave_scope();
                }
            }
        } template_scope_guard{collect_.get()};

        active_template_parameter_stack_.push_back({});
        struct ActiveTemplateParameterGuard {
            std::vector<std::vector<const TemplateParameterDecl*>>* stack = nullptr;
            ~ActiveTemplateParameterGuard() {
                if (stack && !stack->empty()) {
                    stack->pop_back();
                }
            }
        } active_template_parameter_guard{&active_template_parameter_stack_};
        ++template_pattern_depth_;
        struct TemplatePatternGuard {
            uint32_t* depth = nullptr;
            ~TemplatePatternGuard() {
                if (depth) {
                    --(*depth);
                }
            }
        } template_pattern_guard{&template_pattern_depth_};

        auto& active_parameters = active_template_parameter_stack_.back();
        active_parameters.reserve(method_template->parameters.size());
        for (const auto& parameter : method_template->parameters) {
            const auto* template_parameter = parameter.get();
            if (!template_parameter) {
                continue;
            }
            active_parameters.push_back(template_parameter);
            if (auto* type_parameter =
                    dyn_cast<TemplateTypeParmDecl>(parameter.get())) {
                if (!type_parameter->name.empty()) {
                    collect_->collect_declare_type_name_symbol(
                        type_parameter->name,
                        QualType(type_parameter->type),
                        type_parameter->location);
                }
                continue;
            }
            if (auto* non_type_parameter =
                    dyn_cast<TemplateNonTypeParmDecl>(parameter.get())) {
                if (!non_type_parameter->name.empty() &&
                    non_type_parameter->sym) {
                    collect_->collect_bind_symbol_in_current_scope(
                        non_type_parameter->name,
                        non_type_parameter->sym);
                }
            }
        }

        if (templated_ctor) {
            parse_deferred_inline_member_body(
                templated_ctor,
                false,
                true,
                [&](CppConstructorDecl* ctor) {
                    parse_deferred_constructor_member_initializers(ctor);
                });
            return;
        }

        parse_deferred_inline_member_body(
            templated_method,
            templated_method->storage_class == StorageClass::STATIC,
            false,
            [](CppMethodDecl*) {});
    };

    for (const auto& member : record->members) {
        auto* method_decl = dyn_cast<CppMethodDecl>(member.get());
        if (!method_decl) {
            auto* method_template = dyn_cast<FunctionTemplateDecl>(member.get());
            if (!method_template) {
                continue;
            }
            parse_deferred_inline_method_template_body(method_template);
            continue;
        }
        parse_deferred_inline_member_body(
            method_decl,
            method_decl->storage_class == StorageClass::STATIC,
            false,
            [](CppMethodDecl*) {});
    }
    for (const auto& member : record->members) {
        auto* ctor_decl = dyn_cast<CppConstructorDecl>(member.get());
        if (!ctor_decl) {
            continue;
        }
        parse_deferred_inline_member_body(
            ctor_decl,
            false,
            true,
            [&](CppConstructorDecl* ctor) {
                parse_deferred_constructor_member_initializers(ctor);
            });
    }
    for (const auto& member : record->members) {
        auto* dtor_decl = dyn_cast<CppDestructorDecl>(member.get());
        if (!dtor_decl) {
            continue;
        }
        parse_deferred_inline_member_body(
            dtor_decl,
            false,
            false,
            [](CppDestructorDecl*) {});
    }
}

void Parser::prepare_cpp_template_pattern_record(ClassTemplateDecl& class_template) {
    prepare_cpp_template_pattern_record_impl(class_template);
}

void Parser::prepare_cpp_template_pattern_record(
    ClassTemplatePartialSpecializationDecl& class_template) {
    prepare_cpp_template_pattern_record_impl(class_template);
}
/*
 * int x, y, z, a(int, int), h[67], *accra(int belgrade, int bucharest); is a valid declstmt
 */
std::optional<std::vector<std::unique_ptr<Decl>>> Parser::try_parse_extern_linkage_declaration() {
    Token t = current_token();
    if (t.type != TokenType::EXTERN || peek_token().type != TokenType::STRING_LITERAL) {
        return std::nullopt;
    }

    std::vector<std::unique_ptr<Decl>> ret_vec;
    advance(); // consume extern
    Token linkage_tok = current_token();
    LanguageLinkage linkage_kind = LanguageLinkage::None;
    if (linkage_tok.literal_prefix != LiteralPrefix::None) {
        error_custloc(
            "invalid language linkage specification; expected \"C\" or \"C++\"",
            linkage_tok.loc);
    }
    if (linkage_tok.value == "C") {
        linkage_kind = LanguageLinkage::C;
    } else if (linkage_tok.value == "C++") {
        linkage_kind = LanguageLinkage::CXX;
    } else {
        error_custloc(
            "invalid language linkage specification \"" + linkage_tok.value +
                "\"; expected \"C\" or \"C++\"",
            linkage_tok.loc);
    }
    advance(); // consume string literal

    LanguageLinkage saved_linkage = current_language_linkage_;
    current_language_linkage_ = linkage_kind;
    try {
        if (gentle_check_and_consume(TokenType::LEFT_BRACE)) {
            while (!gentle_check(TokenType::RIGHT_BRACE)) {
                if (gentle_check(TokenType::Eof)) {
                    error("Expected '}' to close extern linkage block");
                    return std::vector<std::unique_ptr<Decl>>{};
                }
                auto decls = parse_declaration();
                if (decls.empty()) {
                    error("While parsing extern linkage block, we encountered a non-declaration");
                    return std::vector<std::unique_ptr<Decl>>{};
                }
                ret_vec.insert(ret_vec.end(),
                    std::make_move_iterator(decls.begin()),
                    std::make_move_iterator(decls.end()));
            }
            advance(); // consume }
            gentle_check_and_consume(TokenType::SEMICOLON);
            if (ret_vec.empty()) {
                ret_vec.push_back(collect_->collect_nop_declaration(linkage_tok.loc));
            }
            current_language_linkage_ = saved_linkage;
            return std::move(ret_vec);
        }
        auto decls = parse_declaration();
        current_language_linkage_ = saved_linkage;
        return decls;
    } catch (...) {
        current_language_linkage_ = saved_linkage;
        throw;
    }
}

std::optional<std::vector<std::unique_ptr<Decl>>> Parser::try_parse_cpp_standalone_record_declaration() {
    if (!is_cxx_mode_active() ||
        (!gentle_check(TokenType::CLASS) &&
         !gentle_check(TokenType::STRUCT) &&
         !gentle_check(TokenType::UNION))) {
        return std::nullopt;
    }

    std::vector<std::unique_ptr<Decl>> ret_vec;
    RevertingTentativeParsingAction tentative(*this);
    try {
        auto cpp_record = parse_cpp_record_specifier();
        if (gentle_check(TokenType::SEMICOLON)) {
            tentative.commit();
            auto* cpp_record_decl = dyn_cast<CppRecordDecl>(cpp_record.get());
            ret_vec.push_back(std::move(cpp_record));
            if (cpp_record_decl) {
                if (auto semantic_decl = build_cpp_record_semantic_decl(*cpp_record_decl)) {
                    ret_vec.push_back(std::move(semantic_decl));
                }
            }
            advance();
            return std::move(ret_vec);
        }
    } catch (const ParseError& e) {
        if (e.message.find("C++ parser unsupported syntax:") == 0) {
            throw;
        }
    }

    return std::nullopt;
}

std::optional<std::vector<std::unique_ptr<Decl>>> Parser::try_parse_special_declaration() {
    if (auto extern_linkage = try_parse_extern_linkage_declaration()) {
        return extern_linkage;
    }

    if (gentle_check(TokenType::STATIC_ASSERT)) {
        std::vector<std::unique_ptr<Decl>> ret_vec;
        ret_vec.push_back(parse_static_assert_declaration());
        return std::move(ret_vec);
    }

    if (gentle_check(TokenType::EXTENSION_KW)) {
        advance(); // consume __extension__
        return parse_declaration();
    }

    if (gentle_check(TokenType::SEMICOLON)) {
        std::vector<std::unique_ptr<Decl>> ret_vec;
        SrcLoc loc = current_token().loc;
        advance();
        ret_vec.push_back(collect_->collect_nop_declaration(loc));
        return std::move(ret_vec);
    }

    if (is_cxx_mode_active() &&
        (gentle_check(TokenType::NAMESPACE) ||
         (gentle_check(TokenType::INLINE) && peek_token().type == TokenType::NAMESPACE))) {
        return parse_cpp_namespace_definition();
    }
    if (is_cxx_mode_active() && gentle_check(TokenType::USING)) {
        return parse_cpp_using_alias_declaration();
    }
    if (is_cxx_mode_active() && gentle_check(TokenType::TEMPLATE)) {
        return parse_cpp_template_declaration();
    }
    if (is_cxx_mode_active() && is_cpp_deduction_guide_declaration_start()) {
        std::vector<std::unique_ptr<Decl>> ret_vec;
        ret_vec.push_back(parse_cpp_deduction_guide_declaration());
        return std::move(ret_vec);
    }
    if (is_cxx_mode_active()) {
        if (is_cpp_out_of_line_constructor_declaration_start()) {
            return parse_cpp_out_of_line_constructor_definition();
        }
        if (is_cpp_out_of_line_destructor_declaration_start()) {
            return parse_cpp_out_of_line_destructor_definition();
        }
    }
    if (auto standalone_record = try_parse_cpp_standalone_record_declaration()) {
        return standalone_record;
    }

    return std::nullopt;
}

void Parser::validate_declaration_start(Token start_token) {
    if (!isTokenDeclarationSpec(current_token())) {
        // K&R / C89 implicit int: if this looks like a declarator, assume int.
        bool looks_like_implicit_int_decl =
            lang_opts.implicit_int &&
            (current_token().type == TokenType::IDENTIFIER ||
             current_token().type == TokenType::MULTIPLY ||
             current_token().type == TokenType::LEFT_PAREN);
        if (!looks_like_implicit_int_decl &&
            !(current_token().type == TokenType::IDENTIFIER &&
              peek_token().type == TokenType::LEFT_PAREN)) {
            error("Unexpected token while parsing declaration: expected a decl specifier, got \""
                          + start_token.value + "\" instead.");
        }
    }
}

void Parser::emit_declaration_head_side_decls(DeclarationParser& decl_parser,
    const std::shared_ptr<CType>& parsed_type,
    std::vector<std::unique_ptr<Decl>>& ret_vec) {
    if (decl_parser.cpp_record_obj) {
        ret_vec.push_back(std::move(decl_parser.cpp_record_obj));
    }
    if (canonical_type_kind(parsed_type) == TypeKind::Object && decl_parser.struct_obj) {
        // We will "weed" out the unncessary object_decls at sema stage
        ret_vec.push_back(std::move(decl_parser.struct_obj));
    } else if (canonical_type_kind(parsed_type) == TypeKind::Enum && decl_parser.enum_obj) {
        ret_vec.push_back(std::move(decl_parser.enum_obj));
    }
}

std::shared_ptr<CType> Parser::parse_declaration_head(Token start_token,
    DeclarationParser& decl_parser,
    std::vector<std::unique_ptr<Decl>>& ret_vec) {

    // example: Distance::operator double()
    auto looks_like_typeless_cpp_conversion_declaration =
        [&]() -> bool {
            if (!is_cxx_mode_active()) {
                return false;
            }
            auto consume_scope_resolution =
                [&](size_t& offset) -> bool {
                    Token tok = peek_token_shortcut(offset);
                    if (tok.type == TokenType::SCOPE_RESOLUTION) {
                        ++offset;
                        return true;
                    }
                    if (tok.type == TokenType::COLON &&
                        peek_token_shortcut(offset + 1).type == TokenType::COLON) {
                        offset += 2;
                        return true;
                    }
                    return false;
                };
            auto skip_balanced_tokens =
                [&](size_t& offset,
                    TokenType open_tok,
                    TokenType close_tok) -> bool {
                if (peek_token_shortcut(offset).type != open_tok) {
                    return false;
                }
                int depth = 0;
                while (peek_token_shortcut(offset).type != TokenType::Eof) {
                    TokenType tok = peek_token_shortcut(offset).type;
                    if (tok == open_tok) {
                        ++depth;
                    } else if (tok == close_tok) {
                        --depth;
                        if (depth == 0) {
                            ++offset;
                            return true;
                        }
                    }
                    ++offset;
                }
                return false;
            };
            auto skip_explicit_specifier =
                [&](size_t& offset) -> bool {
                if (peek_token_shortcut(offset).type != TokenType::EXPLICIT_KW) {
                    return false;
                }
                ++offset;
                if (peek_token_shortcut(offset).type == TokenType::LEFT_PAREN) {
                    skip_balanced_tokens(
                        offset,
                        TokenType::LEFT_PAREN,
                        TokenType::RIGHT_PAREN);
                }
                return true;
            };

            size_t offset = 0;
            bool saw_scope_resolution = false;
            skip_explicit_specifier(offset);
            TokenType toktype = peek_token_shortcut(offset).type;
            if (toktype == TokenType::OPERATOR_KW) {
                return true;
            }

            if (consume_scope_resolution(offset)) {
                saw_scope_resolution = true;
            }

            while (peek_token_shortcut(offset).type == TokenType::IDENTIFIER) {
                ++offset;
                if (!consume_scope_resolution(offset)) {
                    break;
                }
                saw_scope_resolution = true;
            }
            return saw_scope_resolution &&
                   peek_token_shortcut(offset).type == TokenType::OPERATOR_KW;
        };

    if (looks_like_typeless_cpp_conversion_declaration()) {
        decl_parser.begin_loc = current_token().loc;
        decl_parser.first_half = nullptr;
        decl_parser.base_qualifiers = QUAL_NONE;
        decl_parser.qualifiers = QUAL_NONE;
        return nullptr;
    }

    validate_declaration_start(start_token);

    bool enable_implicit_int_for_decl =
        !lang_opts.implicit_int &&
        current_token().type == TokenType::IDENTIFIER &&
        peek_token().type == TokenType::LEFT_PAREN;
    bool saved_implicit_int = lang_opts.implicit_int;
    bool saved_implicit_func_decl = lang_opts.implicit_function_declarations;
    if (enable_implicit_int_for_decl) {
        lang_opts.implicit_int = true;
        lang_opts.implicit_function_declarations = true;
        collect_->set_lang_options(lang_opts);
    }
    std::shared_ptr<CType> parsed_type;
    try {
        parsed_type = decl_parser.parse_declaration(false);
    } catch (...) {
        if (enable_implicit_int_for_decl) {
            lang_opts.implicit_int = saved_implicit_int;
            lang_opts.implicit_function_declarations = saved_implicit_func_decl;
            collect_->set_lang_options(lang_opts);
        }
        throw;
    }
    if (enable_implicit_int_for_decl) {
        lang_opts.implicit_int = saved_implicit_int;
        // Keep implicit function declarations enabled after old-style
        // implicit-int declarations to support GNU89/K&R call sites.
        lang_opts.implicit_function_declarations = true;
        collect_->set_lang_options(lang_opts);
    }
    emit_declaration_head_side_decls(decl_parser, parsed_type, ret_vec);
    return parsed_type;
}

Parser::QualifiedDeclaratorContext Parser::prepare_qualified_declarator_context(
    DeclarationParser& decl_parser) {
    decl_parser.reset_declarator_parsing_state();

    QualifiedDeclaratorContext context;
    context.info.loc = current_token().loc;
    context.scope_snapshot.scope = collect_->collect_current_scope();
    context.scope_snapshot.decl_context = collect_->get_current_decl_context();

    auto starts_with_member_pointer_declarator_prefix = [&]() -> bool {
        if (!is_cxx_mode_active() || !gentle_check(TokenType::IDENTIFIER)) {
            return false;
        }
        size_t offset = 1;
        Token sep = peek_token(offset);
        if (sep.type == TokenType::SCOPE_RESOLUTION) {
            ++offset;
        } else if (sep.type == TokenType::COLON &&
                   peek_token(offset + 1).type == TokenType::COLON) {
            offset += 2;
        } else {
            return false;
        }
        return peek_token(offset).type == TokenType::MULTIPLY;
    };

    struct QualifiedDeclaratorComponent {
        std::string name;
        std::vector<TemplateArgument> template_arguments;
        bool has_template_argument_list = false;

        std::string spelling() const {
            if (!has_template_argument_list) {
                return name;
            }
            std::string spelled = name;
            spelled += "<";
            for (size_t idx = 0; idx < template_arguments.size(); ++idx) {
                if (idx > 0) {
                    spelled += ", ";
                }
                spelled += template_arguments[idx].to_string();
            }
            spelled += ">";
            return spelled;
        }
    };

    auto qualified_declarator_matches_primary_class_template_owner =
        [&](const ClassTemplateDecl* class_template,
            const std::vector<TemplateArgument>& arguments) -> bool {
            return cpp_primary_template_owner_matches(class_template, arguments);
        };

    auto skip_leading_declarator_prefix_tokens =
        [&]() {
            auto consume_post_pointer_qualifiers = [&]() {
                while (true) {
                    if (gentle_check(TokenType::CONST) ||
                        gentle_check(TokenType::VOLATILE) ||
                        gentle_check(TokenType::RESTRICT) ||
                        gentle_check(TokenType::ATOMIC) ||
                        gentle_check(TokenType::NULLABILITY_QUALIFIER)) {
                        advance();
                        continue;
                    }
                    if (is_gnu_attribute_token(current_token())) {
                        try_parse_attributes();
                        continue;
                    }
                    break;
                }
            };

            while (true) {
                if (gentle_check(TokenType::MULTIPLY) ||
                    gentle_check(TokenType::BITWISE_XOR)) {
                    advance();
                    consume_post_pointer_qualifiers();
                    continue;
                }
                if (gentle_check(TokenType::LOGICAL_AND)) {
                    advance();
                    continue;
                }
                if (gentle_check(TokenType::BITWISE_AND)) {
                    advance();
                    continue;
                }
                break;
            }
        };

    if (!is_cxx_mode_active() || starts_with_member_pointer_declarator_prefix()) {
        return context;
    }

    bool has_global_qualifier = false;
    std::vector<QualifiedDeclaratorComponent> qualifier_components;
    std::vector<std::string> qualifier_component_spellings;
    std::optional<size_t> terminal_token_idx;
    {
        RevertingTentativeParsingAction tentative(*this);
        context.info.loc = current_token().loc;
        skip_leading_declarator_prefix_tokens();
        context.info.loc = current_token().loc;
        has_global_qualifier = consume_cpp_scope_resolution();
        auto parse_qualified_component =
            [&]() -> std::pair<QualifiedDeclaratorComponent, size_t> {
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected identifier after '::' in qualified-id declarator",
                    current_token().loc);
            }
            QualifiedDeclaratorComponent component;
            size_t ident_token_idx = get_token_idx();
            component.name = current_token().value;
            advance();
            if (gentle_check(TokenType::LESS_THAN)) {
                component.has_template_argument_list = true;
                component.template_arguments =
                    parse_cpp_template_argument_list();
            }
            return {std::move(component), ident_token_idx};
        };
        if (has_global_qualifier && gentle_check(TokenType::OPERATOR_KW)) {
            terminal_token_idx = get_token_idx();
        } else if (has_global_qualifier || gentle_check(TokenType::IDENTIFIER)) {
            if (!gentle_check(TokenType::IDENTIFIER)) {
                error_custloc(
                    "expected identifier after '::' in qualified-id declarator",
                    current_token().loc);
            }
            auto [component, ident_token_idx] = parse_qualified_component();
            while (is_cpp_scope_resolution_here()) {
                consume_cpp_scope_resolution();
                qualifier_component_spellings.push_back(component.spelling());
                qualifier_components.push_back(std::move(component));
                if (gentle_check(TokenType::OPERATOR_KW)) {
                    terminal_token_idx = get_token_idx();
                    break;
                }
                auto next_component = parse_qualified_component();
                component = std::move(next_component.first);
                ident_token_idx = next_component.second;
            }
            if (!terminal_token_idx.has_value() &&
                (has_global_qualifier || !qualifier_components.empty())) {
                terminal_token_idx = ident_token_idx;
            }
        }
    }

    if (!terminal_token_idx.has_value()) {
        return context;
    }

    auto current_scope = collect_->collect_current_scope();
    auto tu_context = collect_->get_translation_unit_decl_context();
    auto current_context = collect_->get_current_decl_context();
    if (!current_scope || !tu_context || !current_context) {
        diag_engine->report_error(
            "internal error: namespace lookup context missing",
            context.info.loc);
        error_custloc("namespace lookup context missing", context.info.loc);
    }
    auto global_scope = current_scope;
    while (global_scope && global_scope->parent) {
        global_scope = global_scope->parent;
    }
    if (!global_scope) {
        diag_engine->report_error(
            "internal error: global scope missing",
            context.info.loc);
        error_custloc("global scope missing", context.info.loc);
    }

    auto lookup_scope = has_global_qualifier ? global_scope : current_scope;
    const DeclContext* lookup_context =
        has_global_qualifier ? tu_context.get() : current_context.get();
    for (size_t idx = 0; idx < qualifier_components.size(); ++idx) {
        bool allow_enclosing_lookup = (!has_global_qualifier && idx == 0);
        bool is_last_component = idx + 1 == qualifier_components.size();
        const auto& component = qualifier_components[idx];
        if (component.has_template_argument_list && !is_last_component) {
            fail_cpp_future_work(
                "template-id nested-name specifier",
                "template-id qualifier chains",
                context.info.loc);
        }
        auto namespace_scope = resolve_named_namespace_scope(
            lookup_context, component.name, allow_enclosing_lookup);
        if (namespace_scope && namespace_scope->associated_decl_context) {
            lookup_scope = namespace_scope;
            lookup_context = namespace_scope->associated_decl_context;
            continue;
        }
        if (!lookup_scope) {
            error_custloc(
                "internal error: missing lookup scope while resolving nested-name specifier",
                context.info.loc);
        }
        if (!is_last_component) {
            error_custloc(
                "nested-name specifier component '" +
                    component.spelling() +
                    "' does not name a namespace",
                context.info.loc);
        }

        if (component.has_template_argument_list) {
            const DeclBinding* template_binding =
                LookupEngine::lookup_unqualified_template_binding(
                    component.name,
                    lookup_scope,
                    allow_enclosing_lookup,
                    LookupNamespace::Tag);
            const Decl* primary_template = nullptr;
            if (template_binding) {
                primary_template = template_binding->template_decl;
                if (!primary_template &&
                    template_binding->template_overload_candidates.size() == 1) {
                    primary_template =
                        template_binding->template_overload_candidates.front();
                }
            }
            auto* class_template =
                dyn_cast<ClassTemplateDecl>(primary_template);
            if (!class_template) {
                error_custloc(
                    "out-of-line declaration target '" +
                        component.spelling() +
                        "' does not name the primary class template pattern",
                    context.info.loc);
            }
            context.info.owner_class_template = class_template;
            context.info.owner_template_arguments = component.template_arguments;
            context.info.owner_has_specialization_argument_list =
                component.has_template_argument_list;
            if (!qualified_declarator_matches_primary_class_template_owner(
                    class_template,
                    component.template_arguments)) {
                if (!is_parsing_cpp_explicit_specialization()) {
                    error_custloc(
                        "out-of-line declaration target '" +
                            component.spelling() +
                            "' does not name the primary class template pattern",
                        context.info.loc);
                }
                context.info.targets_template_pattern = false;
            } else {
                context.info.targets_template_pattern = true;
            }
            context.info.owner_record_decl =
                class_template->pattern_semantic_decl();
            if (!context.info.owner_record_decl) {
                error_custloc(
                    "internal error: missing primary class template pattern owner",
                    context.info.loc);
            }
        } else {
            auto* owner_tag_decl = LookupEngine::lookup_tag_decl(
                component.name,
                lookup_scope,
                allow_enclosing_lookup);
            const auto* owner_record_decl = dyn_cast<ObjectDecl>(owner_tag_decl);
            if (!owner_record_decl) {
                error_custloc(
                    "out-of-line declaration target '" +
                        component.spelling() +
                        "' is not a class/struct/union",
                    context.info.loc);
            }
            if (owner_record_decl->get_record_type()) {
                if (auto* canonical_owner =
                        dyn_cast<ObjectDecl>(
                            owner_record_decl->get_record_type()->get_decl())) {
                    owner_record_decl = canonical_owner;
                }
            }
            context.info.owner_record_decl = owner_record_decl;
            context.info.owner_has_specialization_argument_list = false;
            context.info.targets_template_pattern = false;
        }
        break;
    }

    if (context.info.owner_record_decl &&
        context.scope_snapshot.scope &&
        scope_flags_contains(
            context.scope_snapshot.scope->flags,
            ScopeFlags::TemplateParameterScope) &&
        context.scope_snapshot.decl_context) {
        auto rebased_scope =
            std::make_shared<Scope>(*context.scope_snapshot.scope);
        rebased_scope->parent = lookup_scope;
        rebased_scope->associated_decl_context =
            context.scope_snapshot.decl_context.get();
        collect_->collect_set_current_scope(std::move(rebased_scope));
    } else {
        collect_->collect_set_current_scope(lookup_scope);
    }
    if (!context.info.owner_record_decl) {
        context.info.target_context =
            collect_->get_current_decl_context();
        context.info.target_scope =
            collect_->collect_current_scope();
        if (!context.info.target_context) {
            diag_engine->report_error(
                "internal error: namespace declaration context missing",
                context.info.loc);
            error_custloc("namespace declaration context missing",
                          context.info.loc);
        }
    }
    context.info.has_global_qualifier = has_global_qualifier;
    context.info.qualifiers = std::move(qualifier_component_spellings);
    return context;
}

bool Parser::qualified_variable_types_compatible(QualType declared_type,
                                                 QualType member_type) {
    declared_type = desugar_type(declared_type);
    member_type = desugar_type(member_type);
    if (!declared_type || !member_type) {
        return declared_type.get_shared() == member_type.get_shared();
    }
    if (declared_type.equals_qualified(member_type) ||
        declared_type.equals_unqualified(member_type) ||
        cpp_out_of_line_type_matches(declared_type, member_type, false)) {
        return true;
    }
    auto declared_arr = declared_type.as_shared<ArrayType>();
    auto member_arr = member_type.as_shared<ArrayType>();
    if (!declared_arr || !member_arr) {
        return false;
    }
    if (!declared_arr->element_type.equals_qualified(member_arr->element_type)) {
        return false;
    }
    bool declared_complete =
        declared_arr->size_kind == ArraySizeKind::Constant &&
        declared_arr->size.has_value();
    bool member_complete =
        member_arr->size_kind == ArraySizeKind::Constant &&
        member_arr->size.has_value();
    if (declared_complete && member_complete) {
        return declared_arr->size.value() == member_arr->size.value();
    }
    return true;
}

bool Parser::record_method_signature_matches(
    const RecordSemanticState::Method& method,
    const std::shared_ptr<CType>& parsed_decl_type,
    uint8_t parsed_trailing_cv_qualifiers) {
    auto parsed_fn_type =
        desugar_type(QualType(parsed_decl_type)).as_shared<FunctionType>();
    auto method_fn_type = desugar_type(method.type).as_shared<FunctionType>();
    if (!parsed_fn_type || !method_fn_type) {
        return false;
    }
    if (parsed_fn_type->is_variadic != method_fn_type->is_variadic) {
        return false;
    }
    if (parsed_fn_type->has_explicit_exception_spec !=
        method_fn_type->has_explicit_exception_spec) {
        return false;
    }
    if (!function_exception_specs_equal(*parsed_fn_type, *method_fn_type)) {
        return false;
    }
    if (!cpp_out_of_line_type_matches(
            parsed_fn_type->ret_type,
            method_fn_type->ret_type,
            true)) {
        return false;
    }

    size_t method_user_param_start = method.is_static ? 0 : 1;
    if (method_fn_type->parameters.size() < method_user_param_start) {
        return false;
    }
    size_t method_user_param_count =
        method_fn_type->parameters.size() - method_user_param_start;
    if (parsed_fn_type->parameters.size() != method_user_param_count) {
        return false;
    }
    for (size_t idx = 0; idx < parsed_fn_type->parameters.size(); ++idx) {
        if (!cpp_out_of_line_type_matches(
                parsed_fn_type->parameters[idx],
                method_fn_type->parameters[method_user_param_start + idx],
                true)) {
            return false;
        }
    }

    uint8_t parsed_cv =
        parsed_trailing_cv_qualifiers &
        static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE);
    if (method.is_static) {
        return parsed_cv == QUAL_NONE;
    }

    if (method_fn_type->parameters.empty()) {
        return false;
    }
    auto this_ptr_type =
        desugar_type(method_fn_type->parameters.front()).as_shared<PointerType>();
    if (!this_ptr_type) {
        return false;
    }
    uint8_t expected_cv =
        this_ptr_type->pointed_type.get_qualifiers() &
        static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE);
    return parsed_cv == expected_cv;
}

bool Parser::active_template_parameter_list_matches(
    const TemplateParameterList& parameters) {
    if (active_template_parameter_stack_.empty()) {
        return false;
    }
    const auto& active_parameters = active_template_parameter_stack_.back();
    if (active_parameters.size() != parameters.size()) {
        return false;
    }
    for (size_t idx = 0; idx < parameters.size(); ++idx) {
        const auto* active_parameter = active_parameters[idx];
        const auto* existing_parameter = parameters[idx].get();
        if (!active_parameter || !existing_parameter ||
            active_parameter->get_kind() != existing_parameter->get_kind() ||
            active_parameter->is_parameter_pack !=
                existing_parameter->is_parameter_pack) {
            return false;
        }
        if (auto* active_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(active_parameter)) {
            auto* existing_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(existing_parameter);
            if (!existing_non_type ||
                !cpp_out_of_line_type_matches(
                    active_non_type->type,
                    existing_non_type->type,
                    false)) {
                return false;
            }
        }
    }
    return true;
}

bool Parser::record_method_template_signature_matches(
    const RecordSemanticState::MethodTemplate& method_template,
    const std::shared_ptr<CType>& parsed_decl_type,
    uint8_t parsed_trailing_cv_qualifiers) {
    if (!method_template.decl || !method_template.decl->function_decl() ||
        !active_template_parameter_list_matches(
            method_template.decl->parameters)) {
        return false;
    }
    RecordSemanticState::Method synthetic_method;
    synthetic_method.type =
        QualType(method_template.decl->function_decl()->type);
    synthetic_method.is_static = method_template.is_static;
    return record_method_signature_matches(
        synthetic_method,
        parsed_decl_type,
        parsed_trailing_cv_qualifiers);
}

bool Parser::record_method_template_explicit_specialization_matches(
    const RecordSemanticState::MethodTemplate& method_template,
    const std::shared_ptr<CType>& parsed_decl_type,
    uint8_t parsed_trailing_cv_qualifiers,
    const ClassTemplateDecl* owner_class_template,
    const std::vector<TemplateArgument>& owner_template_arguments,
    bool owner_has_specialization_argument_list,
    bool targets_template_pattern,
    SrcLoc declarator_loc,
    std::vector<TemplateArgument>& deduced_arguments_out) {
    deduced_arguments_out.clear();
    if (!is_parsing_cpp_explicit_specialization() ||
        !method_template.decl ||
        !method_template.decl->function_decl() ||
        !parsed_decl_type) {
        return false;
    }

    QualType pattern_type(method_template.decl->function_decl()->type);
    if (owner_class_template &&
        owner_has_specialization_argument_list &&
        !targets_template_pattern) {
        pattern_type = collect_->collect_partially_substitute_template_type(
            pattern_type,
            owner_class_template->parameters,
            owner_template_arguments,
            declarator_loc);
    }

    return collect_->deduce_function_template_specialization_arguments_from_pattern(
        pattern_type,
        method_template.decl->parameters,
        method_template.decl,
        QualType(parsed_decl_type),
        deduced_arguments_out,
        nullptr,
        parsed_trailing_cv_qualifiers,
        method_template.is_static ? 0u : 1u);
}

void Parser::resolve_qualified_declarator_match(
    QualifiedDeclaratorInfo& qualified_declarator,
    const DeclarationParser& decl_parser,
    const std::shared_ptr<CType>& parsed_decl_type) {
    if (qualified_declarator.target_context) {
        auto prior_decls = LookupEngine::lookup_qualified_ordinary_bindings(
            decl_parser.name,
            qualified_declarator.target_context.get(),
            qualified_declarator.target_scope,
            LookupEngine::OrdinaryFilter::Any,
            LookupEngine::NamespaceReachability::InlineVisible);
        const LookupEngine::QualifiedOrdinaryBindingMatch* matched_prior_decl =
            nullptr;
        if (canonical_type_kind(parsed_decl_type) == TypeKind::Function) {
            QualType declared_function_type = desugar_type(QualType(parsed_decl_type));
            for (const auto& prior_decl : prior_decls) {
                if (!namespace_function_prior_match(
                        prior_decl.binding,
                        declared_function_type)) {
                    continue;
                }
                matched_prior_decl = &prior_decl;
                break;
            }
        } else {
            for (const auto& prior_decl : prior_decls) {
                if (!namespace_variable_prior_match(prior_decl.binding)) {
                    continue;
                }
                matched_prior_decl = &prior_decl;
                break;
            }
        }
        if (!matched_prior_decl) {
            error_custloc(
                "out-of-line declaration of '" +
                    qualified_name_utils::format_cpp_qualified_name(
                        qualified_declarator.has_global_qualifier,
                        qualified_declarator.qualifiers,
                        decl_parser.name) +
                    "' does not match any declaration in the target namespace",
                qualified_declarator.loc);
        }
        if (matched_prior_decl->owner_context &&
            matched_prior_decl->owner_context !=
                qualified_declarator.target_context.get()) {
            if (!matched_prior_decl->owner_scope) {
                error_custloc(
                    "internal error: missing owning scope for inline namespace member declaration",
                    qualified_declarator.loc);
            }
            collect_->collect_set_current_scope(matched_prior_decl->owner_scope);
            qualified_declarator.target_context =
                collect_->get_current_decl_context();
            qualified_declarator.target_scope =
                collect_->collect_current_scope();
        }
        return;
    }

    if (!qualified_declarator.owner_record_decl) {
        return;
    }

    const RecordSemanticState* owner_state =
        collect_->query_lookup_record_semantics(
            qualified_declarator.owner_record_decl);
    if (!owner_state || owner_state->is_incomplete) {
        std::vector<std::string> owner_qualifiers = qualified_declarator.qualifiers;
        std::string owner_terminal;
        if (!owner_qualifiers.empty()) {
            owner_terminal = owner_qualifiers.back();
            owner_qualifiers.pop_back();
        } else if (qualified_declarator.owner_record_decl) {
            owner_terminal = qualified_declarator.owner_record_decl->tag;
        }
        error_custloc(
            "incomplete type '" +
                qualified_name_utils::format_cpp_qualified_name(
                    qualified_declarator.has_global_qualifier,
                    owner_qualifiers,
                    owner_terminal) +
                "' named in nested name specifier",
            qualified_declarator.loc);
    }

    std::string qualified_name = qualified_name_utils::format_cpp_qualified_name(
        qualified_declarator.has_global_qualifier,
        qualified_declarator.qualifiers,
        decl_parser.name);
    if (canonical_type_kind(parsed_decl_type) == TypeKind::Function) {
        bool saw_method_name_match = false;
        bool saw_method_template_name_match = false;
        for (const auto& method : owner_state->methods) {
            if (method.name != decl_parser.name) {
                continue;
            }
            saw_method_name_match = true;
            if (!record_method_signature_matches(
                    method,
                    parsed_decl_type,
                    decl_parser.trailing_function_cv_qualifiers)) {
                continue;
            }
            qualified_declarator.method_match = &method;
            break;
        }
        if (!qualified_declarator.method_match) {
            for (const auto& method_template : owner_state->method_templates) {
                if (method_template.name != decl_parser.name) {
                    continue;
                }
                saw_method_name_match = true;
                saw_method_template_name_match = true;
                if (record_method_template_signature_matches(
                        method_template,
                        parsed_decl_type,
                        decl_parser.trailing_function_cv_qualifiers)) {
                    qualified_declarator.method_template_match = &method_template;
                    qualified_declarator
                        .method_template_specialization_arguments.clear();
                    break;
                }
                if (record_method_template_explicit_specialization_matches(
                        method_template,
                        parsed_decl_type,
                        decl_parser.trailing_function_cv_qualifiers,
                        qualified_declarator.owner_class_template,
                        qualified_declarator.owner_template_arguments,
                        qualified_declarator
                            .owner_has_specialization_argument_list,
                        qualified_declarator.targets_template_pattern,
                        qualified_declarator.loc,
                        qualified_declarator
                            .method_template_specialization_arguments)) {
                    qualified_declarator.method_template_match = &method_template;
                    break;
                }
            }
        }
        if (!qualified_declarator.method_match &&
            !qualified_declarator.method_template_match) {
            if (saw_method_name_match) {
                error_custloc(
                    "conflicting types for '" + qualified_name + "'",
                    qualified_declarator.loc);
            }
            error_custloc(
                "out-of-line declaration of '" + qualified_name +
                    "' does not match any declaration in the target class",
                qualified_declarator.loc);
        }
        return;
    }

    bool saw_name_match = false;
    QualType declared_member_type(parsed_decl_type, decl_parser.qualifiers);
    for (const auto& static_member : owner_state->static_data_members) {
        if (static_member.name != decl_parser.name) {
            continue;
        }
        saw_name_match = true;
        if (!qualified_variable_types_compatible(
                declared_member_type, static_member.type)) {
            continue;
        }
        qualified_declarator.static_data_match = &static_member;
        break;
    }

    if (!qualified_declarator.static_data_match) {
        if (saw_name_match) {
            error_custloc(
                "conflicting types for '" + qualified_name + "'",
                qualified_declarator.loc);
        }
        error_custloc(
            "out-of-line declaration of '" + qualified_name +
                "' does not match any declaration in the target class",
            qualified_declarator.loc);
    }
}

void Parser::merge_function_asm_label(DeclarationParser& decl_parser,
                                      const std::shared_ptr<Symbol>& sym,
                                      SrcLoc loc) {
    if (!sym) {
        return;
    }
    if (decl_parser.asm_label.has_value()) {
        if (sym->asm_label.has_value() &&
            sym->asm_label.value() != decl_parser.asm_label.value()) {
            diag_engine->report_error(
                "conflicting asm label for function '" + decl_parser.name + "'",
                loc);
            // Keep the previously established asm label as canonical.
            decl_parser.asm_label = sym->asm_label;
            return;
        }
        sym->asm_label = decl_parser.asm_label;
        return;
    }
    if (sym->asm_label.has_value()) {
        // Preserve asm label from a prior declaration on later redeclarations/definition.
        decl_parser.asm_label = sym->asm_label;
    }
}

void Parser::remap_out_of_line_primary_template_method(
    CppMethodDecl* method_decl,
    const ClassTemplateDecl* owner_class_template,
    SrcLoc declarator_loc) {
    if (!method_decl ||
        !owner_class_template ||
        active_template_parameter_stack_.empty()) {
        return;
    }

    const auto& active_parameters = active_template_parameter_stack_.back();
    if (active_parameters.size() != owner_class_template->parameters.size()) {
        error_custloc(
            "internal error: out-of-line template head does not match owner template parameter list",
            declarator_loc);
    }

    ASTCloneContext clone_ctx;
    clone_ctx.ast_ctx = ast_ctx.get();
    std::unordered_map<const TemplateParameterDecl*, const TemplateParameterDecl*>
        parameter_rebinds;
    parameter_rebinds.reserve(active_parameters.size());

    for (size_t idx = 0; idx < active_parameters.size(); ++idx) {
        const auto* active_parameter = active_parameters[idx];
        const auto* canonical_parameter =
            owner_class_template->parameters[idx].get();
        if (!active_parameter || !canonical_parameter ||
            active_parameter->get_kind() != canonical_parameter->get_kind()) {
            error_custloc(
                "internal error: out-of-line template head is not structurally compatible with the owner template",
                declarator_loc);
        }
        parameter_rebinds.emplace(active_parameter, canonical_parameter);

        if (auto* canonical_type =
                dyn_cast<TemplateTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(canonical_parameter))) {
            (void)canonical_type;
            continue;
        }

        if (auto* canonical_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(canonical_parameter))) {
            auto* active_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(active_parameter));
            if (active_non_type && active_non_type->sym &&
                canonical_non_type->sym) {
                clone_ctx.symbol_remap.emplace(
                    active_non_type->sym.get(),
                    canonical_non_type->sym);
            }
            continue;
        }

        error_custloc(
            "internal error: unsupported out-of-line owner template parameter kind",
            declarator_loc);
    }

    clone_ctx.rewrite_type = [&](QualType type) -> QualType {
        return template_sema_internal::remap_template_parameter_types_in_type(
            type,
            parameter_rebinds);
    };
    clone_ctx.rewrite_symbol =
        [&](const std::shared_ptr<Symbol>& sym) -> std::shared_ptr<Symbol> {
        if (!sym) {
            return nullptr;
        }
        if (auto it = clone_ctx.symbol_remap.find(sym.get());
            it != clone_ctx.symbol_remap.end()) {
            return it->second;
        }
        return sym;
    };

    method_decl->type =
        clone_ctx.rewrite_type(QualType(method_decl->type)).get_shared();

    std::vector<std::unique_ptr<Decl>> remapped_parameters;
    remapped_parameters.reserve(method_decl->parameters.size());
    for (const auto& parameter : method_decl->parameters) {
        std::string clone_error;
        auto remapped_parameter =
            clone_decl_tree(parameter.get(), clone_ctx, &clone_error);
        if (!remapped_parameter) {
            error_custloc(
                clone_error.empty()
                    ? "failed to remap out-of-line template method parameter"
                    : clone_error,
                parameter ? parameter->location : declarator_loc);
        }
        remapped_parameters.push_back(std::move(remapped_parameter));
    }
    method_decl->parameters = std::move(remapped_parameters);

    if (method_decl->body) {
        std::string clone_error;
        auto remapped_body =
            clone_stmt_tree(method_decl->body.get(), clone_ctx, &clone_error);
        if (!remapped_body) {
            error_custloc(
                clone_error.empty()
                    ? "failed to remap out-of-line template method body"
                    : clone_error,
                method_decl->body->location);
        }
        method_decl->body = std::move(remapped_body);
    }
}

void Parser::remap_out_of_line_primary_template_static_member(
    QualType& declared_type,
    std::unique_ptr<Expr>& init_expr,
    const ClassTemplateDecl* owner_class_template,
    SrcLoc declarator_loc) {
    if (!owner_class_template || active_template_parameter_stack_.empty()) {
        return;
    }

    const auto& active_parameters = active_template_parameter_stack_.back();
    if (active_parameters.size() != owner_class_template->parameters.size()) {
        error_custloc(
            "internal error: out-of-line template head does not match owner template parameter list",
            declarator_loc);
    }

    ASTCloneContext clone_ctx;
    clone_ctx.ast_ctx = ast_ctx.get();
    std::unordered_map<const TemplateParameterDecl*, const TemplateParameterDecl*>
        parameter_rebinds;
    parameter_rebinds.reserve(active_parameters.size());

    for (size_t idx = 0; idx < active_parameters.size(); ++idx) {
        const auto* active_parameter = active_parameters[idx];
        const auto* canonical_parameter =
            owner_class_template->parameters[idx].get();
        if (!active_parameter || !canonical_parameter ||
            active_parameter->get_kind() != canonical_parameter->get_kind()) {
            error_custloc(
                "internal error: out-of-line template head is not structurally compatible with the owner template",
                declarator_loc);
        }
        parameter_rebinds.emplace(active_parameter, canonical_parameter);

        if (auto* canonical_type =
                dyn_cast<TemplateTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(canonical_parameter))) {
            (void)canonical_type;
            continue;
        }

        if (auto* canonical_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(canonical_parameter))) {
            auto* active_non_type =
                dyn_cast<TemplateNonTypeParmDecl>(
                    const_cast<TemplateParameterDecl*>(active_parameter));
            if (active_non_type && active_non_type->sym &&
                canonical_non_type->sym) {
                clone_ctx.symbol_remap.emplace(
                    active_non_type->sym.get(),
                    canonical_non_type->sym);
            }
            continue;
        }

        error_custloc(
            "internal error: unsupported out-of-line owner template parameter kind",
            declarator_loc);
    }

    clone_ctx.rewrite_type = [&](QualType type) -> QualType {
        return template_sema_internal::remap_template_parameter_types_in_type(
            type,
            parameter_rebinds);
    };
    clone_ctx.rewrite_symbol =
        [&](const std::shared_ptr<Symbol>& sym) -> std::shared_ptr<Symbol> {
        if (!sym) {
            return nullptr;
        }
        if (auto it = clone_ctx.symbol_remap.find(sym.get());
            it != clone_ctx.symbol_remap.end()) {
            return it->second;
        }
        return sym;
    };

    declared_type = clone_ctx.rewrite_type(declared_type);

    if (init_expr) {
        std::string clone_error;
        auto remapped_init =
            clone_expr_with_substitution(
                init_expr.get(),
                clone_ctx,
                &clone_error);
        if (!remapped_init) {
            error_custloc(
                clone_error.empty()
                    ? "failed to remap out-of-line template static data member initializer"
                    : clone_error,
                init_expr->location);
        }
        init_expr = std::move(remapped_init);
    }
}

Parser::DeclaratorHandlingResult Parser::handle_typedef_declarator(
    DeclarationParser& decl_parser,
    Token declarator_token,
    std::shared_ptr<CType>& parsed_decl_type,
    std::vector<ParsedAttribute>& trailing_attrs,
    bool declaration_is_constexpr,
    bool declaration_is_consteval,
    std::vector<std::unique_ptr<Decl>>& ret_vec) {
    if (decl_parser.explicit_specifier.is_present) {
        error_custloc(
            "'explicit' is only allowed on constructors and conversion functions",
            decl_parser.explicit_specifier.location);
    }
    if (decl_parser.is_mutable) {
        error_custloc(
            "'mutable' cannot be applied to typedef declarations",
            decl_parser.begin_loc);
    }
    if (declaration_is_constexpr || declaration_is_consteval) {
        error("'constexpr' or 'consteval' cannot be combined with 'typedef'");
    }
    if (gentle_check(TokenType::ASSIGN)) {
        error("illegal initializer in typedef (typedefs do not declare objects)");
    }
    auto all_attrs_for_typedef = decl_parser.leading_attrs;
    all_attrs_for_typedef.insert(
        all_attrs_for_typedef.end(),
        trailing_attrs.begin(),
        trailing_attrs.end());
    for (const auto& attr : all_attrs_for_typedef) {
        std::string canon = attr.canonical_name();
        if (canon == "vector_size" && !attr.args.empty() &&
            attr.args[0].kind == AttributeArg::Kind::INTEGER) {
            if (parsed_decl_type &&
                canonical_type_kind(parsed_decl_type) == TypeKind::Vector) {
                continue;
            }
            size_t vec_bytes = static_cast<size_t>(attr.args[0].int_value);
            auto base = parsed_decl_type;
            if (!base->isArithmetic() || base->isVoid()) {
                error("vector_size attribute requires an integer or floating-point base type");
            }
            if (vec_bytes == 0 || (vec_bytes & (vec_bytes - 1)) != 0) {
                error("vector_size must be a power of 2");
            }
            int64_t elem_bytes = base->getWidthBytes();
            if (elem_bytes <= 0 ||
                vec_bytes % static_cast<size_t>(elem_bytes) != 0) {
                error("vector_size must be a multiple of the base type size");
            }
            parsed_decl_type =
                std::make_shared<VectorType>(QualType(parsed_decl_type), vec_bytes);
            continue;
        }
        if (canon == "transparent_union") {
            auto obj = dyn_cast_shared<ObjectType>(parsed_decl_type);
            if (obj && obj->is_union) {
                obj->is_transparent_union = true;
            }
        }
    }
    auto typedef_underlying =
        QualType(parsed_decl_type, decl_parser.qualifiers);
    auto td_sym = collect_->collect_declare_typedef_symbol(
        decl_parser.name, typedef_underlying, declarator_token.loc);
    if (td_sym) {
        for (const auto& attr : decl_parser.leading_attrs) {
            td_sym->sym_attrs.attrs.push_back(attr);
        }
        for (const auto& attr : trailing_attrs) {
            td_sym->sym_attrs.attrs.push_back(attr);
        }
    }
    auto typedef_decl = collect_->collect_typedef_declaration(
        decl_parser.name,
        td_sym ? td_sym->type : typedef_underlying,
        td_sym,
        declarator_token.loc);
    if (td_sym && td_sym->type->kind == TypeKind::Typedef) {
        auto ttype = td_sym->type.as<TypedefType>();
        auto tdecl = dyn_cast<TypedefDecl>(typedef_decl.get());
        ttype->typedef_decl = tdecl;
    }
    ret_vec.push_back(std::move(typedef_decl));
    return DeclaratorHandlingResult::Continue;
}

Parser::DeclaratorHandlingResult Parser::handle_function_declarator(
    DeclarationParser& decl_parser,
    Token declarator_token,
    const std::shared_ptr<CType>& parsed_decl_type,
    std::vector<ParsedAttribute>& trailing_attrs,
    StorageClass storage_class,
    bool declaration_is_constexpr,
    bool declaration_is_consteval,
    LanguageLinkage declaration_language_linkage,
    QualifiedDeclaratorInfo& qualified_declarator,
    std::vector<std::unique_ptr<Decl>>& ret_vec) {
    if (decl_parser.explicit_specifier.is_present) {
        error_custloc(
            qualified_declarator.owner_record_decl
                ? "'explicit' is only allowed on declarations inside a class definition"
                : "'explicit' is only allowed on constructors and conversion functions",
            decl_parser.explicit_specifier.location);
    }
    if (decl_parser.is_mutable) {
        error_custloc(
            "'mutable' cannot be applied to functions",
            decl_parser.begin_loc);
    }
    if (qualified_declarator.owner_record_decl) {
        bool matched_member_template =
            qualified_declarator.method_template_match != nullptr;
        bool preserve_member_template_explicit_specialization =
            is_parsing_cpp_explicit_specialization() &&
            matched_member_template;
        bool preserve_ordinary_member_explicit_specialization =
            is_parsing_cpp_explicit_specialization() &&
            qualified_declarator.owner_class_template != nullptr &&
            qualified_declarator.owner_has_specialization_argument_list &&
            !matched_member_template &&
            !qualified_declarator.targets_template_pattern;
        bool preserve_explicit_specialization_member_decl =
            preserve_member_template_explicit_specialization ||
            preserve_ordinary_member_explicit_specialization;
        auto method_sym =
            preserve_explicit_specialization_member_decl
                ? nullptr
                : qualified_declarator.method_match
                ? qualified_declarator.method_match->symbol
                : nullptr;
        if (!preserve_explicit_specialization_member_decl &&
            !matched_member_template &&
            (!qualified_declarator.method_match || !method_sym)) {
            error_custloc(
                "internal error: missing member function symbol for out-of-line declaration",
                qualified_declarator.loc);
        }
        if (storage_class == StorageClass::STATIC) {
            error_custloc(
                "out-of-line member function declaration must not use 'static'",
                qualified_declarator.loc);
        }
        bool is_static_method = matched_member_template
            ? qualified_declarator.method_template_match->is_static
            : qualified_declarator.method_match->is_static;
        if (is_static_method &&
            (decl_parser.trailing_function_cv_qualifiers != QUAL_NONE ||
             decl_parser.trailing_function_ref_qualifier != 0)) {
            error_custloc(
                "static member function cannot have cv/ref qualifier",
                qualified_declarator.loc);
        }
        validate_cpp_operator_function_declaration(
            decl_parser.name,
            true,
            is_static_method,
            declarator_token.loc);

        cxx_record_parse_stack_.push_back(CppRecordParseFrame{
            qualified_declarator.owner_record_decl->is_union
                ? CppRecordKind::Union
                : CppRecordKind::Class,
            qualified_declarator.owner_record_decl->tag});
        struct RecordParseScopeGuard {
            std::vector<CppRecordParseFrame>* stack = nullptr;
            ~RecordParseScopeGuard() {
                if (stack && !stack->empty()) {
                    stack->pop_back();
                }
            }
        } record_parse_scope_guard{&cxx_record_parse_stack_};

        merge_function_asm_label(decl_parser, method_sym, declarator_token.loc);
        auto parsed_method_decl =
            parse_function(&decl_parser, declarator_token.loc, method_sym);
        auto* parsed_method_func_raw = dyn_cast<FuncDecl>(parsed_method_decl.get());
        if (!parsed_method_func_raw) {
            error_custloc(
                "internal error: expected function declaration for out-of-line member function",
                qualified_declarator.loc);
        }
        auto parsed_method_func = std::unique_ptr<FuncDecl>(
            static_cast<FuncDecl*>(parsed_method_decl.release()));

        auto out_of_line_method = std::make_unique<CppMethodDecl>(
            parsed_method_func->name,
            parsed_method_func->type,
            std::move(parsed_method_func->parameters),
            std::move(parsed_method_func->body),
            std::move(parsed_method_func->stmt_labels),
            parsed_method_func->storage_class,
            parsed_method_func->is_inline != 0,
            parsed_method_func->location);
        out_of_line_method->node_id = parsed_method_func->node_id;
        out_of_line_method->scope = parsed_method_func->scope;
        out_of_line_method->type = parsed_method_func->type;
        out_of_line_method->is_constexpr = parsed_method_func->is_constexpr;
        out_of_line_method->is_consteval = parsed_method_func->is_consteval;
        if (out_of_line_method->is_consteval) {
            out_of_line_method->is_constexpr = true;
            out_of_line_method->is_inline = true;
        }
        out_of_line_method->is_deleted = parsed_method_func->is_deleted;
        out_of_line_method->is_defaulted = parsed_method_func->is_defaulted;
        out_of_line_method->is_defaulted_on_first_declaration = false;
        out_of_line_method->explicit_specialization_arguments =
            parsed_method_func->explicit_specialization_arguments;
        out_of_line_method->has_explicit_specialization_argument_list =
            parsed_method_func->has_explicit_specialization_argument_list;
        out_of_line_method->set_language_linkage(
            parsed_method_func->get_language_linkage());
        if (parsed_method_func->asm_label) {
            out_of_line_method->set_asm_label(*parsed_method_func->asm_label);
        }

        auto* matched_method_decl = matched_member_template
            ? const_cast<CppMethodDecl*>(
                  dyn_cast<CppMethodDecl>(
                      qualified_declarator.method_template_match->decl
                          ? qualified_declarator.method_template_match->decl
                                ->function_decl()
                          : nullptr))
            : const_cast<CppMethodDecl*>(qualified_declarator.method_match->decl);
        if (matched_member_template && !matched_method_decl) {
            error_custloc(
                "internal error: missing member template method declaration for out-of-line definition",
                qualified_declarator.loc);
        }
        out_of_line_method->is_virtual = matched_method_decl
            ? matched_method_decl->is_virtual
            : qualified_declarator.method_match->is_virtual;
        out_of_line_method->is_override = matched_method_decl
            ? matched_method_decl->is_override
            : qualified_declarator.method_match->is_override;
        out_of_line_method->is_final = matched_method_decl
            ? matched_method_decl->is_final
            : qualified_declarator.method_match->is_final;
        out_of_line_method->is_pure = matched_method_decl
            ? matched_method_decl->is_pure
            : qualified_declarator.method_match->is_pure;
        out_of_line_method->is_conversion_function = matched_method_decl
            ? matched_method_decl->is_conversion_function
            : qualified_declarator.method_match->is_conversion_function;
        out_of_line_method->is_explicit_conversion = matched_method_decl
            ? matched_method_decl->is_explicit_conversion
            : qualified_declarator.method_match->is_explicit;
        out_of_line_method->explicit_specifier = matched_method_decl
            ? matched_method_decl->explicit_specifier
            : CppExplicitSpecifier{};
        out_of_line_method->conversion_target_type = matched_method_decl
            ? matched_method_decl->conversion_target_type
            : qualified_declarator.method_match->conversion_target_type;

        if (matched_method_decl) {
            if (auto* existing_prefix =
                    get_func_decl_cxx_qualifier_prefix(matched_method_decl)) {
                set_func_decl_cxx_qualifier_prefix(
                    out_of_line_method.get(), *existing_prefix);
            }
        }

        QualType explicit_specialized_owner_type;
        if (preserve_explicit_specialization_member_decl &&
            qualified_declarator.owner_class_template &&
            qualified_declarator.owner_has_specialization_argument_list &&
            !qualified_declarator.targets_template_pattern) {
            auto owner_record_kind =
                qualified_declarator.owner_record_decl->is_union
                    ? CppRecordKind::Union
                    : CppRecordKind::Class;
            auto* specialized_owner_decl =
                ensure_cpp_specialized_record_semantic_owner(
                    owner_record_kind,
                    qualified_declarator.owner_class_template
                        ->record_decl()
                        ->name,
                    qualified_declarator.owner_template_arguments,
                    qualified_declarator.loc,
                    qualified_declarator.owner_class_template,
                    qualified_declarator.owner_has_specialization_argument_list);
            if (!specialized_owner_decl ||
                !specialized_owner_decl->get_record_type()) {
                error_custloc(
                    "internal error: failed to realize specialized owner for explicit specialization",
                    qualified_declarator.loc);
            }
            explicit_specialized_owner_type =
                QualType(specialized_owner_decl->get_record_type());
            std::string specialized_owner_prefix =
                qualified_name_utils::format_cpp_qualified_name(
                    qualified_declarator.has_global_qualifier,
                    qualified_declarator.qualifiers,
                    "");
            if (specialized_owner_prefix.size() >= 2 &&
                specialized_owner_prefix.ends_with("::")) {
                specialized_owner_prefix.erase(
                    specialized_owner_prefix.size() - 2);
            }
            if (!specialized_owner_prefix.empty()) {
                set_func_decl_cxx_qualifier_prefix(
                    out_of_line_method.get(),
                    specialized_owner_prefix);
            }
            set_func_decl_owner_record_type(
                out_of_line_method.get(),
                explicit_specialized_owner_type);
        }

        if (!is_static_method) {
            auto method_fn_type = desugar_type(
                matched_member_template
                    ? QualType(matched_method_decl->type)
                    : qualified_declarator.method_match->type)
                .as_shared<FunctionType>();
            if (!method_fn_type || method_fn_type->parameters.empty()) {
                error_custloc(
                    "internal error: out-of-line method is missing implicit object parameter",
                    qualified_declarator.loc);
            }
            QualType this_type = method_fn_type->parameters.front();
            if (explicit_specialized_owner_type) {
                if (auto this_ptr_type =
                        desugar_type(this_type).as_shared<PointerType>()) {
                    QualType specialized_pointee = explicit_specialized_owner_type;
                    if (this_ptr_type->pointed_type.is_const()) {
                        specialized_pointee = specialized_pointee.with_const();
                    }
                    if (this_ptr_type->pointed_type.is_volatile()) {
                        specialized_pointee =
                            specialized_pointee.with_volatile();
                    }
                    this_type = QualType(
                        std::make_shared<PointerType>(specialized_pointee));
                }
            }
            auto this_param = collect_->collect_parameter_declaration(
                this_type,
                "this",
                nullptr,
                StorageClass::NONE,
                qualified_declarator.loc);
            out_of_line_method->parameters.insert(
                out_of_line_method->parameters.begin(), std::move(this_param));
            if (auto fn_type =
                    dyn_cast_shared<FunctionType>(out_of_line_method->type)) {
                fn_type->insert_parameter(0, this_type);
                fn_type->has_prototype = true;
            }
        }

        if (out_of_line_method->is_defaulted &&
            !is_defaultable_method(
                out_of_line_method.get(),
                QualType(qualified_declarator.owner_record_decl->get_record_type()),
                ast_ctx.get())) {
            error_custloc(
                "only comparison operators and copy/move assignment operators may be defaulted here",
                    qualified_declarator.loc);
        }

        if (matched_method_decl &&
            matched_method_decl->is_consteval != out_of_line_method->is_consteval) {
            error_custloc(
                "conflicting consteval specifier for '" +
                    qualified_name_utils::format_cpp_qualified_name(
                        qualified_declarator.has_global_qualifier,
                        qualified_declarator.qualifiers,
                        decl_parser.name) +
                    "'",
                qualified_declarator.loc);
        }

        bool is_definition = function_decl_defines_entity(out_of_line_method.get());
        if (preserve_explicit_specialization_member_decl) {
            const Decl* primary_member_decl = nullptr;
            const FunctionTemplateDecl* primary_member_template = nullptr;
            std::vector<TemplateArgument> specialization_arguments;
            std::vector<TemplateArgument> owner_specialization_arguments;

            if (preserve_member_template_explicit_specialization) {
                primary_member_template =
                    qualified_declarator.method_template_match
                        ? qualified_declarator.method_template_match->decl
                        : nullptr;
                primary_member_decl =
                    primary_member_template
                        ? static_cast<const Decl*>(
                              primary_member_template->function_decl())
                        : nullptr;
                specialization_arguments =
                    qualified_declarator
                        .method_template_specialization_arguments;
                owner_specialization_arguments =
                    qualified_declarator.owner_template_arguments;
            } else {
                primary_member_decl =
                    qualified_declarator.method_match
                        ? static_cast<const Decl*>(
                              qualified_declarator.method_match->decl)
                        : nullptr;
                specialization_arguments =
                    qualified_declarator.owner_template_arguments;
            }

            if (!primary_member_decl) {
                error_custloc(
                    "internal error: missing primary member declaration for explicit specialization",
                    qualified_declarator.loc);
            }
            pending_cpp_explicit_specialization_info_ =
                PendingCppExplicitSpecializationInfo{
                    qualified_declarator.owner_class_template,
                    primary_member_template,
                    std::move(specialization_arguments),
                    std::move(owner_specialization_arguments),
                    primary_member_decl,
                };
            ast_ctx->append_attrs(
                out_of_line_method->node_id,
                std::move(decl_parser.leading_attrs));
            ast_ctx->append_attrs(
                out_of_line_method->node_id,
                std::move(trailing_attrs));
            ret_vec.push_back(std::move(out_of_line_method));
            return is_definition ? DeclaratorHandlingResult::Return
                                 : DeclaratorHandlingResult::Continue;
        }

        if (qualified_declarator.owner_class_template &&
            qualified_declarator.targets_template_pattern &&
            !matched_member_template) {
            remap_out_of_line_primary_template_method(
                out_of_line_method.get(),
                qualified_declarator.owner_class_template,
                qualified_declarator.loc);
        }

        if (is_definition) {
            if (!matched_method_decl) {
                error_custloc(
                    "internal error: missing member declaration for out-of-line definition",
                    qualified_declarator.loc);
            }
            if (matched_method_decl->body != nullptr ||
                matched_method_decl->has_deferred_inline_body() ||
                (method_sym && method_sym->is_defined)) {
                error_custloc(
                    "redefinition of '" +
                        qualified_name_utils::format_cpp_qualified_name(
                            qualified_declarator.has_global_qualifier,
                            qualified_declarator.qualifiers,
                            decl_parser.name) +
                        "'",
                    qualified_declarator.loc);
            }

            matched_method_decl->parameters =
                std::move(out_of_line_method->parameters);
            matched_method_decl->type = out_of_line_method->type;
            matched_method_decl->body = std::move(out_of_line_method->body);
            matched_method_decl->scope = out_of_line_method->scope;
            matched_method_decl->stmt_labels =
                std::move(out_of_line_method->stmt_labels);
            matched_method_decl->is_constexpr =
                out_of_line_method->is_constexpr;
            matched_method_decl->is_consteval =
                out_of_line_method->is_consteval;
            if (matched_method_decl->is_consteval) {
                matched_method_decl->is_constexpr = true;
                matched_method_decl->is_inline = true;
            }
            matched_method_decl->is_deleted =
                out_of_line_method->is_deleted;
            matched_method_decl->is_defaulted =
                out_of_line_method->is_defaulted;
            matched_method_decl->is_defaulted_on_first_declaration = false;
            matched_method_decl->is_conversion_function =
                out_of_line_method->is_conversion_function;
            matched_method_decl->is_explicit_conversion =
                out_of_line_method->is_explicit_conversion;
            matched_method_decl->explicit_specifier =
                out_of_line_method->explicit_specifier;
            matched_method_decl->conversion_target_type =
                out_of_line_method->conversion_target_type;
            matched_method_decl->set_language_linkage(
                out_of_line_method->get_language_linkage());
            if (out_of_line_method->asm_label) {
                matched_method_decl->set_asm_label(*out_of_line_method->asm_label);
            } else {
                matched_method_decl->clear_asm_label();
            }
            if (auto* parsed_prefix =
                    get_func_decl_cxx_qualifier_prefix(out_of_line_method.get())) {
                set_func_decl_cxx_qualifier_prefix(
                    matched_method_decl, *parsed_prefix);
            }

            if (matched_method_decl->is_defaulted) {
                if (const auto* owner_state =
                        collect_->query_lookup_record_semantics(
                            qualified_declarator.owner_record_decl)) {
                    collect_->collect_materialize_defaulted_copy_assignment_body(
                        matched_method_decl,
                        qualified_declarator.owner_record_decl,
                        *owner_state);
                }
            }

            if (method_sym) {
                method_sym->is_defined =
                    matched_method_decl->body != nullptr ||
                    matched_method_decl->is_deleted;
                method_sym->is_deleted = matched_method_decl->is_deleted;
                method_sym->is_defaulted = matched_method_decl->is_defaulted;
                method_sym->is_constexpr = matched_method_decl->is_constexpr;
                method_sym->is_consteval = matched_method_decl->is_consteval;
                method_sym->is_inline = matched_method_decl->is_inline;
                method_sym->type = QualType(matched_method_decl->type);
                method_sym->function_definition = matched_method_decl;
            }

            if (const auto* owner_state =
                    collect_->query_lookup_record_semantics(
                        qualified_declarator.owner_record_decl)) {
                RecordSemanticState updated_state = *owner_state;
                if (!matched_member_template) {
                    for (auto& method : updated_state.methods) {
                        if (method.decl != qualified_declarator.method_match->decl) {
                            continue;
                        }
                        method.decl = matched_method_decl;
                        method.type = QualType(matched_method_decl->type);
                        method.is_deleted = matched_method_decl->is_deleted;
                        method.is_defaulted = matched_method_decl->is_defaulted;
                        method.is_constexpr = matched_method_decl->is_constexpr;
                        method.is_consteval = matched_method_decl->is_consteval;
                        method.is_explicit =
                            matched_method_decl->is_explicit_conversion;
                        method.is_conversion_function =
                            matched_method_decl->is_conversion_function;
                        method.conversion_target_type =
                            matched_method_decl->conversion_target_type;
                        if (method_sym) {
                            method.symbol = method_sym;
                        }
                        break;
                    }
                }
                collect_->query_publish_record_semantics(
                    qualified_declarator.owner_record_decl,
                    std::move(updated_state));
            }

            ast_ctx->append_attrs(
                matched_method_decl->node_id,
                std::move(decl_parser.leading_attrs));
            ast_ctx->append_attrs(
                matched_method_decl->node_id,
                std::move(trailing_attrs));
            ret_vec.push_back(
                collect_->collect_nop_declaration(qualified_declarator.loc));
            return DeclaratorHandlingResult::Return;
        }

        ast_ctx->append_attrs(
            out_of_line_method->node_id,
            std::move(decl_parser.leading_attrs));
        ast_ctx->append_attrs(
            out_of_line_method->node_id,
            std::move(trailing_attrs));
        ret_vec.push_back(
            collect_->collect_nop_declaration(qualified_declarator.loc));
        return DeclaratorHandlingResult::Continue;
    }

    if (is_cxx_mode_active() &&
        (decl_parser.trailing_function_cv_qualifiers != QUAL_NONE ||
         decl_parser.trailing_function_ref_qualifier != 0)) {
        error("non-member function cannot have cv/ref qualifier");
    }
    if (declaration_is_constexpr && !is_cxx_mode_active()) {
        error("'constexpr' can only be applied to object declarations");
    }
    validate_cpp_operator_function_declaration(
        decl_parser.name,
        false,
        false,
        declarator_token.loc);
    bool preserve_function_explicit_specialization_decl =
        is_parsing_cpp_explicit_specialization();
    bool suppress_primary_function_template_symbol_binding =
        is_cxx_mode_active() &&
        template_pattern_depth_ > 0 &&
        !preserve_function_explicit_specialization_decl;
    std::shared_ptr<Symbol> predecl_sym = nullptr;
    if (!preserve_function_explicit_specialization_decl &&
        !suppress_primary_function_template_symbol_binding) {
        predecl_sym = collect_->collect_declare_function_symbol(
            decl_parser.name,
            QualType(parsed_decl_type),
            storage_class,
            declaration_is_constexpr,
            declaration_is_consteval,
            decl_parser.is_inline,
            false,
            declarator_token.loc,
            declaration_language_linkage,
            false,
            false,
            false);
        if (predecl_sym && declaration_is_consteval) {
            predecl_sym->is_consteval = true;
            predecl_sym->is_constexpr = true;
            predecl_sym->is_inline = true;
        }
        merge_function_asm_label(decl_parser, predecl_sym, declarator_token.loc);
    }
    auto funct = parse_function(&decl_parser, declarator_token.loc, predecl_sym);
    auto* func_decl_check = dyn_cast<FuncDecl>(funct.get());
    if (func_decl_check && func_decl_check->is_defaulted) {
        error_custloc(
            "only non-static member special member functions may be defaulted",
            declarator_token.loc);
    }
    bool is_definition =
        func_decl_check && function_decl_defines_entity(func_decl_check);
    std::shared_ptr<Symbol> final_sym = nullptr;
    if (!preserve_function_explicit_specialization_decl &&
        !suppress_primary_function_template_symbol_binding) {
        final_sym = collect_->collect_declare_function_symbol(
            decl_parser.name,
            QualType(parsed_decl_type),
            storage_class,
            declaration_is_constexpr,
            declaration_is_consteval,
            decl_parser.is_inline,
            is_definition,
            declarator_token.loc,
            declaration_language_linkage,
            false,
            func_decl_check && func_decl_check->is_deleted,
            func_decl_check && func_decl_check->is_defaulted);
        if (final_sym && declaration_is_consteval) {
            final_sym->is_consteval = true;
            final_sym->is_constexpr = true;
            final_sym->is_inline = true;
        }
        if (final_sym) {
            final_sym->is_hidden_friend = false;
        }
        if (is_definition && func_decl_check) {
            if (predecl_sym) {
                predecl_sym->is_hidden_friend = false;
                predecl_sym->function_definition = func_decl_check;
            }
            if (final_sym) {
                final_sym->function_definition = func_decl_check;
            }
        }
        if (func_decl_check && final_sym && final_sym != predecl_sym) {
            register_function_default_arguments(
                final_sym, func_decl_check, declarator_token.loc);
        }
        merge_function_asm_label(decl_parser, final_sym, declarator_token.loc);
    }
    auto append_function_attrs_to_symbol = [&](const std::shared_ptr<Symbol>& sym) {
        if (!sym) {
            return;
        }
        for (const auto& attr : decl_parser.leading_attrs) {
            sym->sym_attrs.attrs.push_back(attr);
        }
        for (const auto& attr : trailing_attrs) {
            sym->sym_attrs.attrs.push_back(attr);
        }
    };
    append_function_attrs_to_symbol(predecl_sym);
    if (final_sym != predecl_sym) {
        append_function_attrs_to_symbol(final_sym);
    }
    ast_ctx->append_attrs(funct->node_id, std::move(decl_parser.leading_attrs));
    ast_ctx->append_attrs(funct->node_id, std::move(trailing_attrs));
    ret_vec.push_back(std::move(funct));
    return is_definition ? DeclaratorHandlingResult::Return
                         : DeclaratorHandlingResult::Continue;
}

Parser::DeclaratorHandlingResult Parser::handle_variable_declarator(
    DeclarationParser& decl_parser,
    Token declarator_token,
    const std::shared_ptr<CType>& parsed_decl_type,
    std::vector<ParsedAttribute>& trailing_attrs,
    StorageClass storage_class,
    bool declaration_is_constexpr,
    bool declaration_is_consteval,
    LanguageLinkage declaration_language_linkage,
    QualifiedDeclaratorInfo& qualified_declarator,
    std::optional<QualType>& first_cxx_auto_deduced_type,
    std::vector<std::unique_ptr<Decl>>& ret_vec) {
    if (decl_parser.explicit_specifier.is_present) {
        error_custloc(
            "'explicit' is only allowed on constructors and conversion functions",
            decl_parser.explicit_specifier.location);
    }
    if (decl_parser.is_mutable) {
        error_custloc(
            "'mutable' can only be applied to non-static data members",
            decl_parser.begin_loc);
    }
    auto has_cxx_auto_type = [&](const std::shared_ptr<CType>& type) -> bool {
        return auto_type_utils::has_cxx_auto_type(type);
    };
    auto has_gnu_auto_type = [&](const std::shared_ptr<CType>& type) -> bool {
        return auto_type_utils::has_gnu_auto_type(type);
    };

    bool declarator_has_gnu_auto_type = has_gnu_auto_type(parsed_decl_type);
    bool declarator_has_cxx_auto_type = has_cxx_auto_type(parsed_decl_type);
    if (declarator_has_gnu_auto_type && declarator_has_cxx_auto_type) {
        error("cannot mix '__auto_type' and 'auto' in the same declaration");
    }
    if (declarator_has_gnu_auto_type && !gentle_check(TokenType::ASSIGN)) {
        error("'__auto_type' requires an initializer");
    }
    if (declaration_is_consteval) {
        error("'consteval' can only be applied to function declarations");
    }
    QualType declared_type(parsed_decl_type, decl_parser.qualifiers);
    if (declaration_is_constexpr && storage_class == StorageClass::EXTERN) {
        error("'constexpr' cannot be combined with 'extern'");
    }
    if (declaration_is_constexpr && storage_class == StorageClass::AUTO) {
        error("'constexpr' cannot be combined with 'auto'");
    }
    if (declaration_is_constexpr && decl_parser.is_thread_local) {
        error("'constexpr' cannot be combined with '_Thread_local'");
    }
    bool is_out_of_line_static_data_member =
        qualified_declarator.owner_record_decl != nullptr;
    std::shared_ptr<Symbol> declared_sym = nullptr;
    bool is_variable_template_specialization_declarator =
        is_cxx_mode_active() &&
        decl_parser.has_explicit_specialization_argument_list &&
        (is_parsing_cpp_explicit_specialization() ||
         is_in_template_pattern_context());
    bool preserve_explicit_specialization_static_decl =
        is_parsing_cpp_explicit_specialization() &&
        qualified_declarator.owner_class_template != nullptr &&
        qualified_declarator.owner_has_specialization_argument_list &&
        !qualified_declarator.targets_template_pattern;
    if (qualified_declarator.owner_record_decl) {
        if (storage_class == StorageClass::STATIC) {
            error_custloc(
                "out-of-line static data member definition must not use 'static'",
                qualified_declarator.loc);
        }
        if (!preserve_explicit_specialization_static_decl &&
            (!qualified_declarator.static_data_match ||
             !qualified_declarator.static_data_match->symbol)) {
            error_custloc(
                "internal error: missing static data member symbol for out-of-line definition",
                qualified_declarator.loc);
        }
        if (!preserve_explicit_specialization_static_decl) {
            declared_sym = qualified_declarator.static_data_match->symbol;
            declared_sym->type = desugar_type(declared_type);
            declared_sym->storage_class = StorageClass::STATIC;
            declared_sym->is_constexpr = declaration_is_constexpr;
            if (declared_sym->get_language_linkage() == LanguageLinkage::None) {
                declared_sym->set_language_linkage(
                    declaration_language_linkage);
            }
        }
    } else if (!is_variable_template_specialization_declarator) {
        declared_sym = collect_->collect_declare_variable_symbol(
            decl_parser.name,
            declared_type,
            storage_class,
            declaration_is_constexpr,
            decl_parser.is_inline,
            declarator_token.loc,
            declaration_language_linkage,
            true);
    }
    if (declared_sym) {
        declared_sym->is_constexpr = declaration_is_constexpr;
    }
    bool declared_sym_was_defined =
        declared_sym ? declared_sym->is_defined != 0 : false;
    const VariableDecl* declared_sym_prior_definition =
        declared_sym ? declared_sym->variable_definition : nullptr;
    if (declared_sym) {
        for (const auto& attr : decl_parser.leading_attrs) {
            declared_sym->sym_attrs.attrs.push_back(attr);
        }
        for (const auto& attr : trailing_attrs) {
            declared_sym->sym_attrs.attrs.push_back(attr);
        }
    }
    bool is_file_scope = collect_->collect_is_file_scope();
    QualType previous_record_lookup_type =
        collect_ ? collect_->collect_current_cpp_record_lookup_type()
                 : QualType();
    struct StaticDataMemberInitializerContextGuard {
        Collect* collect = nullptr;
        QualType previous_type = nullptr;
        ~StaticDataMemberInitializerContextGuard() {
            if (collect) {
                collect->collect_set_current_cpp_record_lookup_type(previous_type);
            }
        }
    } static_data_member_initializer_context_guard{
        collect_.get(),
        previous_record_lookup_type
    };
    if (collect_ &&
        qualified_declarator.owner_record_decl &&
        qualified_declarator.owner_record_decl->get_record_type()) {
        collect_->collect_set_current_cpp_record_lookup_type(
            QualType(qualified_declarator.owner_record_decl->get_record_type()));
    }
    if (is_cxx_mode_active() &&
        !qualified_declarator.owner_record_decl &&
        !is_variable_template_specialization_declarator &&
        !decl_parser.has_explicit_specialization_argument_list) {
        try_publish_pending_primary_variable_template_pattern(
            decl_parser.name,
            declared_type,
            declared_sym,
            storage_class,
            decl_parser.is_inline,
            declaration_is_constexpr,
            decl_parser.is_thread_local,
            decl_parser.is_block_byref,
            decl_parser.asm_label,
            declaration_language_linkage,
            declarator_token.loc);
    }
    std::unique_ptr<Expr> init_expr;
    bool is_copy_initialization = false;
    bool is_cxx_object_decl =
        is_cxx_mode_active() &&
        can_parse_cxx_object_initializer_syntax(declared_type);
    if (gentle_check_and_consume(TokenType::ASSIGN)) {
        is_copy_initialization = true;
        if (gentle_check(TokenType::LEFT_BRACE)) {
            init_expr = parse_init_list();
        } else {
            init_expr = parse_assignment_expression();
        }
    } else if (is_cxx_object_decl && gentle_check(TokenType::LEFT_PAREN)) {
        init_expr = parse_paren_init_list();
    } else if (is_cxx_object_decl && gentle_check(TokenType::LEFT_BRACE)) {
        init_expr = parse_init_list();
    }

    if (qualified_declarator.owner_record_decl &&
        qualified_declarator.targets_template_pattern &&
        qualified_declarator.owner_class_template) {
        remap_out_of_line_primary_template_static_member(
            declared_type,
            init_expr,
            qualified_declarator.owner_class_template,
            qualified_declarator.loc);
        if (declared_sym) {
            declared_sym->type = desugar_type(declared_type);
        }
    }

    auto var_decl_base = collect_->collect_variable_declaration(
        declared_type,
        decl_parser.name,
        std::move(init_expr),
        declared_sym,
        storage_class,
        {declaration_is_constexpr,
         decl_parser.is_inline,
         is_file_scope,
         is_out_of_line_static_data_member,
         is_out_of_line_static_data_member &&
             declaration_is_constexpr,
         decl_parser.is_thread_local,
         decl_parser.is_block_byref,
         is_copy_initialization,
         false,
         qualified_declarator.owner_record_decl != nullptr &&
             !preserve_explicit_specialization_static_decl},
        declarator_token.loc,
        declaration_language_linkage);
    auto* var_decl = cast<VariableDecl>(var_decl_base.get());
    var_decl->is_thread_local = decl_parser.is_thread_local;
    var_decl->is_block_byref = decl_parser.is_block_byref;
    var_decl->is_constexpr = declaration_is_constexpr;
    var_decl->explicit_specialization_arguments =
        decl_parser.explicit_specialization_arguments;
    var_decl->has_explicit_specialization_argument_list =
        decl_parser.has_explicit_specialization_argument_list;
    var_decl->set_asm_label(decl_parser.asm_label);
    if (decl_parser.asm_label.has_value() &&
        !is_file_scope &&
        storage_class != StorageClass::STATIC &&
        storage_class != StorageClass::REGISTER) {
        error("asm label on automatic local variable is not allowed");
    }
    ast_ctx->append_attrs(var_decl->node_id, std::move(decl_parser.leading_attrs));
    ast_ctx->append_attrs(var_decl->node_id, std::move(trailing_attrs));
    if (qualified_declarator.owner_record_decl &&
        declared_sym &&
        !preserve_explicit_specialization_static_decl) {
        declared_sym->is_defined = declared_sym_was_defined;
        declared_sym->variable_definition = declared_sym_prior_definition;
    }

    if (preserve_explicit_specialization_static_decl) {
        const Decl* primary_member_decl =
            qualified_declarator.static_data_match
                ? static_cast<const Decl*>(
                      qualified_declarator.static_data_match->decl)
                : nullptr;
        if (!primary_member_decl) {
            error_custloc(
                "internal error: missing primary static data member declaration for explicit specialization",
                qualified_declarator.loc);
        }
        pending_cpp_explicit_specialization_info_ =
            PendingCppExplicitSpecializationInfo{
                qualified_declarator.owner_class_template,
                nullptr,
                qualified_declarator.owner_template_arguments,
                {},
                primary_member_decl,
            };
        ret_vec.push_back(std::move(var_decl_base));
        return DeclaratorHandlingResult::Continue;
    }

    if (qualified_declarator.owner_record_decl &&
        declared_sym &&
        !qualified_declarator.targets_template_pattern) {
        bool is_definition =
            collect_->is_definition_bearing_variable_declaration(
                storage_class,
                {declaration_is_constexpr,
                 decl_parser.is_inline,
                 is_file_scope,
                 is_out_of_line_static_data_member,
                 false,
                 decl_parser.is_thread_local,
                 decl_parser.is_block_byref,
                 is_copy_initialization,
                 false},
                var_decl->init.get());
        if (is_definition) {
            if (declared_sym->is_defined) {
                error_custloc(
                    "redefinition of '" +
                        qualified_name_utils::format_cpp_qualified_name(
                            qualified_declarator.has_global_qualifier,
                            qualified_declarator.qualifiers,
                            decl_parser.name) +
                        "'",
                    qualified_declarator.loc);
            }
            declared_sym->is_defined = true;
            declared_sym->variable_definition = var_decl;
        }
    }

    if (qualified_declarator.owner_record_decl &&
        qualified_declarator.targets_template_pattern) {
        auto* matched_static_decl =
            qualified_declarator.static_data_match
                ? const_cast<VariableDecl*>(
                      qualified_declarator.static_data_match->decl)
                : nullptr;
        if (!matched_static_decl) {
            error_custloc(
                "internal error: missing primary template static data member declaration",
                qualified_declarator.loc);
        }

        bool is_definition =
            collect_->is_definition_bearing_variable_declaration(
                storage_class,
                {declaration_is_constexpr,
                 decl_parser.is_inline,
                 is_file_scope,
                 is_out_of_line_static_data_member,
                 false,
                 decl_parser.is_thread_local,
                 decl_parser.is_block_byref,
                 is_copy_initialization,
                 false},
                var_decl->init.get());
        if (is_definition &&
            (matched_static_decl->init != nullptr ||
             (declared_sym && declared_sym->is_defined))) {
            error_custloc(
                "redefinition of '" +
                    qualified_name_utils::format_cpp_qualified_name(
                        qualified_declarator.has_global_qualifier,
                        qualified_declarator.qualifiers,
                        decl_parser.name) +
                    "'",
                qualified_declarator.loc);
        }

        matched_static_decl->type = var_decl->type;
        matched_static_decl->sym = declared_sym;
        matched_static_decl->storage_class = StorageClass::STATIC;
        matched_static_decl->is_inline = var_decl->is_inline;
        matched_static_decl->is_constexpr = var_decl->is_constexpr;
        matched_static_decl->is_thread_local = var_decl->is_thread_local;
        matched_static_decl->set_language_linkage(
            var_decl->get_language_linkage());
        if (var_decl->asm_label) {
            matched_static_decl->set_asm_label(*var_decl->asm_label);
        } else {
            matched_static_decl->clear_asm_label();
        }
        if (is_definition) {
            matched_static_decl->init = std::move(var_decl->init);
        }

        if (declared_sym) {
            declared_sym->type = desugar_type(matched_static_decl->type);
            declared_sym->storage_class = StorageClass::STATIC;
            declared_sym->is_constexpr = matched_static_decl->is_constexpr;
            if (declared_sym->get_language_linkage() ==
                LanguageLinkage::None) {
                declared_sym->set_language_linkage(
                    matched_static_decl->get_language_linkage());
            }
            if (is_definition) {
                declared_sym->is_defined = true;
                declared_sym->variable_definition = matched_static_decl;
            }
        }

        if (const auto* owner_state =
                collect_->query_lookup_record_semantics(
                    qualified_declarator.owner_record_decl)) {
            RecordSemanticState updated_state = *owner_state;
            for (auto& static_member : updated_state.static_data_members) {
                if (static_member.decl !=
                    qualified_declarator.static_data_match->decl) {
                    continue;
                }
                static_member.decl = matched_static_decl;
                static_member.type = matched_static_decl->type;
                static_member.symbol = declared_sym;
                break;
            }
            collect_->query_publish_record_semantics(
                qualified_declarator.owner_record_decl,
                std::move(updated_state));
        }

        const auto& parsed_attrs = ast_ctx->get_attrs(var_decl->node_id).attrs;
        if (!parsed_attrs.empty()) {
            auto& dst_attrs =
                ast_ctx->get_attrs_mut(matched_static_decl->node_id).attrs;
            dst_attrs.insert(
                dst_attrs.end(), parsed_attrs.begin(), parsed_attrs.end());
        }

        ret_vec.push_back(
            collect_->collect_nop_declaration(qualified_declarator.loc));
        return DeclaratorHandlingResult::Continue;
    }

    ret_vec.push_back(std::move(var_decl_base));

    if (declarator_has_cxx_auto_type) {
        auto deduced = auto_type_utils::extract_auto_placeholder_replacement(
            declared_type, var_decl->type);
        if (deduced.has_value() &&
            deduced->get_shared() &&
            auto_type_utils::auto_type_flavors_in(deduced->get_shared()) == 0) {
            QualType deduced_canonical = desugar_type(*deduced);
            if (!first_cxx_auto_deduced_type.has_value()) {
                first_cxx_auto_deduced_type = deduced_canonical;
            } else {
                QualType first_canonical =
                    desugar_type(first_cxx_auto_deduced_type.value());
                if (!deduced_canonical.equals_qualified(first_canonical)) {
                    error(
                        "inconsistent deduction for 'auto': '" +
                        first_canonical.to_string() + "' and then '" +
                        deduced_canonical.to_string() + "'");
                }
            }
        }
    }

    if (declarator_has_gnu_auto_type && gentle_check(TokenType::COMMA)) {
        error("'__auto_type' cannot be used in a multi-declarator statement");
    }
    if (!gentle_check(TokenType::SEMICOLON) &&
        !gentle_check(TokenType::COMMA)) {
        error("expected ',' or ';' after declarator");
    }
    return DeclaratorHandlingResult::Continue;
}

std::vector<std::unique_ptr<Decl>> Parser::parse_declaration() {
    Token t = current_token();
    if (auto special_declaration = try_parse_special_declaration()) {
        return std::move(*special_declaration);
    }
    std::vector<std::unique_ptr<Decl>> ret_vec;
    auto decl_parser = DeclarationParser(this);
    auto new_type = parse_declaration_head(t, decl_parser, ret_vec);
    auto storage_class = decl_parser.str_class;
    const bool declaration_is_constexpr = decl_parser.is_constexpr;
    const bool declaration_is_consteval = decl_parser.is_consteval;
    const LanguageLinkage declaration_language_linkage = current_decl_language_linkage();
    std::optional<QualType> first_cxx_auto_deduced_type;
    // Error production: missing ';' after struct/union/enum definition
    // Detect: struct S { ... } <type-keyword> — likely forgot ';'
    if ((canonical_type_kind(new_type) == TypeKind::Object ||
         canonical_type_kind(new_type) == TypeKind::Enum)
        && !gentle_check(TokenType::SEMICOLON) && !gentle_check(TokenType::IDENTIFIER)
        && !gentle_check(TokenType::MULTIPLY) && !gentle_check(TokenType::LEFT_PAREN)
        && !gentle_check(TokenType::COMMA)
        && isTokenDeclarationSpec(current_token())) {
        diag_engine->report_note("possibly missing ';' after struct/union/enum definition", current_token().loc);
    }
    while (true) {
        if (gentle_check(TokenType::SEMICOLON)) {
            if (ret_vec.empty()) {
                if (storage_class == StorageClass::TYPEDEF) {
                    error("typedef requires a name for the type alias");
                }
                ret_vec.push_back(collect_->collect_nop_declaration(current_token().loc));
            }
            advance();
            break;
        } else if (gentle_check(TokenType::COMMA)) {
            advance();
        }
        t = current_token();
        auto qualified_declarator_context =
            prepare_qualified_declarator_context(decl_parser);
        auto& qualified_declarator = qualified_declarator_context.info;
        struct QualifiedDeclaratorScopeRestoreGuard {
            Collect* collect = nullptr;
            std::shared_ptr<Scope> scope;
            std::shared_ptr<DeclContext> decl_context;

            ~QualifiedDeclaratorScopeRestoreGuard() {
                if (!collect) {
                    return;
                }
                collect->collect_set_current_scope(scope);
                collect->set_current_decl_context(decl_context);
            }
        } scope_restore_guard {
            collect_.get(),
            qualified_declarator_context.scope_snapshot.scope,
            qualified_declarator_context.scope_snapshot.decl_context
        };
        std::shared_ptr<CType> newer_type = decl_parser.parse_declarator(new_type);
        retain_type_specifier_decl_if_needed(decl_parser);
        if (is_cxx_mode_active() && is_cpp_scope_resolution_here()) {
            error_custloc(
                "unsupported qualified declarator form after declarator-id",
                current_token().loc);
        }
        // Parse optional __asm__("name") label after declarator
        if (gentle_check(TokenType::ASM_KW)) {
            advance(); // consume asm/__asm__/__asm
            check_and_consume(TokenType::LEFT_PAREN);
            decl_parser.asm_label = parse_asm_string_literal();
            check_and_consume(TokenType::RIGHT_PAREN);
        }
        // Parse trailing attributes after declarator (e.g., int x __attribute__((aligned(16)));)
        auto trailing_attrs = try_parse_attributes();
        if (!decl_parser.asm_label.has_value()) {
            if (auto alias = extract_weakref_target(decl_parser.leading_attrs)) {
                decl_parser.asm_label = alias.value();
            } else if (auto alias = extract_weakref_target(trailing_attrs)) {
                decl_parser.asm_label = alias.value();
            }
        }
        if (newer_type == nullptr) {
            error("failed to parse declarator");
        }
        // GNU alias pattern:
        //   extern __typeof__(fn) alias __asm__("real_name");
        // When typeof(fn) is represented as pointer-to-function in expression
        // form, treat this declaration as a function declaration.
        if (newer_type && canonical_type_kind(newer_type) == TypeKind::Pointer &&
            decl_parser.asm_label.has_value() &&
            storage_class == StorageClass::EXTERN &&
            collect_->collect_is_file_scope()) {
            auto ptr = dyn_cast_shared<PointerType>(desugar_type(newer_type));
            auto pointed_fn = ptr ? ptr->pointed_type.as_shared<FunctionType>() : nullptr;
            if (pointed_fn) {
                newer_type = ptr->pointed_type.get_shared();
            }
        }
        if (newer_type && canonical_type_kind(newer_type) != TypeKind::Function &&
            decl_parser.asm_label.has_value() &&
            storage_class == StorageClass::EXTERN &&
            collect_->collect_is_file_scope() &&
            !decl_parser.name.empty()) {
            auto existing = collect_->collect_lookup_variable_symbol(decl_parser.name, true);
            if (existing && existing->kind == SymbolKind::FUNCTION && existing->type &&
                canonical_type_kind(existing->type) == TypeKind::Function) {
                newer_type = existing->type.get_shared();
            }
        }
        if (decl_parser.name.empty()) {
            if (is_in_tentative_context()) {
                throw ParseError("tentative declarator parse failed");
            }
            if (storage_class == StorageClass::TYPEDEF) {
                error("typedef requires a name for the type alias");
            }
            error("didn't catch the name of the declarator");
        }
        resolve_qualified_declarator_match(
            qualified_declarator,
            decl_parser,
            newer_type);
        if (is_cxx_mode_active()) {
            auto current_decl_context = collect_->get_current_decl_context();
            bool collides_with_namespace_name = false;
            if (current_decl_context && !decl_parser.name.empty()) {
                collides_with_namespace_name =
                    static_cast<bool>(current_decl_context->lookup_local_namespace_binding(
                        decl_parser.name));
            }
            if (collides_with_namespace_name) {
                if (storage_class == StorageClass::TYPEDEF) {
                    error("redefinition of '" + decl_parser.name + "' as typedef");
                }
                if (canonical_type_kind(newer_type) == TypeKind::Function) {
                    error("redefinition of '" + decl_parser.name + "' as function");
                }
                error("redefinition of '" + decl_parser.name + "' as variable");
            }
        }
        if (storage_class == StorageClass::TYPEDEF) {
            handle_typedef_declarator(
                decl_parser,
                t,
                newer_type,
                trailing_attrs,
                declaration_is_constexpr,
                declaration_is_consteval,
                ret_vec);
            continue;
        }
        if (canonical_type_kind(newer_type) == TypeKind::Function) {
            if (handle_function_declarator(
                    decl_parser,
                    t,
                    newer_type,
                    trailing_attrs,
                    storage_class,
                    declaration_is_constexpr,
                    declaration_is_consteval,
                    declaration_language_linkage,
                    qualified_declarator,
                    ret_vec) == DeclaratorHandlingResult::Return) {
                return ret_vec;
            }
            continue;
        }
        if (handle_variable_declarator(
                decl_parser,
                t,
                newer_type,
                trailing_attrs,
                storage_class,
                declaration_is_constexpr,
                declaration_is_consteval,
                declaration_language_linkage,
                qualified_declarator,
                first_cxx_auto_deduced_type,
                ret_vec) == DeclaratorHandlingResult::Return) {
            return ret_vec;
        }
    }
    return ret_vec;
}
std::unique_ptr<Decl> Parser::parse_parameter_declaration() {
    Token t = current_token();
    auto decl_parser = DeclarationParser(this);
    // Keep array types for parameters; decay happens in semantic analysis.
    decl_parser.arrays_are_pointers = false;
    decl_parser.in_function_parameter = true;
    auto new_type = decl_parser.parse_declaration();
    retain_type_specifier_decl_if_needed(decl_parser);
    auto ctype = new_type;
    std::string name = decl_parser.name;
    StorageClass sclass = decl_parser.str_class;
    if (decl_parser.is_consteval) {
        error("'consteval' is not valid for function parameter declarations");
    }
    if (decl_parser.is_constexpr) {
        error("'constexpr' is not valid for function parameter declarations");
    }
    if (decl_parser.is_friend) {
        error("'friend' is not valid for function parameter declarations");
    }
    if (decl_parser.explicit_specifier.is_present) {
        error("'explicit' is not valid for function parameter declarations");
    }
    if (decl_parser.is_mutable) {
        error("'mutable' is not valid for function parameter declarations");
    }
    std::shared_ptr<Symbol> sym = nullptr;
    if (!name.empty()) {
        sym = collect_->collect_declare_variable_symbol(
            name, ctype, sclass, false, false, t.loc);
    }
    auto param_decl = collect_->collect_parameter_declaration(ctype, name, sym, sclass, t.loc);
    if (auto* parsed_param = dyn_cast<ParamDecl>(param_decl.get())) {
        parsed_param->is_constexpr = decl_parser.is_constexpr;
        parsed_param->is_parameter_pack = decl_parser.is_parameter_pack;
    }
    return param_decl;

}

// Parse struct declaration (field inside struct body)
// Handles both regular fields and bitfields:
//   type-specifier declarator ;
//   type-specifier declarator : constant-expression ;
//   type-specifier : constant-expression ;  (anonymous bitfield)
std::vector<std::unique_ptr<Decl>> Parser::parse_struct_declaration(bool leading_virtual_specifier) {
    Token t = current_token();
    std::vector<std::unique_ptr<Decl>> fields;

    // C11/C23: _Static_assert is allowed inside struct/union declarations.
    if (gentle_check(TokenType::STATIC_ASSERT)) {
        fields.push_back(parse_static_assert_declaration());
        return fields;
    }

    DeclarationParser decl_parser(this);
    decl_parser.allow_typeless_conversion_function =
        is_cxx_mode_active() &&
        is_parsing_cpp_record_body() &&
        !cxx_record_parse_stack_.empty() &&
        cxx_record_parse_stack_.back().kind != CppRecordKind::Union;
    std::shared_ptr<CType> base_type = nullptr;
    base_type = decl_parser.parse_declaration(false);
    bool declaration_leading_virtual = leading_virtual_specifier;
    auto ensure_namespace_qualifier_prefix = [&](std::string& qualifier_prefix) {
        if (!is_cxx_mode_active()) {
            return;
        }
        qualified_name_utils::ensure_namespace_qualifier_prefix_for_scope(
            collect_->collect_current_scope(), qualifier_prefix);
    };

    auto build_member_param_decls =
        [&](std::vector<std::unique_ptr<DeclarationParser>>& parsed_params,
            const std::shared_ptr<CType>& function_type)
        -> std::vector<std::unique_ptr<Decl>> {
        std::vector<std::unique_ptr<Decl>> member_params;
        bool seen_void_param = false;
        for (auto& param_parser : parsed_params) {
            if (!param_parser) {
                continue;
            }
            retain_type_specifier_decl_if_needed(*param_parser);
            if (param_parser->is_constexpr || param_parser->is_consteval) {
                error("'constexpr/consteval' is not valid for function parameter declarations");
            }
            if (param_parser->explicit_specifier.is_present) {
                error("'explicit' is not valid for function parameter declarations");
            }
            if (param_parser->is_mutable) {
                error("'mutable' is not valid for function parameter declarations");
            }
            if (param_parser->result_type &&
                param_parser->result_type->isVoid()) {
                seen_void_param = true;
                if (!param_parser->name.empty()) {
                    error("Argument cannot have 'void' type");
                }
            }
            QualType param_type(
                param_parser->result_type, param_parser->qualifiers);
            auto param_decl = collect_->collect_parameter_declaration(
                param_type,
                param_parser->name,
                nullptr,
                param_parser->str_class,
                param_parser->begin_loc);
            if (auto* typed_param = dyn_cast<ParamDecl>(param_decl.get())) {
                typed_param->is_constexpr = param_parser->is_constexpr;
                typed_param->is_parameter_pack = param_parser->is_parameter_pack;
                set_param_decl_default_argument(
                    typed_param,
                    std::move(param_parser->default_argument));
            }
            member_params.push_back(std::move(param_decl));
        }
        if (auto* func_ty = dyn_cast<FunctionType>(function_type.get())) {
            func_ty->parameter_pack_flags.clear();
            func_ty->parameter_pack_flags.reserve(member_params.size());
            for (const auto& member_param : member_params) {
                const auto* typed_param =
                    dyn_cast<ParamDecl>(member_param.get());
                func_ty->parameter_pack_flags.push_back(
                    typed_param && typed_param->is_parameter_pack ? 1 : 0);
            }
            func_ty->normalize_parameter_pack_flags();
        }
        if (seen_void_param) {
            auto* func_ty = dyn_cast<FunctionType>(function_type.get());
            if (func_ty && func_ty->is_variadic) {
                error("'void' parameter cannot be combined with '...'");
            }
            if (member_params.size() != 1) {
                error("mixed up 'void' with other function arguments in declaration");
            }
        }
        return member_params;
    };

    // If a struct/union was defined as the type specifier, include it so sema
    // can process nested enum/struct declarations in the enclosing scope.
    if (decl_parser.struct_obj) {
        fields.push_back(std::move(decl_parser.struct_obj));
    }

    // If an enum was defined as the type specifier, include it so sema
    // can register the enum constants in the enclosing scope.
    if (decl_parser.enum_obj) {
        fields.push_back(std::move(decl_parser.enum_obj));
    }

    if (!fields.empty() &&
        gentle_check(TokenType::SEMICOLON) &&
        dyn_cast<EnumDecl>(fields.back().get()) != nullptr) {
        check_and_consume(TokenType::SEMICOLON);
        return fields;
    }

    while (true) {
        decl_parser.reset_declarator_parsing_state();
        auto field_type = decl_parser.parse_declarator(base_type);
        std::string field_name = decl_parser.name;
        CppExplicitSpecifier member_explicit_specifier =
            decl_parser.explicit_specifier;
        bool member_explicit = member_explicit_specifier.effective_value;
        auto declared_field_type = [&]() {
            return QualType(field_type, decl_parser.qualifiers);
        };
        auto validate_mutable_data_member = [&]() {
            if (!decl_parser.is_mutable) {
                return;
            }
            QualType field_qual_type = declared_field_type();
            if (field_qual_type.is_const()) {
                error_custloc(
                    "'mutable' and 'const' cannot be mixed",
                    decl_parser.begin_loc);
            }
            auto canonical_field_type =
                desugar_type(field_qual_type, ast_ctx.get());
            if (canonical_field_type.as_shared<ReferenceType>()) {
                error_custloc(
                    "'mutable' cannot be applied to references",
                    decl_parser.begin_loc);
            }
        };

        // Parse attributes that appear right after the declarator.
        auto field_attrs_before_colon = try_parse_attributes();

        // In C++ record bodies, function declarators are methods/constructors, not fields.
        if (is_cxx_mode_active() &&
            is_parsing_cpp_record_body() &&
            cxx_record_parse_stack_.back().kind != CppRecordKind::Union &&
            field_type &&
            canonical_type_kind(field_type) == TypeKind::Function) {
            if (decl_parser.is_mutable) {
                error_custloc(
                    "'mutable' cannot be applied to functions",
                    decl_parser.begin_loc);
            }
            std::string record_name =
                !cxx_record_parse_stack_.empty()
                    ? cxx_record_parse_stack_.back().name
                    : std::string();
            bool is_constructor_member = false;
            auto base_record_type = dyn_cast_shared<ObjectType>(desugar_type(base_type));
            bool looks_like_ctor_name =
                field_name.empty() || field_name == record_name;
            if (!record_name.empty() && looks_like_ctor_name && base_record_type) {
                const TagDecl* base_decl = base_record_type->get_decl();
                if (base_decl && base_decl->get_tag_name() == record_name) {
                    is_constructor_member = true;
                }
            }

            if (gentle_check(TokenType::COLON) && !is_constructor_member) {
                error("member function declaration cannot be a bitfield");
                return {};
            }

            auto capture_deferred_inline_body_tokens =
                [&](auto* callable_decl, const char* missing_closing_brace_diag) {
                if (!callable_decl) {
                    return;
                }
                size_t body_begin_token_idx = get_token_idx();
                if (gentle_check(TokenType::TRY_KW)) {
                    skip_cpp_function_try_block_tokens(false);
                } else {
                    skip_balanced_token_sequence_tokens(
                        TokenType::LEFT_BRACE,
                        TokenType::RIGHT_BRACE,
                        missing_closing_brace_diag);
                }
                size_t body_end_token_idx = get_token_idx();
                callable_decl->set_deferred_inline_body_token_range(
                    body_begin_token_idx, body_end_token_idx);
            };

            if (decl_parser.is_friend) {
                if (declaration_leading_virtual) {
                    error("'virtual' is not allowed on friend declarations");
                }
                if (member_explicit_specifier.is_present) {
                    error("'explicit' is not allowed on friend declarations");
                }
                if (decl_parser.trailing_function_cv_qualifiers != QUAL_NONE ||
                    decl_parser.trailing_function_ref_qualifier != 0) {
                    error("non-member function cannot have cv/ref qualifier");
                }
                validate_cpp_operator_function_declaration(
                    decl_parser.name,
                    false,
                    false,
                    t.loc);

                auto friend_function = collect_->collect_function_declaration(
                    decl_parser.name,
                    field_type,
                    StorageClass::NONE,
                    decl_parser.is_inline,
                    decl_parser.asm_label,
                    t.loc,
                    current_decl_language_linkage());
                friend_function->parameters =
                    build_member_param_decls(decl_parser.func_args,
                                             friend_function->type);
                friend_function->is_constexpr = decl_parser.is_constexpr;
                friend_function->is_consteval = decl_parser.is_consteval;
                if (friend_function->is_consteval) {
                    friend_function->is_constexpr = true;
                    friend_function->is_inline = true;
                }
                friend_function->trailing_requires_clause =
                    std::move(decl_parser.trailing_requires_clause);
                friend_function->explicit_specialization_arguments =
                    decl_parser.explicit_specialization_arguments;
                friend_function->has_explicit_specialization_argument_list =
                    decl_parser.has_explicit_specialization_argument_list;

                if (gentle_check(TokenType::ASSIGN)) {
                    SrcLoc suffix_loc = current_token().loc;
                    advance();
                    if (gentle_check(TokenType::DELETE)) {
                        friend_function->is_deleted = true;
                        advance();
                    } else if (gentle_check(TokenType::DEFAULT)) {
                        friend_function->is_defaulted = true;
                        advance();
                    } else {
                        fail_cpp_unsupported("function declaration suffix",
                                             suffix_loc);
                    }
                }

                QualType granting_record_type = nullptr;
                if (!cxx_record_parse_stack_.empty()) {
                    const auto& record_frame = cxx_record_parse_stack_.back();
                    if (record_frame.semantic_owner &&
                        record_frame.semantic_owner->get_record_type()) {
                        granting_record_type =
                            QualType(record_frame.semantic_owner->get_record_type());
                    }
                    if (!granting_record_type && !record_frame.name.empty()) {
                        auto owner_type = dyn_cast_shared<ObjectType>(
                            collect_->collect_lookup_tag_type(
                                record_frame.name,
                                true));
                        if (owner_type) {
                            granting_record_type = QualType(owner_type);
                        }
                    }
                }

                auto friend_decl = make_ast<FriendDecl>(
                    *ast_ctx,
                    std::move(friend_function),
                    granting_record_type,
                    CppFriendKind::Function,
                    t.loc);
                auto* friend_function_ptr = friend_decl->function_decl();
                if (friend_function_ptr &&
                    friend_function_ptr->is_defaulted &&
                    !is_defaultable_comparison_function(
                        friend_function_ptr,
                        granting_record_type,
                        ast_ctx.get())) {
                    error_custloc(
                        "only comparison friend functions may be defaulted here",
                        friend_function_ptr->location);
                }

                bool friend_has_inline_body = false;
                if (gentle_check(TokenType::LEFT_BRACE) ||
                    gentle_check(TokenType::TRY_KW)) {
                    friend_has_inline_body = true;
                    if (friend_function_ptr) {
                        friend_function_ptr->is_inline = true;
                    }
                    capture_deferred_inline_body_tokens(
                        friend_decl.get(),
                        "expected '}' to close friend function body");
                }

                if (friend_function_ptr) {
                    auto nearest_namespace_scope = [&]() {
                        auto scope = collect_->collect_current_scope();
                        while (scope &&
                               !scope_flags_contains(
                                   scope->flags,
                                   ScopeFlags::FileScope) &&
                               !scope_flags_contains(
                                   scope->flags,
                                   ScopeFlags::NamespaceScope)) {
                            scope = scope->parent;
                        }
                        return scope ? scope : collect_->collect_current_scope();
                    };
                    auto friend_scope = nearest_namespace_scope();
                    bool has_visible_matching_namespace_decl = false;
                    for (const auto& candidate :
                         LookupEngine::lookup_unqualified_function_candidates(
                             friend_function_ptr->name,
                             friend_scope,
                             false)) {
                        if (candidate &&
                            candidate->type.equals_unqualified(
                                QualType(friend_function_ptr->type))) {
                            has_visible_matching_namespace_decl = true;
                            break;
                        }
                    }
                    bool is_definition =
                        friend_function_ptr->is_deleted ||
                        friend_function_ptr->is_defaulted ||
                        friend_decl->has_deferred_inline_body();
                    auto friend_sym = collect_->collect_declare_function_symbol(
                        friend_scope,
                        ast_ctx ? ast_ctx->global_tracker : nullptr,
                        friend_function_ptr->name,
                        QualType(friend_function_ptr->type),
                        StorageClass::NONE,
                        friend_function_ptr->is_constexpr,
                        friend_function_ptr->is_consteval,
                        friend_function_ptr->is_inline,
                        is_definition,
                        friend_function_ptr->location,
                        friend_function_ptr->get_language_linkage(),
                        false,
                        friend_function_ptr->is_deleted,
                        friend_function_ptr->is_defaulted);
                    if (friend_sym) {
                        if (is_definition) {
                            friend_sym->function_definition =
                                friend_function_ptr;
                        }
                        friend_sym->is_hidden_friend =
                            !has_visible_matching_namespace_decl;
                        register_function_default_arguments(
                            friend_sym,
                            friend_function_ptr,
                            friend_function_ptr->location);
                        merge_function_asm_label(
                            decl_parser,
                            friend_sym,
                            friend_function_ptr->location);
                    }
                    friend_decl->function_symbol = std::move(friend_sym);
                    ast_ctx->append_attrs(friend_function_ptr->node_id,
                                          std::move(decl_parser.leading_attrs));
                    ast_ctx->append_attrs(friend_function_ptr->node_id,
                                          std::move(field_attrs_before_colon));
                }
                fields.push_back(std::move(friend_decl));

                if (friend_has_inline_body) {
                    return fields;
                }

                if (gentle_check(TokenType::COMMA)) {
                    advance();
                    continue;
                }
                check_and_consume(TokenType::SEMICOLON);
                break;
            }

            if (member_explicit &&
                !is_constructor_member &&
                !decl_parser.is_conversion_function) {
                error("'explicit' is only allowed on constructors and conversion functions");
            }
            if (decl_parser.is_conversion_function) {
                auto method_fn_type = dyn_cast_shared<FunctionType>(field_type);
                if (method_fn_type && !method_fn_type->parameters.empty()) {
                    error("conversion function cannot have parameters");
                }
            }

            if (is_constructor_member) {
                if (decl_parser.trailing_function_cv_qualifiers != QUAL_NONE ||
                    decl_parser.trailing_function_ref_qualifier != 0) {
                    error("constructor cannot have cv/ref qualifier");
                }
                if (declaration_leading_virtual) {
                    error("constructor cannot be declared 'virtual'");
                }
                if (decl_parser.str_class == StorageClass::STATIC) {
                    error("constructor cannot be declared 'static'");
                }
                std::vector<CppCtorInitializer> parsed_ctor_initializers;
                if (gentle_check(TokenType::COLON)) {
                    advance(); // ':'
                    std::unordered_set<std::string> seen_mem_inits;
                    bool saw_delegating_initializer = false;
                    bool saw_non_delegating_initializer = false;
                    while (true) {
                        if (!gentle_check(TokenType::IDENTIFIER)) {
                            error("expected member name in constructor mem-initializer-list");
                        }
                        Token member_tok = current_token();
                        std::string member_name = member_tok.value;
                        advance();

                        bool is_delegating_initializer = member_name == record_name;
                        if (is_delegating_initializer) {
                            if (saw_non_delegating_initializer) {
                                error_custloc(
                                    "delegating constructor initializer must appear alone",
                                    member_tok.loc);
                            }
                            saw_delegating_initializer = true;
                        } else {
                            if (saw_delegating_initializer) {
                                error_custloc(
                                    "delegating constructor initializer must appear alone",
                                    member_tok.loc);
                            }
                            saw_non_delegating_initializer = true;
                        }

                        if (!seen_mem_inits.insert(member_name).second) {
                            error_custloc(
                                "constructor mem-initializer-list has duplicate member '" +
                                    member_name + "'",
                                member_tok.loc);
                        }

                        CppCtorInitializer mem_init;
                        mem_init.member_name = member_name;
                        mem_init.is_delegating_initializer = is_delegating_initializer;
                        mem_init.location = member_tok.loc;

                        if (gentle_check(TokenType::LEFT_PAREN)) {
                            mem_init.is_list_init = false;
                            mem_init.deferred_init_begin_token_idx = get_token_idx();
                            skip_balanced_token_sequence_tokens(
                                TokenType::LEFT_PAREN,
                                TokenType::RIGHT_PAREN,
                                "expected ')' to close constructor member initializer");
                            mem_init.deferred_init_end_token_idx = get_token_idx();
                        } else if (gentle_check(TokenType::LEFT_BRACE)) {
                            mem_init.is_list_init = true;
                            mem_init.deferred_init_begin_token_idx = get_token_idx();
                            skip_balanced_token_sequence_tokens(
                                TokenType::LEFT_BRACE,
                                TokenType::RIGHT_BRACE,
                                "expected '}' to close constructor member initializer");
                            mem_init.deferred_init_end_token_idx = get_token_idx();
                        } else {
                            error("expected '(' or '{' after constructor mem-initializer '" +
                                  member_name + "'");
                        }

                        parsed_ctor_initializers.push_back(std::move(mem_init));
                        if (!gentle_check_and_consume(TokenType::COMMA)) {
                            break;
                        }
                    }
                }
                bool ctor_is_deleted = false;
                bool ctor_is_defaulted = false;
                if (gentle_check(TokenType::ASSIGN)) {
                    SrcLoc suffix_loc = current_token().loc;
                    advance(); // '='
                    if (gentle_check(TokenType::DEFAULT)) {
                        ctor_is_defaulted = true;
                        advance(); // 'default'
                    } else if (gentle_check(TokenType::DELETE)) {
                        ctor_is_deleted = true;
                        advance(); // 'delete'
                    } else {
                        fail_cpp_unsupported("constructor declaration suffix",
                                             suffix_loc);
                    }
                }

                auto ctor_fn_type = dyn_cast_shared<FunctionType>(field_type);
                if (!ctor_fn_type) {
                    error("internal error: constructor declarator is not a function type");
                    return {};
                }
                ctor_fn_type->ret_type = QualType(type_ctx->get_builtin(BuiltinTypes::Void));

                bool has_inline_body = gentle_check(TokenType::LEFT_BRACE) ||
                    gentle_check(TokenType::TRY_KW);
                auto ctor_params = build_member_param_decls(decl_parser.func_args, field_type);
                auto ctor_decl = make_ast<CppConstructorDecl>(
                    *ast_ctx,
                    record_name,
                    field_type,
                    std::move(ctor_params),
                    nullptr,
                    std::unordered_set<std::string>{},
                    decl_parser.str_class,
                    decl_parser.is_inline,
                    member_explicit,
                    t.loc);
                ctor_decl->type = field_type;
                ctor_decl->explicit_specifier =
                    std::move(member_explicit_specifier);
                ctor_decl->is_constexpr = decl_parser.is_constexpr;
                ctor_decl->is_deleted = ctor_is_deleted;
                ctor_decl->is_defaulted = ctor_is_defaulted;
                ctor_decl->is_defaulted_on_first_declaration =
                    ctor_is_defaulted;
                ctor_decl->set_language_linkage(current_decl_language_linkage());
                ctor_decl->ctor_initializers = std::move(parsed_ctor_initializers);
                if (ctor_is_defaulted) {
                    ctor_decl->body = make_ast<CompoundStmt>(
                        *ast_ctx,
                        std::vector<std::unique_ptr<Stmt>>{},
                        t.loc);
                }
                if ((ctor_is_defaulted || ctor_is_deleted) &&
                    !ctor_decl->ctor_initializers.empty()) {
                    error("defaulted/deleted constructor cannot have a member initializer list");
                }
                if (!ctor_is_defaulted && !ctor_is_deleted &&
                    !has_inline_body && !ctor_decl->ctor_initializers.empty()) {
                    error("constructor with mem-initializer-list requires a function body");
                }

                std::string ctor_qualifier_prefix;
                if (auto* existing_prefix =
                        get_func_decl_cxx_qualifier_prefix(ctor_decl.get())) {
                    ctor_qualifier_prefix = *existing_prefix;
                }
                if (has_inline_body) {
                    capture_deferred_inline_body_tokens(
                        ctor_decl.get(),
                        "expected '}' to close constructor body");
                }

                std::string record_qualifier_prefix = current_cpp_record_qualifier_prefix();
                ensure_namespace_qualifier_prefix(ctor_qualifier_prefix);
                if (!record_qualifier_prefix.empty()) {
                    if (!ctor_qualifier_prefix.empty()) {
                        ctor_qualifier_prefix += "::";
                    }
                    ctor_qualifier_prefix += record_qualifier_prefix;
                }
                if (!ctor_qualifier_prefix.empty()) {
                    set_func_decl_cxx_qualifier_prefix(
                        ctor_decl.get(), ctor_qualifier_prefix);
                }

                if (!record_name.empty()) {
                    const auto& record_frame = cxx_record_parse_stack_.back();
                    auto owner_type =
                        record_frame.semantic_owner
                            ? record_frame.semantic_owner->get_record_type()
                            : nullptr;
                    if (!owner_type) {
                        auto owner_type_raw =
                            collect_->collect_lookup_tag_type(record_name, true);
                        owner_type = dyn_cast_shared<ObjectType>(owner_type_raw);
                    }
                    if (owner_type) {
                        QualType this_type(
                            std::make_shared<PointerType>(QualType(owner_type)));
                        auto this_param = collect_->collect_parameter_declaration(
                            this_type, "this", nullptr, StorageClass::NONE, t.loc);
                        ctor_decl->parameters.insert(
                            ctor_decl->parameters.begin(), std::move(this_param));
                        if (auto fn_type = dyn_cast_shared<FunctionType>(ctor_decl->type)) {
                            fn_type->insert_parameter(0, this_type);
                            fn_type->has_prototype = true;
                        }
                    }
                }

                ast_ctx->append_attrs(ctor_decl->node_id,
                                      std::move(decl_parser.leading_attrs));
                ast_ctx->append_attrs(ctor_decl->node_id,
                                      std::move(field_attrs_before_colon));
                fields.push_back(std::move(ctor_decl));

                if (auto* ctor = dyn_cast<CppConstructorDecl>(fields.back().get());
                    ctor &&
                    !ctor->is_defaulted &&
                    !ctor->is_deleted &&
                    (ctor->body != nullptr || ctor->has_deferred_inline_body())) {
                    // In-class constructor definitions do not require a trailing semicolon.
                    return fields;
                }

                if (ctor_is_deleted || ctor_is_defaulted) {
                    check_and_consume(TokenType::SEMICOLON);
                    break;
                }

                if (gentle_check(TokenType::COMMA)) {
                    advance();
                    continue;
                }
                if (lang_opts.implicit_int && gentle_check(TokenType::RIGHT_BRACE)) {
                    diag_engine->report_warning(
                        "missing ';' after class member declaration; assuming ';'",
                        current_token().loc);
                    break;
                }
                check_and_consume(TokenType::SEMICOLON);
                break;
            }

            validate_cpp_operator_function_declaration(
                decl_parser.name,
                true,
                decl_parser.str_class == StorageClass::STATIC,
                t.loc);

            bool method_is_virtual = declaration_leading_virtual;
            bool method_is_override = false;
            bool method_is_final = false;
            bool method_is_pure = false;

            while (gentle_check(TokenType::IDENTIFIER)) {
                const std::string& spelling = current_token().value;
                if (spelling == "override") {
                    if (method_is_override) {
                        error("duplicate 'override' specifier");
                    }
                    method_is_override = true;
                    advance();
                    continue;
                }
                if (spelling == "final") {
                    if (method_is_final) {
                        error("duplicate 'final' specifier");
                    }
                    method_is_final = true;
                    advance();
                    continue;
                }
                break;
            }

            if ((method_is_virtual || method_is_override || method_is_final) &&
                decl_parser.str_class == StorageClass::STATIC) {
                error("static member function cannot be declared virtual/override/final");
            }
            if (decl_parser.str_class == StorageClass::STATIC &&
                (decl_parser.trailing_function_cv_qualifiers != QUAL_NONE ||
                 decl_parser.trailing_function_ref_qualifier != 0)) {
                error("static member function cannot have cv/ref qualifier");
            }

            if (gentle_check(TokenType::ASSIGN) &&
                peek_token().type == TokenType::INTEGER_CONST &&
                peek_token().value == "0") {
                SrcLoc pure_loc = current_token().loc;
                advance(); // '='
                if (!gentle_check(TokenType::INTEGER_CONST) ||
                    current_token().value != "0") {
                    error_custloc(
                        "pure-specifier must be '= 0' in member declaration",
                        pure_loc);
                }
                method_is_pure = true;
                advance(); // '0'
            }

            if (method_is_pure && decl_parser.str_class == StorageClass::STATIC) {
                error("static member function cannot be pure");
            }

            bool has_inline_body = gentle_check(TokenType::LEFT_BRACE) ||
                gentle_check(TokenType::TRY_KW);
            if (method_is_pure && has_inline_body) {
                error("pure virtual function cannot have a function body");
            }
            std::unique_ptr<CppMethodDecl> cpp_method;
            std::string method_qualifier_prefix;

            if (has_inline_body) {
                auto method_params =
                    build_member_param_decls(decl_parser.func_args, field_type);

                cpp_method = make_ast<CppMethodDecl>(
                    *ast_ctx,
                    decl_parser.name,
                    field_type,
                    std::move(method_params),
                    nullptr,
                    std::unordered_set<std::string>{},
                    decl_parser.str_class,
                    decl_parser.is_inline,
                    t.loc);
                cpp_method->type = field_type;
                cpp_method->is_constexpr = decl_parser.is_constexpr;
                cpp_method->is_consteval = decl_parser.is_consteval;
                cpp_method->is_deleted = false;
                cpp_method->is_defaulted = false;
                cpp_method->is_defaulted_on_first_declaration = false;
                cpp_method->is_conversion_function =
                    decl_parser.is_conversion_function;
                cpp_method->is_explicit_conversion = member_explicit;
                cpp_method->explicit_specifier = member_explicit_specifier;
                cpp_method->conversion_target_type =
                    decl_parser.conversion_target_type;
                cpp_method->is_virtual = method_is_virtual;
                cpp_method->is_override = method_is_override;
                cpp_method->is_final = method_is_final;
                cpp_method->is_pure = method_is_pure;
                cpp_method->set_language_linkage(current_decl_language_linkage());

                if (auto* existing_prefix =
                        get_func_decl_cxx_qualifier_prefix(cpp_method.get())) {
                    method_qualifier_prefix = *existing_prefix;
                }

                capture_deferred_inline_body_tokens(
                    cpp_method.get(),
                    "expected '}' to close class member function body");
            } else {
                auto parsed_method_decl = parse_function(&decl_parser, t.loc);
                auto parsed_method =
                    std::unique_ptr<FuncDecl>(dyn_cast<FuncDecl>(parsed_method_decl.release()));
                if (!parsed_method) {
                    error("internal error: expected function declaration for class member method");
                    return {};
                }

                cpp_method = std::make_unique<CppMethodDecl>(
                    parsed_method->name,
                    parsed_method->type,
                    std::move(parsed_method->parameters),
                    std::move(parsed_method->body),
                    std::move(parsed_method->stmt_labels),
                    parsed_method->storage_class,
                    parsed_method->is_inline != 0,
                    parsed_method->location);
                cpp_method->node_id = parsed_method->node_id;
                cpp_method->scope = parsed_method->scope;
                cpp_method->type = parsed_method->type;
                cpp_method->is_constexpr = parsed_method->is_constexpr;
                cpp_method->is_consteval = parsed_method->is_consteval;
                cpp_method->is_deleted = parsed_method->is_deleted;
                cpp_method->is_defaulted = parsed_method->is_defaulted;
                cpp_method->is_defaulted_on_first_declaration =
                    parsed_method->is_defaulted;
                cpp_method->is_conversion_function =
                    decl_parser.is_conversion_function;
                cpp_method->is_explicit_conversion = member_explicit;
                cpp_method->explicit_specifier = member_explicit_specifier;
                cpp_method->conversion_target_type =
                    decl_parser.conversion_target_type;
                cpp_method->is_virtual = method_is_virtual;
                cpp_method->is_override = method_is_override;
                cpp_method->is_final = method_is_final;
                cpp_method->is_pure = method_is_pure;
                cpp_method->set_language_linkage(parsed_method->get_language_linkage());
                if (parsed_method->asm_label) {
                    cpp_method->set_asm_label(*parsed_method->asm_label);
                }

                if (auto* existing_prefix =
                        get_func_decl_cxx_qualifier_prefix(parsed_method.get())) {
                    method_qualifier_prefix = *existing_prefix;
                }
                set_func_decl_cxx_qualifier_prefix(parsed_method.get(), std::nullopt);
            }

            QualType defaulted_method_owner_type;
            if (!cxx_record_parse_stack_.empty()) {
                const auto& record_frame = cxx_record_parse_stack_.back();
                defaulted_method_owner_type =
                    record_frame.semantic_owner
                        ? QualType(record_frame.semantic_owner->get_record_type())
                        : QualType();
                if (!defaulted_method_owner_type && !record_frame.name.empty()) {
                    auto owner_type_raw = collect_->collect_lookup_tag_type(
                        record_frame.name,
                        true);
                    auto owner_object_type =
                        dyn_cast_shared<ObjectType>(owner_type_raw);
                    if (owner_object_type) {
                        defaulted_method_owner_type = QualType(owner_object_type);
                    }
                }
            }
            if (cpp_method->is_defaulted &&
                !is_defaultable_method(
                    cpp_method.get(),
                    defaulted_method_owner_type,
                    ast_ctx.get())) {
                error_custloc(
                    "only comparison operators and copy/move assignment operators may be defaulted here",
                    cpp_method->location);
            }

            std::string record_qualifier_prefix = current_cpp_record_qualifier_prefix();
            ensure_namespace_qualifier_prefix(method_qualifier_prefix);
            if (!record_qualifier_prefix.empty()) {
                if (!method_qualifier_prefix.empty()) {
                    method_qualifier_prefix += "::";
                }
                method_qualifier_prefix += record_qualifier_prefix;
            }
            if (!method_qualifier_prefix.empty()) {
                set_func_decl_cxx_qualifier_prefix(cpp_method.get(),
                                                   method_qualifier_prefix);
            }

            // Lower non-static methods with an explicit object parameter.
            bool is_static_method = cpp_method->storage_class == StorageClass::STATIC;
            bool is_operator_new_delete =
                cpp_method->name == "operatornew" ||
                cpp_method->name == "operatornew[]" ||
                cpp_method->name == "operatordelete" ||
                cpp_method->name == "operatordelete[]";
            if (cpp_method->is_consteval && is_operator_new_delete) {
                error_custloc(
                    "allocation/deallocation function cannot be consteval",
                    cpp_method->location);
            }
            bool has_implicit_object_parameter =
                !is_static_method && !is_operator_new_delete;
            if (has_implicit_object_parameter &&
                !cxx_record_parse_stack_.empty() &&
                !cxx_record_parse_stack_.back().name.empty()) {
                const auto& record_frame = cxx_record_parse_stack_.back();
                auto owner_type =
                    record_frame.semantic_owner
                        ? record_frame.semantic_owner->get_record_type()
                        : nullptr;
                if (!owner_type) {
                    auto owner_type_raw = collect_->collect_lookup_tag_type(
                        record_frame.name,
                        true);
                    owner_type = dyn_cast_shared<ObjectType>(owner_type_raw);
                }
                if (owner_type) {
                    uint8_t this_object_quals =
                        static_cast<uint8_t>(
                            decl_parser.trailing_function_cv_qualifiers &
                            static_cast<uint8_t>(QUAL_CONST | QUAL_VOLATILE));
                    QualType qualified_owner_type(owner_type, this_object_quals);
                    QualType this_type(
                        std::make_shared<PointerType>(qualified_owner_type));
                    auto this_param = collect_->collect_parameter_declaration(
                        this_type, "this", nullptr, StorageClass::NONE, t.loc);
                    cpp_method->parameters.insert(
                        cpp_method->parameters.begin(), std::move(this_param));
                    auto fn_type = dyn_cast_shared<FunctionType>(cpp_method->type);
                    if (fn_type) {
                        fn_type->insert_parameter(0, this_type);
                        fn_type->has_prototype = true;
                    }
                }
            }

            ast_ctx->append_attrs(cpp_method->node_id,
                                  std::move(decl_parser.leading_attrs));
            ast_ctx->append_attrs(cpp_method->node_id,
                                  std::move(field_attrs_before_colon));
            fields.push_back(std::move(cpp_method));

            if (auto* method = dyn_cast<CppMethodDecl>(fields.back().get());
                method && (method->body != nullptr || method->has_deferred_inline_body())) {
                // In-class method definitions do not require a trailing semicolon.
                return fields;
            }

            if (gentle_check(TokenType::COMMA)) {
                advance();
                continue;
            }
            if (lang_opts.implicit_int && gentle_check(TokenType::RIGHT_BRACE)) {
                diag_engine->report_warning(
                    "missing ';' after class member declaration; assuming ';'",
                    current_token().loc);
                break;
            }
            check_and_consume(TokenType::SEMICOLON);
            break;
        }

        if (declaration_leading_virtual) {
            error("'virtual' can only be specified for class member functions");
        }

        if (member_explicit_specifier.is_present) {
            error("'explicit' is only allowed on constructors and conversion functions");
        }

        bool in_cpp_record_body =
            is_cxx_mode_active() &&
            is_parsing_cpp_record_body() &&
            !cxx_record_parse_stack_.empty();
        bool in_cpp_named_class_body =
            in_cpp_record_body &&
            cxx_record_parse_stack_.back().kind != CppRecordKind::Union;
        bool is_typedef_member_decl =
            in_cpp_record_body &&
            decl_parser.str_class == StorageClass::TYPEDEF;
        bool is_static_data_member_decl =
            in_cpp_named_class_body &&
            decl_parser.str_class == StorageClass::STATIC;
        if (decl_parser.is_mutable && is_static_data_member_decl) {
            error_custloc(
                "'mutable' cannot be applied to static data members",
                decl_parser.begin_loc);
        }
        if (in_cpp_named_class_body &&
            decl_parser.str_class != StorageClass::NONE &&
            decl_parser.str_class != StorageClass::STATIC &&
            decl_parser.str_class != StorageClass::TYPEDEF) {
            error("invalid storage class specifier in class member declaration");
        }

        if (is_typedef_member_decl) {
            if (decl_parser.is_mutable) {
                error_custloc(
                    "'mutable' cannot be applied to typedef declarations",
                    decl_parser.begin_loc);
            }
            handle_typedef_declarator(
                decl_parser,
                t,
                field_type,
                field_attrs_before_colon,
                decl_parser.is_constexpr,
                decl_parser.is_consteval,
                fields);

            if (gentle_check(TokenType::COMMA)) {
                advance();
                continue;
            }
            if (lang_opts.implicit_int && gentle_check(TokenType::RIGHT_BRACE)) {
                diag_engine->report_warning(
                    "missing ';' after class member declaration; assuming ';'",
                    current_token().loc);
                break;
            }
            check_and_consume(TokenType::SEMICOLON);
            break;
        }

        if (decl_parser.is_consteval) {
            error("'consteval' can only be applied to function declarations");
        }

        // Check for bitfield syntax: field_name : width or just : width (anonymous)
        if (gentle_check_and_consume(TokenType::COLON)) {
            if (is_static_data_member_decl) {
                error("static data member declaration cannot be a bitfield");
            }
            validate_mutable_data_member();
            auto width_expr = parse_conditional_expression();
            auto width_val = try_evaluate_with_consteval_compat(
                width_expr.get(), ConstEvalMode::c_ice());
            if (!width_val.has_value()) {
                error("Bitfield width must be a constant expression");
                return {};
            }
            int64_t bitfield_width = *width_val;
            if (bitfield_width < 0) {
                error("Bitfield width cannot be negative");
                return {};
            }
            // Zero-width bitfield must be anonymous
            if (bitfield_width == 0 && !field_name.empty()) {
                error("Zero-width bitfield must be anonymous (no name)");
                return {};
            }

            // GCC accepts attributes after the bitfield width.
            auto field_attrs_after_width = try_parse_attributes();

            auto field_decl = collect_->collect_field_declaration(
                QualType(field_type, decl_parser.qualifiers),
                field_name,
                static_cast<uint32_t>(bitfield_width),
                t.loc);
            if (auto* parsed_field = dyn_cast<FieldDecl>(field_decl.get())) {
                parsed_field->is_mutable = decl_parser.is_mutable;
            }
            ast_ctx->append_attrs(field_decl->node_id, std::move(decl_parser.leading_attrs));
            ast_ctx->append_attrs(field_decl->node_id, std::move(field_attrs_before_colon));
            ast_ctx->append_attrs(field_decl->node_id, std::move(field_attrs_after_width));
            fields.push_back(std::move(field_decl));
        } else {
            if (is_static_data_member_decl) {
                if (field_name.empty()) {
                    error("static data member declaration requires an identifier");
                }
                if (decl_parser.is_thread_local) {
                    error("thread-local storage class is not supported on class static data members");
                }
                if (decl_parser.asm_label.has_value()) {
                    error("asm label on class static data member declarations is not supported");
                }

                QualType static_member_type(field_type, decl_parser.qualifiers);
                std::unique_ptr<Expr> static_member_init;
                bool is_copy_initialization = false;
                bool is_cxx_object_decl =
                    is_cxx_mode_active() &&
                    can_parse_cxx_object_initializer_syntax(static_member_type);
                if (gentle_check_and_consume(TokenType::ASSIGN)) {
                    is_copy_initialization = true;
                    if (gentle_check(TokenType::LEFT_BRACE)) {
                        static_member_init = parse_init_list();
                    } else {
                        static_member_init = parse_assignment_expression();
                    }
                } else if (is_cxx_object_decl && gentle_check(TokenType::LEFT_PAREN)) {
                    static_member_init = parse_paren_init_list();
                } else if (is_cxx_object_decl && gentle_check(TokenType::LEFT_BRACE)) {
                    static_member_init = parse_init_list();
                }

                auto static_member_decl_base = collect_->collect_variable_declaration(
                    static_member_type,
                    field_name,
                    std::move(static_member_init),
                    nullptr,
                    decl_parser.str_class,
                    {decl_parser.is_constexpr, decl_parser.is_inline,
                     collect_->collect_is_file_scope(), true, false,
                     decl_parser.is_thread_local, decl_parser.is_block_byref,
                     is_copy_initialization, false, false},
                    t.loc,
                    current_decl_language_linkage());
                auto* static_member_decl =
                    dyn_cast<VariableDecl>(static_member_decl_base.get());
                if (!static_member_decl) {
                    error("internal error: expected VariableDecl for class static data member");
                }
                static_member_decl->is_thread_local = decl_parser.is_thread_local;
                static_member_decl->set_asm_label(decl_parser.asm_label);
                ast_ctx->append_attrs(static_member_decl->node_id,
                                      std::move(decl_parser.leading_attrs));
                ast_ctx->append_attrs(static_member_decl->node_id,
                                      std::move(field_attrs_before_colon));
                fields.push_back(std::move(static_member_decl_base));

                if (gentle_check(TokenType::COMMA)) {
                    advance();
                    continue;
                }
                if (lang_opts.implicit_int && gentle_check(TokenType::RIGHT_BRACE)) {
                    diag_engine->report_warning(
                        "missing ';' after class member declaration; assuming ';'",
                        current_token().loc);
                    break;
                }
                check_and_consume(TokenType::SEMICOLON);
                break;
            }
            // Not a bitfield - regular field
            validate_mutable_data_member();
            // Check if we got a name - allow anonymous struct/union fields
            if (field_name.empty()) {
                auto obj_type = dyn_cast_shared<ObjectType>(field_type);
                if (!obj_type || obj_type->isIncomplete()) {
                    error("Anonymous struct/union fields must be a complete struct or union type");
                    return {};
                }
            }
            auto field_decl = collect_->collect_field_declaration(
                QualType(field_type, decl_parser.qualifiers),
                field_name,
                t.loc);
            if (auto* parsed_field = dyn_cast<FieldDecl>(field_decl.get())) {
                parsed_field->is_mutable = decl_parser.is_mutable;
            }
            ast_ctx->append_attrs(field_decl->node_id, std::move(decl_parser.leading_attrs));
            ast_ctx->append_attrs(field_decl->node_id, std::move(field_attrs_before_colon));
            fields.push_back(std::move(field_decl));
        }

        if (gentle_check(TokenType::COMMA)) {
            advance();
            continue;
        }
        if (lang_opts.implicit_int && gentle_check(TokenType::RIGHT_BRACE)) {
            // GNU permissive recovery: allow missing ';' at end of field decl.
            diag_engine->report_warning(
                "missing ';' after struct/union field declaration; assuming ';'",
                current_token().loc);
            break;
        }
        check_and_consume(TokenType::SEMICOLON);
        break;
    }
    return fields;
}

// Parse struct specifier: struct tag { fields } or struct tag
std::unique_ptr<Decl> Parser::parse_struct_specifier() {
    Token struct_tok = current_token();
    bool isUnion = false;
    if (gentle_check(TokenType::UNION)) {
        isUnion = true;
        check_and_consume(TokenType::UNION);
    } else {
        check_and_consume(TokenType::STRUCT);
    }

    std::string tag;
    bool has_tag = false;
    auto read_record_state = [&](const ObjectDecl* record_decl) -> RecordSemanticState {
        RecordSemanticState state;
        if (!record_decl) {
            return state;
        }
        const RecordSemanticState* cached =
            collect_ ? collect_->query_lookup_record_semantics(record_decl)
                     : record_semantics_cache_lookup(record_decl);
        if (cached) {
            state = *cached;
        }
        return state;
    };
    auto write_record_state = [&](const ObjectDecl* record_decl, RecordSemanticState state) {
        if (collect_) {
            collect_->query_publish_record_semantics(record_decl,
                                                     std::move(state));
            return;
        }
        record_semantics_cache_set(ast_ctx.get(), record_decl, std::move(state));
    };
    auto extract_record_decl = [&](TagDecl* existing_tag_decl,
                                   const std::string& existing_tag) -> ObjectDecl* {
        auto* existing_obj_decl = dyn_cast<ObjectDecl>(existing_tag_decl);
        if (!existing_obj_decl) {
            error("tag '" + existing_tag + "' was previously declared with a different kind");
        }
        auto existing_obj_type = existing_obj_decl ? existing_obj_decl->get_record_type() : nullptr;
        if (!existing_obj_type) {
            error("tag '" + existing_tag + "' was previously declared with a different kind");
        }
        return existing_obj_decl;
    };
    auto copy_record_decl_state = [&](const ObjectDecl* src, ObjectDecl* dst) {
        if (!src || !dst) {
            return;
        }
        const RecordSemanticState* src_state =
            collect_ ? collect_->query_lookup_record_semantics(src)
                     : record_semantics_cache_lookup(src);
        if (src_state) {
            write_record_state(dst, *src_state);
        }
    };

    // Parse attributes after struct/union keyword (e.g., struct __attribute__((packed)) S { ... })
    auto pre_attrs = try_parse_attributes();
    auto has_packed_attr = [](const std::vector<ParsedAttribute>& attrs) {
        for (const auto& attr : attrs) {
            if (attr.canonical_name() == "packed") {
                return true;
            }
        }
        return false;
    };
    auto has_transparent_union_attr = [](const std::vector<ParsedAttribute>& attrs) {
        for (const auto& attr : attrs) {
            if (attr.canonical_name() == "transparent_union") {
                return true;
            }
        }
        return false;
    };
    auto max_aligned_attr = [](const std::vector<ParsedAttribute>& attrs) -> size_t {
        size_t best = 0;
        for (const auto& attr : attrs) {
            if (attr.canonical_name() != "aligned") {
                continue;
            }
            if (attr.args.empty()) {
                continue;
            }
            if (attr.args[0].kind != AttributeArg::Kind::INTEGER ||
                attr.args[0].int_value <= 0) {
                continue;
            }
            size_t align = static_cast<size_t>(attr.args[0].int_value);
            if (align > best) {
                best = align;
            }
        }
        return best;
    };

    // Check for tag name
    if (gentle_check(TokenType::IDENTIFIER)) {
        tag = current_token().value;
        has_tag = true;
        advance();
    }

    // Check for struct body
    if (gentle_check(TokenType::LEFT_BRACE)) {
        if (has_tag && collect_) {
            if (auto* existing_tag_decl = collect_->collect_lookup_tag_decl(tag, false)) {
                auto* existing_obj_decl = extract_record_decl(existing_tag_decl, tag);
                auto existing_obj = existing_obj_decl->get_record_type();
                if (existing_obj->is_union != isUnion) {
                    error("tag '" + tag + "' was previously declared as a different kind");
                }
            } else {
                auto placeholder_type =
                    std::make_shared<ObjectType>(tag, isUnion, true);
                auto placeholder_decl = collect_->collect_record_declaration(
                    tag,
                    placeholder_type,
                    isUnion,
                    struct_tok.loc);
                if (placeholder_decl) {
                    write_record_state(placeholder_decl.get(), RecordSemanticState{});
                    collect_->collect_add_tag_decl(tag, placeholder_decl.get());
                    // Keep parser-time placeholder tags alive for decl-context
                    // lookups until the completed definition replaces them.
                    cpp_transient_semantic_decls_.push_back(
                        std::move(placeholder_decl));
                }
            }
        }
        advance(); // consume '{'

        // Parse field declarations
        std::vector<std::unique_ptr<Decl>> field_decls;
        size_t last_recovery_idx = std::numeric_limits<size_t>::max();
        while (!gentle_check(TokenType::RIGHT_BRACE) && !gentle_check(TokenType::Eof)) {
            try {
                auto fields = parse_struct_declaration();
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();
                for (auto &field : fields) {
                    field_decls.push_back(std::move(field));
                }
            } catch (ParseError& e) {
                if (is_in_tentative_context()) {
                    throw;
                }
                size_t recover_start_idx = get_token_idx();
                skip_to_field_sync_point();
                if (get_token_idx() == recover_start_idx &&
                    recover_start_idx == last_recovery_idx &&
                    !gentle_check(TokenType::Eof)) {
                    advance();
                }
                last_recovery_idx = get_token_idx();
                diag_engine->sync_point_reached();
                field_decls.push_back(collect_->collect_error_declaration(e.message, e.location));
            }
        }

        check_and_consume(TokenType::RIGHT_BRACE);

        // Parse attributes after closing brace
        auto post_attrs = try_parse_attributes();
        bool packed_attr = has_packed_attr(pre_attrs) || has_packed_attr(post_attrs);
        bool transparent_union_attr = has_transparent_union_attr(pre_attrs) || has_transparent_union_attr(post_attrs);
        size_t aligned_attr = std::max(max_aligned_attr(pre_attrs), max_aligned_attr(post_attrs));
        size_t pragma_pack = tok_mgnt.sm ? tok_mgnt.sm->getPackAlignment(struct_tok.loc) : 0;

        // Build RecordType::Field vector from FieldDecl nodes
        std::vector<ObjectType::Field> fields;
        for (const auto& decl : field_decls) {
            if (auto *field_decl = dyn_cast<FieldDecl>(decl.get())) {
                size_t forced_alignment = 0;
                const auto& attrs = ast_ctx->get_attrs(field_decl->node_id);
                for (const auto& attr : attrs.attrs) {
                    if (attr.resolved_kind != AttributeKind::ALIGNED ||
                        attr.args.empty() ||
                        attr.args[0].kind != AttributeArg::Kind::INTEGER ||
                        attr.args[0].int_value <= 0) {
                        continue;
                    }
                    size_t candidate = static_cast<size_t>(attr.args[0].int_value);
                    if (candidate > forced_alignment) {
                        forced_alignment = candidate;
                    }
                }
                if (field_decl->is_bitfield()) {
                    // Bitfield: use the bitfield constructor
                    // offset, bit_offset, storage_size will be computed later in computeLayout
                    fields.emplace_back(field_decl->name, field_decl->type, 0,
                        0, field_decl->bitfield_width, 0);
                    fields.back().forced_alignment = forced_alignment;
                } else {
                    // Regular field
                    fields.emplace_back(field_decl->name, field_decl->type, 0);
                    fields.back().forced_alignment = forced_alignment;
                }
            }
        }

        // If there's already an incomplete record declaration for this tag in
        // the current scope, complete its ObjectType in-place so existing uses
        // (e.g. self-referential pointer fields) observe the completed type.
        std::shared_ptr<ObjectType> record_type;
        if (has_tag) {
            // A tagged definition in an inner scope may legally shadow an
            // outer tag with the same spelling but different kind.
            if (auto* existing_tag_decl = collect_->collect_lookup_tag_decl(tag, false)) {
                auto* existing_obj_decl = extract_record_decl(existing_tag_decl, tag);
                auto existing_obj = existing_obj_decl->get_record_type();
                if (existing_obj->is_union != isUnion) {
                    error("tag '" + tag + "' was previously declared as a different kind");
                }
                auto existing_state = read_record_state(existing_obj_decl);
                if (existing_state.is_incomplete) {
                    existing_obj->is_packed = packed_attr;
                    existing_obj->is_transparent_union = transparent_union_attr && isUnion;
                    if (aligned_attr > existing_obj->requested_alignment) {
                        existing_obj->requested_alignment = aligned_attr;
                    }
                    existing_obj->pack_alignment = pragma_pack;
                    record_type = existing_obj;
                }
            }
        }
        if (!record_type) {
            record_type = std::make_shared<ObjectType>(tag, isUnion);
            record_type->is_packed = packed_attr;
            record_type->is_transparent_union = transparent_union_attr && isUnion;
            record_type->requested_alignment = aligned_attr;
            record_type->pack_alignment = pragma_pack;
        }
        RecordSemanticState record_state = compute_record_semantics(
            std::move(fields),
            record_type->is_union,
            record_type->is_packed,
            record_type->requested_alignment,
            record_type->pack_alignment,
            false,
            ast_ctx && ast_ctx->abi_policy ? ast_ctx->abi_policy.get() : nullptr);
        auto ret_obj = collect_->collect_record_declaration(
            tag,
            std::move(field_decls),
            record_type,
            isUnion,
            struct_tok.loc);
        write_record_state(ret_obj.get(), std::move(record_state));
        record_type->set_decl(ret_obj.get());
        if (has_tag) {
            collect_->collect_add_tag_decl(tag, ret_obj.get());
        }
        ast_ctx->append_attrs(ret_obj->node_id, std::move(pre_attrs));
        ast_ctx->append_attrs(ret_obj->node_id, std::move(post_attrs));
        return ret_obj;
    } else {
        // Just a tag reference: struct tag (forward declaration or use)
        if (!has_tag) {
            error("Expected struct tag or body");
            return nullptr;
        }
        // Reuse an existing ObjectType if the tag was already declared.
        // Prefer current scope; then fall back to parent scopes only for
        // same-kind tags. A different-kind parent tag can be shadowed here.
        if (auto* existing_decl = collect_->collect_lookup_tag_decl(tag, false)) {
            auto* existing_obj_decl = extract_record_decl(existing_decl, tag);
            auto existing_obj = existing_obj_decl->get_record_type();
            if (existing_obj->is_union != isUnion) {
                error("tag '" + tag + "' was previously declared as a different kind");
            }
            auto ret_obj = collect_->collect_record_declaration(
                tag, existing_obj, isUnion, struct_tok.loc);
            copy_record_decl_state(existing_obj_decl, ret_obj.get());
            return ret_obj;
        } else if (auto* inherited_decl = collect_->collect_lookup_tag_decl(tag)) {
            auto* inherited_obj_decl = extract_record_decl(inherited_decl, tag);
            auto inherited_obj = inherited_obj_decl->get_record_type();
            if (inherited_obj && inherited_obj->is_union == isUnion) {
                // C tag namespace rule: a block-scope forward declaration
                // "struct T;" introduces a new incomplete tag that can shadow
                // an outer tag with the same spelling.
                if (gentle_check(TokenType::SEMICOLON)) {
                    auto shadow = std::make_shared<ObjectType>(tag, isUnion, true);
                    auto ret_obj = collect_->collect_record_declaration(
                        tag, shadow, isUnion, struct_tok.loc);
                    write_record_state(ret_obj.get(), RecordSemanticState{});
                    shadow->set_decl(ret_obj.get());
                    collect_->collect_add_tag_decl(tag, ret_obj.get());
                    return ret_obj;
                }
                auto ret_obj = collect_->collect_record_declaration(
                    tag, inherited_obj, isUnion, struct_tok.loc);
                copy_record_decl_state(inherited_obj_decl, ret_obj.get());
                return ret_obj;
            }
        }
        // No existing tag found — create a new incomplete type and register it
        auto type = std::make_shared<ObjectType>(tag, isUnion, true);
        auto ret_obj = collect_->collect_record_declaration(tag, type, isUnion, struct_tok.loc);
        write_record_state(ret_obj.get(), RecordSemanticState{});
        type->set_decl(ret_obj.get());
        collect_->collect_add_tag_decl(tag, ret_obj.get());
        return ret_obj;

    }
}

std::unique_ptr<Decl> Parser::parse_enum_specifier() {
    Token enum_tok = current_token();
    check_and_consume(TokenType::ENUM);

    bool is_scoped = false;
    if (is_cxx_mode_active() &&
        (gentle_check(TokenType::CLASS) || gentle_check(TokenType::STRUCT))) {
        is_scoped = true;
        advance();
    }

    auto pre_attrs = try_parse_attributes();
    std::string tag;
    bool has_tag = false;

    if (gentle_check(TokenType::IDENTIFIER)) {
        tag = current_token().value;
        has_tag = true;
        advance();
    }

    auto post_tag_attrs = try_parse_attributes();
    bool packed_attr = has_packed_attr(pre_attrs) || has_packed_attr(post_tag_attrs);

    bool has_fixed_underlying = false;
    std::shared_ptr<CType> fixed_underlying = nullptr;
    std::shared_ptr<CType> fixed_underlying_validation = nullptr;
    auto realize_enum_underlying_for_validation =
        [&](const std::shared_ptr<CType>& underlying) -> std::shared_ptr<CType> {
        if (!underlying) {
            return nullptr;
        }
        QualType realized(underlying);
        if (collect_) {
            if (auto collect_realized =
                    collect_->try_realize_deferred_semantic_type(realized)) {
                realized = collect_realized;
            }
        }
        return realized.get_shared();
    };
    if (gentle_check(TokenType::COLON)) {
        if (!is_cxx_mode_active() &&
            !lang_opts.standard.empty() &&
            !is_c23_family_standard(lang_opts.standard)) {
            diag_engine->report_error(
                "fixed underlying enum type requires C23 or GNU2x mode", current_token().loc);
        }
        advance(); // consume ':'
        DeclarationParser underlying_parser(this);
        fixed_underlying = underlying_parser.parse_declaration(false);
        fixed_underlying_validation =
            realize_enum_underlying_for_validation(fixed_underlying);
        if (!fixed_underlying ||
            !is_valid_fixed_enum_underlying_type(
                fixed_underlying_validation,
                ast_ctx.get())) {
            diag_engine->report_error(
                "invalid fixed underlying type for enum", current_token().loc);
            fixed_underlying = type_ctx->get_builtin(BuiltinTypes::Int);
            fixed_underlying_validation = fixed_underlying;
        }
        has_fixed_underlying = true;
    }

    auto read_enum_state = [&](const EnumDecl* enum_decl) -> EnumSemanticState {
        EnumSemanticState state;
        if (!enum_decl) {
            return state;
        }
        if (collect_) {
            collect_->query_lookup_enum_semantics(enum_decl, state);
        } else {
            enum_semantics_cache_lookup(enum_decl, state, ast_ctx.get());
        }
        return state;
    };
    auto write_enum_state = [&](const EnumDecl* enum_decl, const EnumSemanticState& state) {
        if (collect_) {
            collect_->query_publish_enum_semantics(enum_decl, state);
            return;
        }
        enum_semantics_cache_set(ast_ctx.get(), enum_decl, state);
    };
    auto expected_underlying_type =
        [&]() -> std::shared_ptr<CType> {
        if (has_fixed_underlying) {
            return fixed_underlying;
        }
        if (is_cxx_mode_active() && is_scoped) {
            return type_ctx->get_builtin(BuiltinTypes::Int);
        }
        return nullptr;
    };
    auto expected_underlying_validation_type =
        [&]() -> std::shared_ptr<CType> {
        if (has_fixed_underlying) {
            return fixed_underlying_validation;
        }
        if (is_cxx_mode_active() && is_scoped) {
            return type_ctx->get_builtin(BuiltinTypes::Int);
        }
        return nullptr;
    };

    auto reconcile_tag_decl = [&](EnumDecl* enum_decl, SrcLoc loc) {
        if (!enum_decl) {
            return;
        }
        auto state = read_enum_state(enum_decl);
        if (state.is_scoped != is_scoped) {
            diag_engine->report_error(
                "enum declaration scopedness mismatch with previous declaration",
                loc);
            return;
        }
        auto expected_underlying = expected_underlying_type();
        if (!expected_underlying) {
            return;
        }
        if (state.underlying_type &&
            !state.underlying_type->equals(*expected_underlying)) {
            diag_engine->report_error(
                "enum underlying type mismatch with previous declaration", loc);
            return;
        }
        state.underlying_type = expected_underlying;
        write_enum_state(enum_decl, state);
    };
    auto extract_enum_decl = [&](TagDecl* existing_tag_decl,
                                 const std::string& existing_tag) -> EnumDecl* {
        auto* existing_enum_decl = dyn_cast<EnumDecl>(existing_tag_decl);
        if (!existing_enum_decl) {
            error("tag '" + existing_tag + "' was previously declared with a different kind");
        }
        auto existing_enum_type = existing_enum_decl ? existing_enum_decl->get_enum_type() : nullptr;
        if (!existing_enum_type) {
            error("tag '" + existing_tag + "' was previously declared with a different kind");
        }
        return existing_enum_decl;
    };
    auto copy_enum_decl_state = [&](const EnumDecl* src, EnumDecl* dst) {
        if (!src || !dst) {
            return;
        }
        write_enum_state(dst, read_enum_state(src));
    };
    auto build_enumerator_state =
        [](const EnumDecl* enum_decl) {
            std::vector<EnumSemanticState::Enumerator> enumerators;
            if (!enum_decl) {
                return enumerators;
            }
            enumerators.reserve(enum_decl->constants.size());
            for (const auto& constant : enum_decl->constants) {
                if (!constant) {
                    continue;
                }
                EnumSemanticState::Enumerator enumerator;
                enumerator.name = constant->name;
                enumerator.decl = constant.get();
                enumerator.symbol = constant->sym;
                enumerator.value = constant->value;
                enumerators.push_back(std::move(enumerator));
            }
            return enumerators;
        };

    bool has_braced_definition = gentle_check(TokenType::LEFT_BRACE);
    if (is_cxx_mode_active() &&
        !has_braced_definition &&
        !is_scoped &&
        !has_fixed_underlying) {
        diag_engine->report_error(
            "opaque enum declaration requires an explicit underlying type in C++",
            enum_tok.loc);
    }

    if (has_braced_definition) {
        advance(); // consume '{'

        EnumDecl* existing_enum_decl = nullptr;
        std::shared_ptr<EnumType> enum_type = nullptr;
        if (has_tag) {
            if (auto* existing_tag_decl = collect_->collect_lookup_tag_decl(tag, false)) {
                existing_enum_decl = extract_enum_decl(existing_tag_decl, tag);
                enum_type = existing_enum_decl->get_enum_type();
            }
        }
        if (!enum_type) {
            enum_type = std::make_shared<EnumType>(tag);
        }

        std::shared_ptr<CType> enum_underlying = expected_underlying_type();
        bool enum_has_negative_values = false;
        if (existing_enum_decl) {
            auto existing_state = read_enum_state(existing_enum_decl);
            if (existing_state.is_scoped != is_scoped) {
                diag_engine->report_error(
                    "enum declaration scopedness mismatch with previous declaration",
                    enum_tok.loc);
            }
            if (!existing_state.underlying_type) {
                existing_state.underlying_type = enum_underlying;
                existing_state.is_scoped = is_scoped;
                write_enum_state(existing_enum_decl, existing_state);
            }
            reconcile_tag_decl(existing_enum_decl, enum_tok.loc);
            existing_state = read_enum_state(existing_enum_decl);
            is_scoped = existing_state.is_scoped;
            if (existing_state.underlying_type) {
                enum_underlying = existing_state.underlying_type;
            }
            enum_has_negative_values = existing_state.has_negative_values;
        }
        std::shared_ptr<CType> enum_underlying_validation =
            existing_enum_decl
                ? realize_enum_underlying_for_validation(enum_underlying)
                : expected_underlying_validation_type();
        bool validate_against_fixed_underlying =
            has_fixed_underlying || (is_cxx_mode_active() && is_scoped);
        auto enum_underlying_builtin = fixed_enum_integer_underlying_type(
            enum_underlying_validation,
            ast_ctx.get());
        if (enum_underlying_builtin && enum_underlying_builtin->isUnsigned()) {
            enum_has_negative_values = false;
        }

        std::vector<std::unique_ptr<EnumConstantDecl>> constants;
        std::unordered_set<std::string> seen_enumerator_names;
        int64_t next_enum_value = 0;
        bool saw_any_enumerator = false;
        int64_t min_enum_value = 0;
        int64_t max_enum_value = 0;
        size_t last_recovery_idx = std::numeric_limits<size_t>::max();
        while (!gentle_check(TokenType::RIGHT_BRACE) && !gentle_check(TokenType::Eof)) {
            try {
                if (!gentle_check(TokenType::IDENTIFIER)) {
                    error("Expected identifier in enum list");
                    return nullptr;
                }
                std::string name = current_token().value;
                SrcLoc loc = current_token().loc;
                advance();

                // Skip attributes on enum constants (e.g. __attribute__((availability(...))))
                while (is_gnu_attribute_token(current_token())) {
                    try_parse_attributes();
                }

                std::unique_ptr<Expr> init = nullptr;
                if (gentle_check_and_consume(TokenType::ASSIGN)) {
                    init = parse_conditional_expression();
                }

                if (!seen_enumerator_names.insert(name).second) {
                    diag_engine->report_error(
                        "redefinition of enum constant '" + name + "'", loc);
                }
                bool inject_enumerator_into_scope =
                    !is_cxx_mode_active() ||
                    (!is_scoped && !is_parsing_cpp_record_body());
                if (inject_enumerator_into_scope) {
                    auto existing = collect_->collect_lookup_variable_symbol(name, false);
                    if (existing) {
                        diag_engine->report_error(
                            "redefinition of enum constant '" + name + "'", loc);
                    }
                }

                int64_t enum_value = next_enum_value;
                if (init) {
                    auto eval = try_evaluate_with_consteval_compat(
                        init.get(), ConstEvalMode::c_ice());
                    if (!eval.has_value() &&
                        !collect_->expression_depends_on_template_parameters(
                            init.get())) {
                        diag_engine->report_error(
                            "enumerator value is not an integer constant expression", loc);
                    } else if (eval.has_value()) {
                        enum_value = *eval;
                    }
                }

                if (validate_against_fixed_underlying &&
                    !fixed_enum_value_fits_underlying(
                        enum_value,
                        enum_underlying_validation,
                        ast_ctx.get())) {
                    diag_engine->report_error(
                        "enumerator value is not representable in fixed underlying enum type", loc);
                }
                if (enum_value < 0) {
                    enum_has_negative_values = true;
                }
                if (!saw_any_enumerator) {
                    min_enum_value = enum_value;
                    max_enum_value = enum_value;
                    saw_any_enumerator = true;
                } else {
                    min_enum_value = std::min(min_enum_value, enum_value);
                    max_enum_value = std::max(max_enum_value, enum_value);
                }

                auto enum_const = collect_->collect_enum_constant_declaration(name, std::move(init), loc);
                enum_const->value = enum_value;

                // Enumerator constants have type int in C.
                auto enum_sym = std::make_shared<Symbol>(
                    name,
                    SymbolKind::ENUM_CONSTANT,
                    QualType(type_ctx->get_builtin(BuiltinTypes::Int)),
                    StorageClass::NONE);
                enum_sym->enum_val = enum_value;
                enum_const->sym = enum_sym;
                if (inject_enumerator_into_scope) {
                    collect_->collect_bind_symbol_in_current_scope(name, enum_sym);
                    collect_->collect_add_global_symbol(enum_sym);
                }

                constants.push_back(std::move(enum_const));
                if (__builtin_add_overflow(enum_value, int64_t{1}, &next_enum_value)) {
                    diag_engine->report_error(
                        "incremented enumerator value is not representable in int64", loc);
                    next_enum_value = enum_value;
                }
                diag_engine->sync_point_reached();
                last_recovery_idx = std::numeric_limits<size_t>::max();

                if (!gentle_check(TokenType::RIGHT_BRACE)) {
                    check_and_consume(TokenType::COMMA);
                }
            } catch (ParseError& e) {
                if (is_in_tentative_context()) {
                    throw;
                }
                size_t recover_start_idx = get_token_idx();
                skip_to_enum_sync_point();
                if (get_token_idx() == recover_start_idx &&
                    recover_start_idx == last_recovery_idx &&
                    !gentle_check(TokenType::Eof)) {
                    advance();
                }
                last_recovery_idx = get_token_idx();
                diag_engine->sync_point_reached();
            }
        }
        check_and_consume(TokenType::RIGHT_BRACE);
        auto post_attrs = try_parse_attributes();
        packed_attr = packed_attr || has_packed_attr(post_attrs);
        if (!validate_against_fixed_underlying && saw_any_enumerator) {
            if (auto inferred = choose_default_enum_underlying(
                    type_ctx.get(), min_enum_value, max_enum_value, packed_attr)) {
                enum_underlying = inferred;
            }
        }
        if (is_cxx_mode_active() || enum_underlying) {
            for (auto& c : constants) {
                if (c && c->sym) {
                    if (is_cxx_mode_active()) {
                        c->sym->type = QualType(enum_type);
                    } else if (!enum_constant_fits_int(type_ctx.get(), c->value)) {
                        c->sym->type = QualType(enum_underlying);
                    }
                }
            }
        }
        auto ret_enum = collect_->collect_enum_declaration(
            tag, std::move(constants), enum_type, enum_tok.loc);
        EnumSemanticState final_state;
        final_state.is_incomplete = false;
        final_state.is_scoped = is_scoped;
        final_state.has_negative_values = enum_has_negative_values;
        final_state.underlying_type = enum_underlying;
        final_state.enumerators = build_enumerator_state(ret_enum.get());
        write_enum_state(ret_enum.get(), final_state);
        enum_type->set_decl(ret_enum.get());
        if (has_tag) {
            collect_->collect_add_tag_decl(tag, ret_enum.get());
        }
        return ret_enum;
    } else {
        if (!has_tag) {
            error("Expected enum tag or body");
            return nullptr;
        }
        // Reuse an existing enum type if the tag was already declared.
        // Prefer current scope; then fall back to parent scopes. A block-scope
        // forward declaration "enum T;" shadows an outer tag with same name.
        if (auto* existing_tag_decl = collect_->collect_lookup_tag_decl(tag, false)) {
            auto* existing_enum_decl = extract_enum_decl(existing_tag_decl, tag);
            reconcile_tag_decl(existing_enum_decl, enum_tok.loc);
            auto ret_enum = collect_->collect_enum_declaration(
                tag, existing_enum_decl->get_enum_type(), enum_tok.loc);
            copy_enum_decl_state(existing_enum_decl, ret_enum.get());
            return ret_enum;
        } else if (auto* inherited_tag_decl = collect_->collect_lookup_tag_decl(tag)) {
            auto* inherited_enum_decl = extract_enum_decl(inherited_tag_decl, tag);
            if (gentle_check(TokenType::SEMICOLON)) {
                auto shadow = std::make_shared<EnumType>(tag, true);
                auto shadow_underlying = expected_underlying_type();
                auto ret_enum = collect_->collect_enum_declaration(tag, shadow, enum_tok.loc);
                EnumSemanticState shadow_state;
                shadow_state.is_incomplete = true;
                shadow_state.is_scoped = is_scoped;
                shadow_state.has_negative_values = false;
                shadow_state.underlying_type = shadow_underlying;
                write_enum_state(ret_enum.get(), shadow_state);
                shadow->set_decl(ret_enum.get());
                collect_->collect_add_tag_decl(tag, ret_enum.get());
                return ret_enum;
            }
            auto inherited_state = read_enum_state(inherited_enum_decl);
            if (inherited_state.is_scoped != is_scoped) {
                diag_engine->report_error(
                    "enum declaration scopedness mismatch with previous declaration",
                    enum_tok.loc);
            }
            reconcile_tag_decl(inherited_enum_decl, enum_tok.loc);
            auto ret_enum = collect_->collect_enum_declaration(
                tag, inherited_enum_decl->get_enum_type(), enum_tok.loc);
            copy_enum_decl_state(inherited_enum_decl, ret_enum.get());
            return ret_enum;
        }
        auto enum_type = std::make_shared<EnumType>(tag, true);
        auto enum_underlying = expected_underlying_type();
        auto ret_enum = collect_->collect_enum_declaration(tag, enum_type, enum_tok.loc);
        EnumSemanticState opaque_state;
        opaque_state.is_incomplete = true;
        opaque_state.is_scoped = is_scoped;
        opaque_state.has_negative_values = false;
        opaque_state.underlying_type = enum_underlying;
        write_enum_state(ret_enum.get(), opaque_state);
        enum_type->set_decl(ret_enum.get());
        collect_->collect_add_tag_decl(tag, ret_enum.get());
        return ret_enum;
    }
}
bool Parser::isTokenDeclarationSpec(Token s) {
    if (is_gnu_attribute_token(s)) {
        return true;
    }
    if (s.type == TokenType::USING) {
        return is_cxx_mode_active();
    }
    if (s.type == TokenType::TEMPLATE) {
        return is_cxx_mode_active();
    }
    if (s.type == TokenType::CLASS) {
        return is_cxx_mode_active();
    }
    if (s.type == TokenType::TYPENAME) {
        return is_cxx_mode_active();
    }
    if (s.type == TokenType::FRIEND_KW) {
        return is_cxx_mode_active();
    }
    if (s.type == TokenType::EXPLICIT_KW) {
        return is_cxx_mode_active();
    }
    if (s.type == TokenType::MUTABLE_KW) {
        return is_cxx_mode_active();
    }
    if ((s.type == TokenType::CONSTEXPR_KW) ||
        (s.type == TokenType::IDENTIFIER &&
         s.value == "constexpr" &&
         is_c23_constexpr_enabled())) {
        return true;
    }
    if (s.type == TokenType::CONSTEVAL_KW) {
        return is_cxx_mode_active();
    }
    switch (s.type) {
        case TokenType::VOID:
        case TokenType::CHAR:
        case TokenType::SHORT:
        case TokenType::INT:
        case TokenType::LONG:
        case TokenType::FLOAT:
        case TokenType::DOUBLE:
        case TokenType::SIGNED:
        case TokenType::UNSIGNED:
        case TokenType::BOOL:
        case TokenType::WCHAR_T:
        case TokenType::CHAR16_T:
        case TokenType::CHAR32_T:
        case TokenType::STRUCT:
        case TokenType::UNION:
        case TokenType::ENUM:
        case TokenType::CONST:
        case TokenType::VOLATILE:
        case TokenType::RESTRICT:
        case TokenType::ATOMIC:
        case TokenType::INLINE:
        case TokenType::STATIC:
        case TokenType::EXTERN:
        case TokenType::AUTO:
        case TokenType::REGISTER:
        case TokenType::TYPEDEF:
        case TokenType::NORETURN_KW:
        case TokenType::STATIC_ASSERT:
        case TokenType::ALIGNAS:
        case TokenType::THREAD_LOCAL:
        case TokenType::EXTENSION_KW:
        case TokenType::TYPEOF_KW:
        case TokenType::DECLTYPE_KW:
        case TokenType::INT128:
        case TokenType::UINT128_T:
        case TokenType::AUTO_TYPE:
        case TokenType::COMPLEX:
        case TokenType::FLOAT16:
            return true;
        default:
            // Check if identifier names a type in declaration-specifier position.
            // In C mode this is typedef-only; in C++ mode we also allow class
            // names via tag lookup.
            if (s.type == TokenType::IDENTIFIER) {
                if (type_ctx && type_ctx->target &&
                    darwin_blocks::blocks_enabled_for_langopts(
                        lang_opts, *type_ctx->target) &&
                    s.value == "__block") {
                    return true;
                }
                if (collect_->collect_lookup_type_name(
                        s.value,
                        true,
                        is_cxx_mode_active())) {
                    return true;
                }
                if (is_cxx_mode_active()) {
                    QualType current_record_lookup_type =
                        collect_->collect_current_cpp_record_lookup_type();
                    if (current_record_lookup_type &&
                        collect_->collect_lookup_record_nested_type(
                            current_record_lookup_type,
                            s.value)) {
                        return true;
                    }
                }
                if (is_cxx_mode_active() &&
                    (is_cpp_qualified_id_start() ||
                     peek_token().type == TokenType::LESS_THAN)) {
                    RevertingTentativeParsingAction tentative(*this);
                    try {
                        DeclarationParser decl(this);
                        return static_cast<bool>(decl.parse_declaration(false));
                    } catch (const FatalErrorLimitReached&) {
                        return false;
                    } catch (const ParseError&) {
                        return false;
                    }
                }
                return false;
            }
            if (is_cxx_mode_active() &&
                (s.type == TokenType::SCOPE_RESOLUTION ||
                 (s.type == TokenType::COLON &&
                  peek_token().type == TokenType::COLON))) {
                RevertingTentativeParsingAction tentative(*this);
                try {
                    DeclarationParser decl(this);
                    return static_cast<bool>(decl.parse_declaration(false));
                } catch (const FatalErrorLimitReached&) {
                    return false;
                } catch (const ParseError&) {
                    return false;
                }
            }
            // Check for C23 [[...]] attribute syntax
            if (s.type == TokenType::LEFT_BRACKET && peek_token().type == TokenType::LEFT_BRACKET) {
                return true;
            }
            return false;
    }

}
