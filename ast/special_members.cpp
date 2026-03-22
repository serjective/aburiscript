#include "special_members.h"

#include "symbols.h"

bool cpp_access_allows_member(RecordMemberAccess access,
                              bool allow_protected_access) {
    if (allow_protected_access) {
        return access != RecordMemberAccess::Private;
    }
    return access == RecordMemberAccess::Public;
}

CppConstructorUserParamInfo cpp_compute_constructor_user_param_info(
    const RecordSemanticState::Constructor& ctor) {
    CppConstructorUserParamInfo info;

    auto fn_type = desugar_type(ctor.type).as_shared<FunctionType>();
    if (!fn_type) {
        return info;
    }

    info.user_param_start = fn_type->parameters.empty() ? 0 : 1;
    info.max_user_param_count =
        fn_type->parameters.size() > info.user_param_start
            ? fn_type->parameters.size() - info.user_param_start
            : 0;
    if (info.max_user_param_count == 1 &&
        info.user_param_start < fn_type->parameters.size() &&
        fn_type->parameters[info.user_param_start] &&
        fn_type->parameters[info.user_param_start]->isVoid()) {
        info.max_user_param_count = 0;
    }

    info.required_user_param_count = info.max_user_param_count;
    if (ctor.symbol) {
        const auto* defaults = get_symbol_cpp_default_arguments(ctor.symbol.get());
        if (defaults) {
            size_t trailing_defaults = 0;
            for (size_t param_idx =
                     info.user_param_start + info.max_user_param_count;
                 param_idx > info.user_param_start;
                 --param_idx) {
                size_t index = param_idx - 1;
                if (index >= defaults->size() || !(*defaults)[index]) {
                    break;
                }
                ++trailing_defaults;
            }
            if (trailing_defaults > info.required_user_param_count) {
                trailing_defaults = info.required_user_param_count;
            }
            info.required_user_param_count -= trailing_defaults;
        }
    }
    return info;
}

bool cpp_constructor_is_viable_default_candidate(
    const RecordSemanticState::Constructor& ctor,
    bool allow_protected_access) {
    if (ctor.is_deleted) {
        return false;
    }
    if (!cpp_access_allows_member(ctor.declared_access, allow_protected_access)) {
        return false;
    }
    CppConstructorUserParamInfo info = cpp_compute_constructor_user_param_info(ctor);
    return info.required_user_param_count == 0;
}

bool cpp_destructor_is_viable_candidate(
    const RecordSemanticState::Destructor& dtor,
    bool allow_protected_access) {
    if (dtor.is_deleted) {
        return false;
    }
    return cpp_access_allows_member(dtor.declared_access, allow_protected_access);
}

bool cpp_record_has_viable_default_constructor(
    const RecordSemanticState* state,
    bool allow_protected_access) {
    if (!state || state->is_incomplete) {
        return false;
    }
    if (state->constructors.empty()) {
        // Records without constructor metadata are treated as
        // default-constructible in the current supported C++ subset.
        return true;
    }
    for (const auto& ctor : state->constructors) {
        if (cpp_constructor_is_viable_default_candidate(
                ctor, allow_protected_access)) {
            return true;
        }
    }
    return false;
}

bool cpp_record_has_viable_destructor(
    const RecordSemanticState* state,
    bool allow_protected_access) {
    if (!state || state->is_incomplete) {
        return false;
    }
    if (state->destructors.empty()) {
        // Records without destructor metadata are treated as having an
        // implicitly viable destructor in the current supported subset.
        return true;
    }
    for (const auto& dtor : state->destructors) {
        if (cpp_destructor_is_viable_candidate(
                dtor, allow_protected_access)) {
            return true;
        }
    }
    return false;
}

void cpp_recompute_default_constructor_traits(
    RecordSemanticState::DefinitionData& definition_data,
    const std::vector<RecordSemanticState::Constructor>& constructors) {
    definition_data.has_default_constructor = false;
    definition_data.default_constructor_is_deleted = false;
    for (const auto& ctor : constructors) {
        CppConstructorUserParamInfo info =
            cpp_compute_constructor_user_param_info(ctor);
        if (info.required_user_param_count != 0) {
            continue;
        }
        definition_data.has_default_constructor = true;
        if (ctor.is_deleted) {
            definition_data.default_constructor_is_deleted = true;
        }
    }
}
