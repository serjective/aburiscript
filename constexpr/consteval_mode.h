#ifndef ABURI_CONSTEVAL_MODE_H
#define ABURI_CONSTEVAL_MODE_H

enum class ConstEvalModeKind {
    Unknown,
    CIntegerConstantExpression,
    CStaticInitializer,
    C23ConstexprInitializer,
    PreprocessorConditional,
    BuiltinQuery,
    CppCoreConstantExpression,
    CppNonTypeTemplateArgument,
    CppImmediateFunction
};

struct ConstEvalMode {
    ConstEvalModeKind kind = ConstEvalModeKind::Unknown;
    bool allow_side_effects = false;

    static ConstEvalMode c_ice() {
        return {ConstEvalModeKind::CIntegerConstantExpression, false};
    }

    static ConstEvalMode c_static_initializer() {
        return {ConstEvalModeKind::CStaticInitializer, false};
    }

    static ConstEvalMode c23_constexpr_initializer() {
        return {ConstEvalModeKind::C23ConstexprInitializer, false};
    }

    static ConstEvalMode preprocessor_conditional() {
        return {ConstEvalModeKind::PreprocessorConditional, false};
    }

    static ConstEvalMode builtin_query() {
        return {ConstEvalModeKind::BuiltinQuery, false};
    }

    static ConstEvalMode cpp_core_constant_expression() {
        return {ConstEvalModeKind::CppCoreConstantExpression, false};
    }

    static ConstEvalMode cpp_non_type_template_argument() {
        return {ConstEvalModeKind::CppNonTypeTemplateArgument, false};
    }

    static ConstEvalMode cpp_immediate_function() {
        return {ConstEvalModeKind::CppImmediateFunction, false};
    }
};

#endif // ABURI_CONSTEVAL_MODE_H
