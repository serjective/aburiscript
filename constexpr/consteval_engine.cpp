#include "consteval_engine.h"

#include "../ast/ast.h"
#include "../numeric_utils.h"
#include "eval_state.h"

#include <cmath>
#include <cstddef>
#include <limits>
#include <unordered_map>

namespace {
constexpr size_t kMaxConstEvalDepth = 512;

// ====== Type infrastructure & alignment calculations ======

struct IntShape {
    uint16_t width = 64;
    bool is_unsigned = false;
};

IntShape infer_integer_shape(QualType type) {
    IntShape shape{};
    if (!type) {
        return shape;
    }

    auto resolve_to_integer_like = [](QualType current) -> QualType {
        while (current && current->kind == TypeKind::Enum) {
            auto en = current.as<EnumType>();
            if (!en) {
                break;
            }
            auto underlying = en->semantic_underlying_type();
            if (!underlying) {
                break;
            }
            current = QualType(underlying);
        }
        return current;
    };

    QualType resolved = resolve_to_integer_like(type);
    if (!resolved || !resolved->isInteger()) {
        return shape;
    }

    int64_t width = resolved->getWidth();
    if (width <= 0) {
        width = 64;
    }
    if (width > 64) {
        width = 64;
    }
    shape.width = static_cast<uint16_t>(width);
    shape.is_unsigned = resolved->isUnsigned();
    return shape;
}

int64_t compute_type_alignment_bytes(const std::shared_ptr<CType>& type) {
    if (!type) {
        return 0;
    }
    auto canonical = desugar_type(type);
    if (!canonical) {
        return 0;
    }
    if (canonical->isVoid()) {
        return 1;
    }
    if (auto obj = std::dynamic_pointer_cast<ObjectType>(canonical)) {
        return static_cast<int64_t>(obj->getAlignment());
    }
    if (auto arr = std::dynamic_pointer_cast<ArrayType>(canonical)) {
        return compute_type_alignment_bytes(arr->element_type.get_shared());
    }
    if (auto comp = std::dynamic_pointer_cast<ComplexType>(canonical)) {
        return compute_type_alignment_bytes(comp->element_type);
    }
    if (auto enm = std::dynamic_pointer_cast<EnumType>(canonical)) {
        return compute_type_alignment_bytes(enm->semantic_underlying_type());
    }
    int64_t width = canonical->getWidthBytes();
    return width > 0 ? width : 0;
}

std::optional<int64_t> evaluate_sizeof_expr(const SizeOfExpr* sizeof_expr) {
    if (!sizeof_expr || sizeof_expr->is_runtime_sizeof) {
        return std::nullopt;
    }

    QualType target_type = sizeof_expr->getTargetType();
    if (!target_type) {
        return std::nullopt;
    }
    return target_type->getWidthBytes();
}

std::optional<int64_t> evaluate_alignof_expr(const AlignOfExpr* alignof_expr) {
    if (!alignof_expr) {
        return std::nullopt;
    }

    if (alignof_expr->expr_operand) {
        if (auto* vref = dyn_cast<VarRef>(alignof_expr->expr_operand.get())) {
            if (vref->symref) {
                if (const auto* aligned = vref->symref->sym_attrs.find(AttributeKind::ALIGNED)) {
                    if (!aligned->args.empty() &&
                        aligned->args[0].kind == AttributeArg::Kind::INTEGER &&
                        aligned->args[0].int_value > 0) {
                        return aligned->args[0].int_value;
                    }
                }
            }
        }

        QualType expr_type = alignof_expr->expr_operand->get_type();
        if (expr_type) {
            int64_t align = compute_type_alignment_bytes(expr_type.get_shared());
            if (align > 0) {
                return align;
            }
        }
    }

    if (alignof_expr->type_operand) {
        int64_t align = compute_type_alignment_bytes(alignof_expr->type_operand.get_shared());
        if (align > 0) {
            return align;
        }
    }

    return std::nullopt;
}

std::optional<int64_t> evaluate_offsetof_expr(const OffsetOfExpr* offsetof_expr) {
    if (!offsetof_expr) {
        return std::nullopt;
    }
    if (offsetof_expr->computed_offset >= 0) {
        return offsetof_expr->computed_offset;
    }
    return std::nullopt;
}

// ====== Result construction helpers ======

ConstEvalResult make_not_evaluated(ConstEvalDiagCode code, std::string message, SrcLoc loc) {
    ConstEvalResult result = ConstEvalResult::not_evaluated(std::move(message));
    result.diagnostics.push_back(ConstEvalDiagnostic::make(code, result.message, loc));
    return result;
}

ConstEvalResult make_error(ConstEvalDiagCode code, std::string message, SrcLoc loc) {
    return ConstEvalResult::error(std::move(message), code, loc);
}

ConstEvalResult make_constant_int(ConstIntValue value) {
    return ConstEvalResult::constant(ConstValue::integer(value));
}

struct InterpScopeBindings {
    std::unordered_map<const Symbol*, ConstValue> symbol_values;
    std::unordered_map<std::string, ConstValue> named_values;
};

struct InterpFrame {
    const FuncDecl* function_decl = nullptr;
    std::vector<InterpScopeBindings> scopes;
};

struct InterpreterSession {
    EvalState* state = nullptr;
    ConstEvalMode mode = ConstEvalMode::cpp_core_constant_expression();
    std::vector<InterpFrame> frames;
};

thread_local InterpreterSession* g_interpreter_session = nullptr;

class InterpreterSessionGuard {
public:
    explicit InterpreterSessionGuard(InterpreterSession* session)
        : previous_(g_interpreter_session) {
        g_interpreter_session = session;
    }

    ~InterpreterSessionGuard() {
        g_interpreter_session = previous_;
    }

private:
    InterpreterSession* previous_ = nullptr;
};

class InterpreterFrameGuard {
public:
    InterpreterFrameGuard(InterpreterSession& session, std::string function_name,
        const FuncDecl* function_decl)
        : session_(session), entered_(false) {
        if (!session_.state) {
            return;
        }
        if (!session_.state->push_frame(std::move(function_name))) {
            return;
        }
        entered_ = true;
        InterpFrame frame;
        frame.function_decl = function_decl;
        frame.scopes.emplace_back();
        session_.frames.push_back(std::move(frame));
    }

    ~InterpreterFrameGuard() {
        if (!entered_) {
            return;
        }
        if (!session_.frames.empty()) {
            session_.frames.pop_back();
        }
        if (session_.state) {
            session_.state->pop_frame();
        }
    }

    bool entered() const {
        return entered_;
    }

private:
    InterpreterSession& session_;
    bool entered_ = false;
};

// ====== Evaluation mode predicates & value classification ======

std::string describe_function_call_target(const FuncCall* call) {
    if (!call || !call->func) {
        return "<unknown>";
    }
    if (auto* var_ref = dyn_cast<VarRef>(call->func.get())) {
        if (!var_ref->get_name().empty()) {
            return var_ref->get_name();
        }
    }
    return "<indirect>";
}

bool interpreter_mode_enabled(ConstEvalMode mode) {
    return mode.kind == ConstEvalModeKind::CppCoreConstantExpression ||
           mode.kind == ConstEvalModeKind::CppImmediateFunction;
}

bool is_c23_constexpr_initializer_mode(ConstEvalMode mode) {
    return mode.kind == ConstEvalModeKind::C23ConstexprInitializer;
}

bool is_cpp_non_type_template_argument_mode(ConstEvalMode mode) {
    return mode.kind == ConstEvalModeKind::CppNonTypeTemplateArgument;
}

bool is_zero_like_constant(const ConstValue& value) {
    switch (value.kind) {
        case ConstValueKind::Integer:
            return value.int_value.cast(64, true).to_unsigned_u64() == 0;
        case ConstValueKind::Boolean:
            return !value.bool_value;
        case ConstValueKind::Floating:
            return value.float_value.value == 0.0L;
        case ConstValueKind::NullPointer:
            return true;
        default:
            return false;
    }
}

bool has_static_storage_duration(const Symbol* sym) {
    if (!sym || sym->kind != SymbolKind::VARIABLE) {
        return false;
    }
    if (sym->storage_class == StorageClass::STATIC) {
        return true;
    }
    return sym->linkage != VariableLinkage::NONE;
}

// ====== Interpreter scope management ======

void push_interpreter_scope() {
    if (!g_interpreter_session || g_interpreter_session->frames.empty()) {
        return;
    }
    g_interpreter_session->frames.back().scopes.emplace_back();
}

void pop_interpreter_scope() {
    if (!g_interpreter_session || g_interpreter_session->frames.empty()) {
        return;
    }
    auto& scopes = g_interpreter_session->frames.back().scopes;
    if (!scopes.empty()) {
        scopes.pop_back();
    }
}

InterpScopeBindings* current_interpreter_scope() {
    if (!g_interpreter_session || g_interpreter_session->frames.empty()) {
        return nullptr;
    }
    auto& scopes = g_interpreter_session->frames.back().scopes;
    if (scopes.empty()) {
        return nullptr;
    }
    return &scopes.back();
}

bool bind_interpreter_local(
    const std::shared_ptr<Symbol>& sym, const std::string& name, const ConstValue& value) {
    auto* scope = current_interpreter_scope();
    if (!scope) {
        return false;
    }
    if (sym) {
        scope->symbol_values[sym.get()] = value;
    }
    if (!name.empty()) {
        scope->named_values[name] = value;
    }
    return true;
}

bool assign_interpreter_local(const VarRef* var_ref, const ConstValue& value) {
    if (!g_interpreter_session || g_interpreter_session->frames.empty() || !var_ref) {
        return false;
    }
    auto& current_frame = g_interpreter_session->frames.back();
    for (auto scope_it = current_frame.scopes.rbegin();
         scope_it != current_frame.scopes.rend(); ++scope_it) {
        if (var_ref->symref) {
            auto sym_it = scope_it->symbol_values.find(var_ref->symref.get());
            if (sym_it != scope_it->symbol_values.end()) {
                sym_it->second = value;
                return true;
            }
        }
        if (!var_ref->get_name().empty()) {
            auto name_it = scope_it->named_values.find(var_ref->get_name());
            if (name_it != scope_it->named_values.end()) {
                name_it->second = value;
                return true;
            }
        }
    }
    return false;
}

bool lookup_interpreter_local(const VarRef* var_ref, ConstValue& value_out) {
    if (!g_interpreter_session || !var_ref) {
        return false;
    }
    for (auto frame_it = g_interpreter_session->frames.rbegin();
         frame_it != g_interpreter_session->frames.rend(); ++frame_it) {
        for (auto scope_it = frame_it->scopes.rbegin();
             scope_it != frame_it->scopes.rend(); ++scope_it) {
            if (var_ref->symref) {
                auto sym_it = scope_it->symbol_values.find(var_ref->symref.get());
                if (sym_it != scope_it->symbol_values.end()) {
                    value_out = sym_it->second;
                    return true;
                }
            }
            if (!var_ref->get_name().empty()) {
                auto name_it = scope_it->named_values.find(var_ref->get_name());
                if (name_it != scope_it->named_values.end()) {
                    value_out = name_it->second;
                    return true;
                }
            }
        }
    }
    return false;
}

// ====== Type conversion & casting ======

bool const_value_to_bool(const ConstValue& value, bool& out) {
    switch (value.kind) {
        case ConstValueKind::Integer:
            out = value.int_value.to_unsigned_u64() != 0;
            return true;
        case ConstValueKind::Boolean:
            out = value.bool_value;
            return true;
        case ConstValueKind::Floating:
            out = value.float_value.value != 0.0L;
            return true;
        case ConstValueKind::NullPointer:
            out = false;
            return true;
        case ConstValueKind::Address:
        case ConstValueKind::MemberPointer:
            out = true;
            return true;
        default:
            return false;
    }
}

bool const_value_to_int(const ConstValue& value, IntShape target_shape, ConstIntValue& out) {
    if (value.kind == ConstValueKind::Integer) {
        out = value.int_value.cast(target_shape.width, target_shape.is_unsigned);
        return true;
    }
    if (value.kind == ConstValueKind::Boolean) {
        out = target_shape.is_unsigned
            ? ConstIntValue::from_unsigned(value.bool_value ? 1u : 0u, target_shape.width)
            : ConstIntValue::from_signed(value.bool_value ? 1 : 0, target_shape.width);
        return true;
    }
    return false;
}

bool is_pointer_like_const_value(const ConstValue& value) {
    return value.kind == ConstValueKind::NullPointer ||
           value.kind == ConstValueKind::Address ||
           value.kind == ConstValueKind::MemberPointer;
}

bool try_compare_pointer_like_const_values(const ConstValue& lhs,
                                           const ConstValue& rhs,
                                           bool& equal_out) {
    if (!is_pointer_like_const_value(lhs) || !is_pointer_like_const_value(rhs)) {
        return false;
    }

    if (lhs.kind == ConstValueKind::NullPointer &&
        rhs.kind == ConstValueKind::NullPointer) {
        equal_out = true;
        return true;
    }

    if (lhs.kind == ConstValueKind::Address &&
        rhs.kind == ConstValueKind::Address) {
        equal_out =
            lhs.address_value.symbol.get() == rhs.address_value.symbol.get() &&
            lhs.address_value.byte_offset == rhs.address_value.byte_offset;
        return true;
    }

    if (lhs.kind == ConstValueKind::MemberPointer &&
        rhs.kind == ConstValueKind::MemberPointer) {
        equal_out =
            lhs.member_pointer_value.byte_offset ==
                rhs.member_pointer_value.byte_offset &&
            lhs.member_pointer_value.method_symbol.get() ==
                rhs.member_pointer_value.method_symbol.get() &&
            lhs.member_pointer_value.virtual_slot_index ==
                rhs.member_pointer_value.virtual_slot_index &&
            lhs.member_pointer_value.member_name ==
                rhs.member_pointer_value.member_name &&
            lhs.member_pointer_value.is_function_member ==
                rhs.member_pointer_value.is_function_member;
        return true;
    }

    equal_out = false;
    return true;
}

Expr* strip_noop_implicit_casts(Expr* expr) {
    while (auto* cast = dyn_cast<ImplicitCast>(expr)) {
        switch (cast->kind) {
            case ImplicitCastTypes::LVALUE_TO_RVALUE:
            case ImplicitCastTypes::ARRAY_TO_POINTER:
            case ImplicitCastTypes::RAW_CAST:
            case ImplicitCastTypes::ARITH_CAST:
                expr = cast->expr.get();
                continue;
            default:
                return expr;
        }
    }
    return expr;
}

std::optional<ConstValue> cast_const_value_to_type(
    const ConstValue& input, QualType target_type) {
    if (!target_type) {
        return input;
    }

    QualType resolved = target_type;
    if (resolved->kind == TypeKind::Enum) {
        auto enum_type = resolved.as_shared<EnumType>();
        if (enum_type) {
            auto underlying = enum_type->semantic_underlying_type();
            if (underlying) {
                resolved = underlying;
            }
        }
    }

    if (resolved->isInteger()) {
        IntShape shape = infer_integer_shape(resolved);
        ConstIntValue int_value{};
        if (!const_value_to_int(input, shape, int_value)) {
            if (input.kind == ConstValueKind::Floating) {
                long double truncated = std::trunc(input.float_value.value);
                int64_t as_i64 = static_cast<int64_t>(truncated);
                int_value = shape.is_unsigned
                    ? ConstIntValue::from_unsigned(static_cast<uint64_t>(as_i64), shape.width)
                    : ConstIntValue::from_signed(as_i64, shape.width);
            } else {
                return std::nullopt;
            }
        }
        return ConstValue::integer(int_value.cast(shape.width, shape.is_unsigned));
    }

    if (resolved->isFloatingPoint()) {
        long double value = 0.0L;
        switch (input.kind) {
            case ConstValueKind::Floating:
                value = input.float_value.value;
                break;
            case ConstValueKind::Integer:
                value = input.int_value.is_unsigned
                    ? static_cast<long double>(input.int_value.to_unsigned_u64())
                    : static_cast<long double>(input.int_value.to_signed_i64());
                break;
            case ConstValueKind::Boolean:
                value = input.bool_value ? 1.0L : 0.0L;
                break;
            default:
                return std::nullopt;
        }

        uint16_t width = 64;
        int64_t target_width = resolved->getWidth();
        if (target_width > 0 && target_width <= std::numeric_limits<uint16_t>::max()) {
            width = static_cast<uint16_t>(target_width);
        }
        return ConstValue::floating(value, width);
    }

    if (resolved->kind == TypeKind::Pointer ||
        resolved->kind == TypeKind::MemberPointer ||
        (resolved->kind == TypeKind::Builtin &&
         static_cast<const BuiltinType*>(resolved.get_shared().get())->builtin_kind ==
             BuiltinTypes::NullPtr)) {
        switch (input.kind) {
            case ConstValueKind::NullPointer:
                return ConstValue::null_pointer();
            case ConstValueKind::Address:
                if (resolved->kind == TypeKind::Pointer) {
                    return std::optional<ConstValue>(input);
                }
                return std::nullopt;
            case ConstValueKind::MemberPointer:
                if (resolved->kind == TypeKind::MemberPointer) {
                    return std::optional<ConstValue>(input);
                }
                return std::nullopt;
            default:
                break;
        }
    }

    if (resolved->kind == TypeKind::Object &&
        input.kind == ConstValueKind::Object &&
        input.object_value &&
        input.object_value->kind == ConstObjectValueKind::Record) {
        return input;
    }
    if (resolved->kind == TypeKind::Array &&
        input.kind == ConstValueKind::Object &&
        input.object_value &&
        input.object_value->kind == ConstObjectValueKind::Array) {
        return input;
    }

    return std::nullopt;
}

std::optional<ConstValue> default_const_value_for_type(QualType type) {
    if (!type) {
        return std::nullopt;
    }
    if (type->kind == TypeKind::Enum) {
        auto enum_type = type.as_shared<EnumType>();
        if (enum_type) {
            auto underlying = enum_type->semantic_underlying_type();
            if (underlying) {
                type = underlying;
            }
        }
    }
    if (type->isInteger()) {
        IntShape shape = infer_integer_shape(type);
        return ConstValue::integer(shape.is_unsigned
            ? ConstIntValue::from_unsigned(0, shape.width)
            : ConstIntValue::from_signed(0, shape.width));
    }
    if (type->isFloatingPoint()) {
        uint16_t width = 64;
        int64_t type_width = type->getWidth();
        if (type_width > 0 && type_width <= std::numeric_limits<uint16_t>::max()) {
            width = static_cast<uint16_t>(type_width);
        }
        return ConstValue::floating(0.0L, width);
    }
    if (type->kind == TypeKind::Pointer ||
        type->kind == TypeKind::MemberPointer ||
        (type->kind == TypeKind::Builtin &&
         static_cast<const BuiltinType*>(type.get_shared().get())->builtin_kind ==
             BuiltinTypes::NullPtr)) {
        return ConstValue::null_pointer();
    }
    if (type->kind == TypeKind::Array) {
        auto array = type.as_shared<ArrayType>();
        if (!array || array->size_kind != ArraySizeKind::Constant ||
            !array->size.has_value()) {
            return std::nullopt;
        }
        std::vector<ConstValue> elements;
        elements.reserve(*array->size);
        for (size_t idx = 0; idx < *array->size; ++idx) {
            auto element = default_const_value_for_type(array->element_type);
            if (!element.has_value()) {
                return std::nullopt;
            }
            elements.push_back(*element);
        }
        return ConstValue::object(ConstObjectValueKind::Array, std::move(elements));
    }
    if (type->kind == TypeKind::Object) {
        auto object = type.as_shared<ObjectType>();
        if (!object || object->isIncomplete()) {
            return std::nullopt;
        }
        std::vector<ConstValue> fields;
        const auto& semantic_fields = object->semantic_fields();
        fields.reserve(semantic_fields.size());
        for (const auto& field : semantic_fields) {
            auto field_value = default_const_value_for_type(field.type);
            if (!field_value.has_value()) {
                return std::nullopt;
            }
            fields.push_back(*field_value);
        }
        return ConstValue::object(ConstObjectValueKind::Record, std::move(fields));
    }
    return std::nullopt;
}

// ====== Typed expression evaluation & initialization ======

ConstEvalResult eval_expr(Expr* expr, ConstEvalMode mode, size_t depth);

ConstEvalResult eval_expr_as_typed_const_value(Expr* expr,
                                               QualType target_type,
                                               ConstEvalMode mode,
                                               size_t depth);

ConstEvalResult eval_init_list_as_typed_const_value(InitListExpr* init_list,
                                                    QualType target_type,
                                                    ConstEvalMode mode,
                                                    size_t depth) {
    if (!init_list || !target_type) {
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "aggregate initializer is missing a target type",
            init_list ? init_list->location : SrcLoc());
    }

    target_type = desugar_type(target_type);
    if (target_type->kind == TypeKind::Array) {
        auto array = target_type.as_shared<ArrayType>();
        if (!array || array->size_kind != ArraySizeKind::Constant ||
            !array->size.has_value()) {
            return make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "non-type template argument array initializer requires a constant bound",
                init_list->location);
        }

        std::vector<ConstValue> elements;
        elements.reserve(*array->size);
        for (size_t idx = 0; idx < *array->size; ++idx) {
            auto mapping = init_list->mappings.find(idx);
            if (mapping == init_list->mappings.end()) {
                auto default_value =
                    default_const_value_for_type(array->element_type);
                if (!default_value.has_value()) {
                    return make_not_evaluated(
                        ConstEvalDiagCode::UnsupportedExpression,
                        "array element type is not supported in class-type non-type template arguments",
                        init_list->location);
                }
                elements.push_back(*default_value);
                continue;
            }

            ConstEvalResult element =
                eval_expr_as_typed_const_value(
                    mapping->second.get(),
                    array->element_type,
                    mode,
                    depth + 1);
            if (element.status != ConstEvalStatus::Constant ||
                !element.value.has_value()) {
                return element;
            }
            elements.push_back(*element.value);
        }
        return ConstEvalResult::constant(
            ConstValue::object(ConstObjectValueKind::Array, std::move(elements)));
    }

    if (target_type->kind != TypeKind::Object) {
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "aggregate initializer target is not a supported structural object type",
            init_list->location);
    }

    auto object = target_type.as_shared<ObjectType>();
    if (!object || object->is_union || object->isIncomplete()) {
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "class-type non-type template argument requires a complete non-union structural type",
            init_list->location);
    }

    std::vector<ConstValue> fields;
    const auto& semantic_fields = object->semantic_fields();
    fields.reserve(semantic_fields.size());
    for (size_t idx = 0; idx < semantic_fields.size(); ++idx) {
        const auto& field = semantic_fields[idx];
        auto mapping = init_list->mappings.find(idx);
        if (mapping == init_list->mappings.end()) {
            auto default_value = default_const_value_for_type(field.type);
            if (!default_value.has_value()) {
                return make_not_evaluated(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "class-type non-type template argument field is not supported in zero-initialization",
                    init_list->location);
            }
            fields.push_back(*default_value);
            continue;
        }

        ConstEvalResult field_value =
            eval_expr_as_typed_const_value(
                mapping->second.get(),
                field.type,
                mode,
                depth + 1);
        if (field_value.status != ConstEvalStatus::Constant ||
            !field_value.value.has_value()) {
            return field_value;
        }
        fields.push_back(*field_value.value);
    }
    return ConstEvalResult::constant(
        ConstValue::object(ConstObjectValueKind::Record, std::move(fields)));
}

ConstEvalResult eval_expr_as_typed_const_value(Expr* expr,
                                               QualType target_type,
                                               ConstEvalMode mode,
                                               size_t depth) {
    if (!expr || !target_type) {
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "typed constant evaluation requires an expression and target type",
            expr ? expr->location : SrcLoc());
    }

    target_type = desugar_type(target_type);
    Expr* stripped = strip_noop_implicit_casts(expr);
    if ((target_type->kind == TypeKind::Object ||
         target_type->kind == TypeKind::Array) &&
        dyn_cast<InitListExpr>(stripped)) {
        return eval_init_list_as_typed_const_value(
            static_cast<InitListExpr*>(stripped),
            target_type,
            mode,
            depth + 1);
    }

    ConstEvalResult inner = eval_expr(expr, mode, depth + 1);
    if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
        return inner;
    }
    auto casted = cast_const_value_to_type(*inner.value, target_type);
    if (!casted.has_value()) {
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "expression is not convertible to the structural constant target type",
            expr->location);
    }
    return ConstEvalResult::constant(*casted);
}

ConstEvalResult eval_local_constexpr_variable_initializer(
    const Symbol* sym,
    ConstEvalMode mode,
    size_t depth) {
    if (!sym || sym->kind != SymbolKind::VARIABLE || !sym->is_constexpr ||
        has_static_storage_duration(sym) || !sym->variable_definition ||
        !sym->variable_definition->init) {
        return ConstEvalResult::not_evaluated();
    }

    QualType target_type = sym->variable_definition->type
        ? sym->variable_definition->type
        : sym->type;
    if (!target_type) {
        return ConstEvalResult::not_evaluated();
    }

    return eval_expr_as_typed_const_value(
        sym->variable_definition->init.get(),
        target_type,
        mode,
        depth + 1);
}

struct InterpExecResult {
    enum class Kind {
        Continue,
        Return,
        Fail
    };

    Kind kind = Kind::Continue;
    ConstEvalResult value = ConstEvalResult::not_evaluated();
};

// ====== Interpreter execution infrastructure ======

QualType extract_function_return_type(const FuncDecl* function_decl) {
    if (!function_decl || !function_decl->type) {
        return nullptr;
    }
    auto function_type = std::dynamic_pointer_cast<FunctionType>(function_decl->type);
    if (!function_type) {
        return nullptr;
    }
    return function_type->ret_type;
}

bool is_void_parameter_sentinel(const ParamDecl* param_decl) {
    return param_decl && param_decl->type && param_decl->type->isVoid() &&
           !param_decl->has_name();
}

InterpExecResult make_interp_continue_result() {
    return InterpExecResult{};
}

InterpExecResult make_interp_fail_result(ConstEvalResult result) {
    InterpExecResult exec_result;
    exec_result.kind = InterpExecResult::Kind::Fail;
    exec_result.value = std::move(result);
    return exec_result;
}

InterpExecResult make_interp_return_result(ConstEvalResult result) {
    InterpExecResult exec_result;
    exec_result.kind = InterpExecResult::Kind::Return;
    exec_result.value = std::move(result);
    return exec_result;
}

InterpExecResult eval_interpreter_stmt(Stmt* stmt, ConstEvalMode mode, size_t depth);
ConstEvalResult eval_function_call_expr(FuncCall* call, ConstEvalMode mode, size_t depth);

ConstEvalResult eval_expr(Expr* expr, ConstEvalMode mode, size_t depth);
bool is_c23_integer_constant_expr(Expr* expr, ConstEvalMode mode, size_t depth);
bool is_c23_address_constant_expr(Expr* expr, ConstEvalMode mode, size_t depth);

// ====== Constant expression classification (C23) ======

bool is_c23_address_constant_operand(Expr* expr, ConstEvalMode mode, size_t depth) {
    if (!expr || depth > kMaxConstEvalDepth) {
        return false;
    }

    Expr* core = strip_noop_implicit_casts(expr);
    if (!core) {
        return false;
    }

    if (isa<StringLiteral>(core)) {
        return true;
    }

    if (auto* var_ref = dyn_cast<VarRef>(core)) {
        if (!var_ref->symref) {
            return false;
        }
        if (var_ref->symref->kind == SymbolKind::FUNCTION) {
            return true;
        }
        return has_static_storage_duration(var_ref->symref.get());
    }

    if (auto* member_expr = dyn_cast<MemberExpr>(core)) {
        if (member_expr->isArrow) {
            return false;
        }
        return is_c23_address_constant_operand(member_expr->base.get(), mode, depth + 1);
    }

    if (auto* subscript_expr = dyn_cast<ArraySubscriptExpr>(core)) {
        if (!subscript_expr->array || !subscript_expr->index) {
            return false;
        }
        ConstEvalResult index_eval = eval_expr(subscript_expr->index.get(), mode, depth + 1);
        if (index_eval.status != ConstEvalStatus::Constant || !index_eval.value.has_value()) {
            return false;
        }

        ConstEvalResult array_eval = eval_expr(subscript_expr->array.get(), mode, depth + 1);
        return array_eval.status == ConstEvalStatus::Constant &&
               array_eval.value.has_value();
    }

    return false;
}

bool is_c23_integer_constant_expr(Expr* expr, ConstEvalMode mode, size_t depth) {
    if (!expr || depth > kMaxConstEvalDepth) {
        return false;
    }

    ConstEvalResult eval = eval_expr(expr, mode, depth + 1);
    if (eval.status != ConstEvalStatus::Constant || !eval.value.has_value()) {
        return false;
    }

    IntShape shape = infer_integer_shape(expr->get_type());
    ConstIntValue value{};
    return const_value_to_int(eval.value.value(), shape, value);
}

bool is_c23_address_constant_expr(Expr* expr, ConstEvalMode mode, size_t depth) {
    if (!expr || depth > kMaxConstEvalDepth) {
        return false;
    }

    Expr* core = strip_noop_implicit_casts(expr);
    if (!core) {
        return false;
    }

    if (auto* unary = dyn_cast<UnaryOperation>(core)) {
        if (unary->uop == UnaryOpTypes::ADDRESS_OF) {
            return is_c23_address_constant_operand(unary->exp.get(), mode, depth + 1);
        }
    }

    if (isa<StringLiteral>(core)) {
        return true;
    }

    if (auto* var_ref = dyn_cast<VarRef>(core)) {
        if (!var_ref->symref) {
            return false;
        }
        if (var_ref->symref->kind == SymbolKind::FUNCTION) {
            return true;
        }
        return var_ref->symref->kind == SymbolKind::VARIABLE &&
               var_ref->get_type() &&
               var_ref->get_type()->kind == TypeKind::Array &&
               has_static_storage_duration(var_ref->symref.get());
    }

    if (auto* binary = dyn_cast<BinaryOperation>(core)) {
        if ((binary->bop == BinOpTypes::ADD || binary->bop == BinOpTypes::SUB) &&
            binary->get_type() && binary->get_type()->kind == TypeKind::Pointer) {
            if (is_c23_address_constant_expr(binary->left.get(), mode, depth + 1) &&
                is_c23_integer_constant_expr(binary->right.get(), mode, depth + 1)) {
                return true;
            }
            if (binary->bop == BinOpTypes::ADD &&
                is_c23_address_constant_expr(binary->right.get(), mode, depth + 1) &&
                is_c23_integer_constant_expr(binary->left.get(), mode, depth + 1)) {
                return true;
            }
        }
    }

    return false;
}

// ====== Unary, binary, and cast operator evaluation ======

ConstEvalResult eval_unary_expr(UnaryOperation* unary, ConstEvalMode mode, size_t depth) {
    if (!unary || !unary->exp) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "unsupported unary expression", unary ? unary->location : SrcLoc());
    }

    if (is_c23_constexpr_initializer_mode(mode) &&
        unary->uop == UnaryOpTypes::ADDRESS_OF) {
        if (is_c23_address_constant_operand(unary->exp.get(), mode, depth + 1)) {
            return ConstEvalResult::constant(ConstValue::boolean(true));
        }
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "address-of expression is not allowed in C23 constexpr initializer",
            unary->location);
    }

    if (is_cpp_non_type_template_argument_mode(mode) &&
        unary->uop == UnaryOpTypes::ADDRESS_OF) {
        Expr* core = strip_noop_implicit_casts(unary->exp.get());
        if (auto* var_ref = dyn_cast<VarRef>(core)) {
            if (!var_ref->symref) {
                return make_not_evaluated(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "address-of expression does not name a bound entity",
                    unary->location);
            }
            if (var_ref->symref->kind == SymbolKind::FUNCTION ||
                has_static_storage_duration(var_ref->symref.get())) {
                return ConstEvalResult::constant(
                    ConstValue::address(var_ref->symref));
            }
        }
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "address-of expression is not a supported non-type template argument",
            unary->location);
    }

    ConstEvalResult inner = eval_expr(unary->exp.get(), mode, depth + 1);
    if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
        return inner;
    }

    if (unary->uop == UnaryOpTypes::LOGICAL_NOT) {
        bool truthy = false;
        if (!const_value_to_bool(inner.value.value(), truthy)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "logical not requires scalar constant operand", unary->location);
        }
        return make_constant_int(ConstIntValue::from_signed(truthy ? 0 : 1, 32));
    }

    IntShape result_shape = infer_integer_shape(unary->get_type());
    ConstIntValue inner_int{};
    if (!const_value_to_int(inner.value.value(), result_shape, inner_int)) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "unary constant evaluation currently supports integer-like operands",
            unary->location);
    }

    switch (unary->uop) {
        case UnaryOpTypes::NEG:
            if (result_shape.is_unsigned) {
                return make_constant_int(ConstIntValue::from_unsigned(
                    uint64_t(0) - inner_int.to_unsigned_u64(), result_shape.width));
            }
            return make_constant_int(ConstIntValue::from_signed(
                -inner_int.to_signed_i64(), result_shape.width));
        case UnaryOpTypes::POSITIVE:
            return make_constant_int(inner_int);
        case UnaryOpTypes::BITWISE_NOT:
            return make_constant_int(ConstIntValue::from_unsigned(
                ~inner_int.to_unsigned_u64(), result_shape.width).cast(
                result_shape.width, result_shape.is_unsigned));
        default:
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "unary operator not supported by consteval engine yet", unary->location);
    }
}

ConstEvalResult eval_binary_expr(BinaryOperation* bin, ConstEvalMode mode, size_t depth) {
    if (!bin || !bin->left || !bin->right) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "unsupported binary expression", bin ? bin->location : SrcLoc());
    }

    if (bin->bop == BinOpTypes::COMMA) {
        ConstEvalResult lhs_res = eval_expr(bin->left.get(), mode, depth + 1);
        if (lhs_res.status != ConstEvalStatus::Constant || !lhs_res.value.has_value()) {
            return lhs_res;
        }
        return eval_expr(bin->right.get(), mode, depth + 1);
    }

    if (bin->bop == BinOpTypes::ASSIGN && g_interpreter_session) {
        Expr* lhs_core = strip_noop_implicit_casts(bin->left.get());
        auto* lhs_var = dyn_cast<VarRef>(lhs_core);
        if (!lhs_var) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "interpreter assignment currently supports variable targets only",
                bin->location);
        }

        ConstEvalResult rhs_res = eval_expr(bin->right.get(), mode, depth + 1);
        if (rhs_res.status != ConstEvalStatus::Constant || !rhs_res.value.has_value()) {
            return rhs_res;
        }

        auto casted = cast_const_value_to_type(rhs_res.value.value(), lhs_var->get_type());
        if (!casted.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "unable to assign expression to variable type in constexpr interpreter",
                bin->location);
        }

        if (!assign_interpreter_local(lhs_var, casted.value())) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "assignment target is not available in current constexpr interpreter scope",
                bin->location);
        }

        return ConstEvalResult::constant(casted.value());
    }

    if (is_c23_constexpr_initializer_mode(mode) &&
        bin->get_type() &&
        bin->get_type()->kind == TypeKind::Pointer &&
        (bin->bop == BinOpTypes::ADD || bin->bop == BinOpTypes::SUB)) {
        if (is_c23_address_constant_expr(bin->left.get(), mode, depth + 1) &&
            is_c23_integer_constant_expr(bin->right.get(), mode, depth + 1)) {
            return ConstEvalResult::constant(ConstValue::boolean(true));
        }
        if (bin->bop == BinOpTypes::ADD &&
            is_c23_address_constant_expr(bin->right.get(), mode, depth + 1) &&
            is_c23_integer_constant_expr(bin->left.get(), mode, depth + 1)) {
            return ConstEvalResult::constant(ConstValue::boolean(true));
        }
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "pointer arithmetic expression is not allowed in C23 constexpr initializer",
            bin->location);
    }

    IntShape operand_shape = infer_integer_shape(bin->left->get_type());
    if (operand_shape.width == 64 && !operand_shape.is_unsigned) {
        IntShape result_shape = infer_integer_shape(bin->get_type());
        if (result_shape.width != 64 || result_shape.is_unsigned) {
            operand_shape = result_shape;
        }
    }

    if (bin->bop == BinOpTypes::LOGICAL_AND || bin->bop == BinOpTypes::LOGICAL_OR) {
        ConstEvalResult lhs_res = eval_expr(bin->left.get(), mode, depth + 1);
        if (lhs_res.status != ConstEvalStatus::Constant || !lhs_res.value.has_value()) {
            return lhs_res;
        }
        bool lhs_truthy = false;
        if (!const_value_to_bool(lhs_res.value.value(), lhs_truthy)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "logical operation requires scalar constant operands", bin->location);
        }

        if (bin->bop == BinOpTypes::LOGICAL_AND && !lhs_truthy) {
            return make_constant_int(ConstIntValue::from_signed(0, 32));
        }
        if (bin->bop == BinOpTypes::LOGICAL_OR && lhs_truthy) {
            return make_constant_int(ConstIntValue::from_signed(1, 32));
        }

        ConstEvalResult rhs_res = eval_expr(bin->right.get(), mode, depth + 1);
        if (rhs_res.status != ConstEvalStatus::Constant || !rhs_res.value.has_value()) {
            return rhs_res;
        }
        bool rhs_truthy = false;
        if (!const_value_to_bool(rhs_res.value.value(), rhs_truthy)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "logical operation requires scalar constant operands", bin->location);
        }
        bool result = (bin->bop == BinOpTypes::LOGICAL_AND) ? (lhs_truthy && rhs_truthy)
                                                             : (lhs_truthy || rhs_truthy);
        return make_constant_int(ConstIntValue::from_signed(result ? 1 : 0, 32));
    }

    ConstEvalResult lhs_res = eval_expr(bin->left.get(), mode, depth + 1);
    if (lhs_res.status != ConstEvalStatus::Constant || !lhs_res.value.has_value()) {
        return lhs_res;
    }
    ConstEvalResult rhs_res = eval_expr(bin->right.get(), mode, depth + 1);
    if (rhs_res.status != ConstEvalStatus::Constant || !rhs_res.value.has_value()) {
        return rhs_res;
    }

    if (bin->bop == BinOpTypes::EQUAL || bin->bop == BinOpTypes::NOT_EQUAL) {
        bool pointer_like_equal = false;
        if (try_compare_pointer_like_const_values(
                lhs_res.value.value(),
                rhs_res.value.value(),
                pointer_like_equal)) {
            bool result =
                (bin->bop == BinOpTypes::EQUAL) ? pointer_like_equal
                                                : !pointer_like_equal;
            return make_constant_int(ConstIntValue::from_signed(result ? 1 : 0, 32));
        }
    }

    ConstIntValue lhs_int{};
    ConstIntValue rhs_int{};
    if (!const_value_to_int(lhs_res.value.value(), operand_shape, lhs_int) ||
        !const_value_to_int(rhs_res.value.value(), operand_shape, rhs_int)) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "binary constant evaluation currently supports integer-like operands",
            bin->location);
    }

    auto make_cmp_result = [&](bool v) {
        return make_constant_int(ConstIntValue::from_signed(v ? 1 : 0, 32));
    };

    switch (bin->bop) {
        case BinOpTypes::ADD:
            if (operand_shape.is_unsigned) {
                return make_constant_int(ConstIntValue::from_unsigned(
                    lhs_int.to_unsigned_u64() + rhs_int.to_unsigned_u64(), operand_shape.width));
            }
            return make_constant_int(ConstIntValue::from_signed(
                lhs_int.to_signed_i64() + rhs_int.to_signed_i64(), operand_shape.width));
        case BinOpTypes::SUB:
            if (operand_shape.is_unsigned) {
                return make_constant_int(ConstIntValue::from_unsigned(
                    lhs_int.to_unsigned_u64() - rhs_int.to_unsigned_u64(), operand_shape.width));
            }
            return make_constant_int(ConstIntValue::from_signed(
                lhs_int.to_signed_i64() - rhs_int.to_signed_i64(), operand_shape.width));
        case BinOpTypes::MULT:
            if (operand_shape.is_unsigned) {
                return make_constant_int(ConstIntValue::from_unsigned(
                    lhs_int.to_unsigned_u64() * rhs_int.to_unsigned_u64(), operand_shape.width));
            }
            return make_constant_int(ConstIntValue::from_signed(
                lhs_int.to_signed_i64() * rhs_int.to_signed_i64(), operand_shape.width));
        case BinOpTypes::DIV: {
            auto div_res = const_int_div(lhs_int, rhs_int);
            if (!div_res.value.has_value()) {
                return make_error(ConstEvalDiagCode::DivisionByZero,
                    "division by zero in constant expression", bin->location);
            }
            return make_constant_int(div_res.value.value());
        }
        case BinOpTypes::MOD: {
            auto mod_res = const_int_mod(lhs_int, rhs_int);
            if (!mod_res.value.has_value()) {
                return make_error(ConstEvalDiagCode::DivisionByZero,
                    "modulo by zero in constant expression", bin->location);
            }
            return make_constant_int(mod_res.value.value());
        }
        case BinOpTypes::BITWISE_AND:
            return make_constant_int(ConstIntValue::from_unsigned(
                lhs_int.to_unsigned_u64() & rhs_int.to_unsigned_u64(), operand_shape.width)
                .cast(operand_shape.width, operand_shape.is_unsigned));
        case BinOpTypes::BITWISE_OR:
            return make_constant_int(ConstIntValue::from_unsigned(
                lhs_int.to_unsigned_u64() | rhs_int.to_unsigned_u64(), operand_shape.width)
                .cast(operand_shape.width, operand_shape.is_unsigned));
        case BinOpTypes::BITWISE_XOR:
            return make_constant_int(ConstIntValue::from_unsigned(
                lhs_int.to_unsigned_u64() ^ rhs_int.to_unsigned_u64(), operand_shape.width)
                .cast(operand_shape.width, operand_shape.is_unsigned));
        case BinOpTypes::SHIFT_LEFT: {
            auto shl_res = const_int_shl(lhs_int, rhs_int);
            if (!shl_res.value.has_value()) {
                return make_error(ConstEvalDiagCode::InvalidShiftAmount,
                    "invalid left-shift amount in constant expression", bin->location);
            }
            return make_constant_int(shl_res.value.value());
        }
        case BinOpTypes::SHIFT_RIGHT: {
            uint64_t shift = rhs_int.to_unsigned_u64();
            if (shift >= lhs_int.bit_width) {
                return make_error(ConstEvalDiagCode::InvalidShiftAmount,
                    "invalid right-shift amount in constant expression", bin->location);
            }
            if (lhs_int.is_unsigned) {
                return make_constant_int(ConstIntValue::from_unsigned(
                    lhs_int.to_unsigned_u64() >> shift, lhs_int.bit_width));
            }
            return make_constant_int(ConstIntValue::from_signed(
                lhs_int.to_signed_i64() >> shift, lhs_int.bit_width));
        }
        case BinOpTypes::LESS_EQUAL_THAN:
            if (operand_shape.is_unsigned) {
                return make_cmp_result(lhs_int.to_unsigned_u64() <= rhs_int.to_unsigned_u64());
            }
            return make_cmp_result(lhs_int.to_signed_i64() <= rhs_int.to_signed_i64());
        case BinOpTypes::LESS_THAN:
            if (operand_shape.is_unsigned) {
                return make_cmp_result(lhs_int.to_unsigned_u64() < rhs_int.to_unsigned_u64());
            }
            return make_cmp_result(lhs_int.to_signed_i64() < rhs_int.to_signed_i64());
        case BinOpTypes::GREATER_EQUAL_THAN:
            if (operand_shape.is_unsigned) {
                return make_cmp_result(lhs_int.to_unsigned_u64() >= rhs_int.to_unsigned_u64());
            }
            return make_cmp_result(lhs_int.to_signed_i64() >= rhs_int.to_signed_i64());
        case BinOpTypes::GREATER_THAN:
            if (operand_shape.is_unsigned) {
                return make_cmp_result(lhs_int.to_unsigned_u64() > rhs_int.to_unsigned_u64());
            }
            return make_cmp_result(lhs_int.to_signed_i64() > rhs_int.to_signed_i64());
        case BinOpTypes::EQUAL:
            return make_cmp_result(lhs_int.to_unsigned_u64() == rhs_int.to_unsigned_u64());
        case BinOpTypes::NOT_EQUAL:
            return make_cmp_result(lhs_int.to_unsigned_u64() != rhs_int.to_unsigned_u64());
        default:
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "binary operator not supported by consteval engine yet", bin->location);
    }
}

ConstEvalResult eval_cast_expr(Expr* operand, QualType target_type,
    SrcLoc loc, ConstEvalMode mode, size_t depth, bool allow_float_to_int) {
    if (!operand) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "cast expression missing operand", loc);
    }
    if (is_c23_constexpr_initializer_mode(mode) &&
        target_type &&
        target_type->kind == TypeKind::Pointer) {
        if (is_c23_address_constant_expr(operand, mode, depth + 1)) {
            return ConstEvalResult::constant(ConstValue::boolean(true));
        }
        ConstEvalResult inner = eval_expr(operand, mode, depth + 1);
        if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
            return inner;
        }
        if (!is_zero_like_constant(inner.value.value())) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "pointer cast operand is not a null pointer constant", loc);
        }
        return ConstEvalResult::constant(ConstValue::boolean(true));
    }
    if (is_cpp_non_type_template_argument_mode(mode) && target_type) {
        ConstEvalResult inner = eval_expr(operand, mode, depth + 1);
        if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
            return inner;
        }
        if (target_type->kind == TypeKind::Pointer ||
            target_type->kind == TypeKind::MemberPointer ||
            (target_type->kind == TypeKind::Builtin &&
             static_cast<const BuiltinType*>(target_type.get_shared().get())
                     ->builtin_kind == BuiltinTypes::NullPtr)) {
            if (inner.value->kind == ConstValueKind::Address &&
                target_type->kind == TypeKind::Pointer) {
                return inner;
            }
            if (inner.value->kind == ConstValueKind::MemberPointer &&
                target_type->kind == TypeKind::MemberPointer) {
                return inner;
            }
            if (is_zero_like_constant(inner.value.value()) ||
                inner.value->kind == ConstValueKind::NullPointer) {
                return ConstEvalResult::constant(ConstValue::null_pointer());
            }
            return make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "pointer cast operand is not a supported non-type template argument constant",
                loc);
        }
    }
    if (target_type &&
        (target_type->kind == TypeKind::Pointer ||
         target_type->kind == TypeKind::MemberPointer ||
         is_nullptr_type(target_type))) {
        ConstEvalResult inner = eval_expr(operand, mode, depth + 1);
        if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
            return inner;
        }
        if (inner.value->kind == ConstValueKind::Address &&
            target_type->kind == TypeKind::Pointer) {
            return inner;
        }
        if (inner.value->kind == ConstValueKind::MemberPointer &&
            target_type->kind == TypeKind::MemberPointer) {
            return inner;
        }
        if (inner.value->kind == ConstValueKind::NullPointer ||
            is_zero_like_constant(inner.value.value())) {
            return ConstEvalResult::constant(ConstValue::null_pointer());
        }
        return make_not_evaluated(
            ConstEvalDiagCode::UnsupportedExpression,
            "pointer cast operand is not a null pointer constant",
            loc);
    }
    if (!target_type || !target_type->isInteger()) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "cast target type is not supported by consteval engine yet", loc);
    }

    ConstEvalResult inner = eval_expr(operand, mode, depth + 1);
    if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
        return inner;
    }

    IntShape shape = infer_integer_shape(target_type);
    ConstIntValue casted{};
    if (allow_float_to_int && inner.value->kind == ConstValueKind::Floating) {
        long double fv = inner.value->float_value.value;
        if (!std::isfinite(fv)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "cast operand is not an integer-like constant", loc);
        }
        long double truncated = std::trunc(fv);
        if (truncated < static_cast<long double>(std::numeric_limits<int64_t>::min()) ||
            truncated > static_cast<long double>(std::numeric_limits<int64_t>::max())) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "cast operand is not an integer-like constant", loc);
        }
        int64_t as_i64 = static_cast<int64_t>(truncated);
        casted = shape.is_unsigned
            ? ConstIntValue::from_unsigned(static_cast<uint64_t>(as_i64), shape.width)
            : ConstIntValue::from_signed(as_i64, shape.width);
        return make_constant_int(casted);
    }

    if (!const_value_to_int(inner.value.value(), shape, casted)) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "cast operand is not an integer-like constant", loc);
    }
    return make_constant_int(casted);
}

// ====== Interpreter statement execution ======

InterpExecResult eval_interpreter_stmt(Stmt* stmt, ConstEvalMode mode, size_t depth) {
    if (!stmt) {
        return make_interp_continue_result();
    }
    if (depth > kMaxConstEvalDepth) {
        return make_interp_fail_result(make_error(ConstEvalDiagCode::RecursionLimitExceeded,
            "constexpr recursion depth exceeded", stmt->location));
    }
    if (!g_interpreter_session || !g_interpreter_session->state) {
        return make_interp_fail_result(make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr interpreter session is unavailable", stmt->location));
    }
    if (!g_interpreter_session->state->consume_step()) {
        return make_interp_fail_result(make_error(ConstEvalDiagCode::StepLimitExceeded,
            "constexpr function interpreter step limit exceeded", stmt->location));
    }

    if (auto* compound_stmt = dyn_cast<CompoundStmt>(stmt)) {
        push_interpreter_scope();
        for (const auto& child : compound_stmt->statements) {
            InterpExecResult child_result = eval_interpreter_stmt(child.get(), mode, depth + 1);
            if (child_result.kind != InterpExecResult::Kind::Continue) {
                pop_interpreter_scope();
                return child_result;
            }
        }
        pop_interpreter_scope();
        return make_interp_continue_result();
    }

    if (auto* decl_stmt = dyn_cast<Decl2Stmt>(stmt)) {
        for (const auto& decl : decl_stmt->decls) {
            if (!decl) {
                continue;
            }
            if (isa<NopDecl>(decl.get()) || isa<TypedefDecl>(decl.get())) {
                continue;
            }
            auto* variable_decl = dyn_cast<VariableDecl>(decl.get());
            if (!variable_decl) {
                return make_interp_fail_result(make_not_evaluated(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constexpr interpreter declaration support is currently limited to local variables",
                    decl->location));
            }

            std::optional<ConstValue> initial_value;
            if (variable_decl->init) {
                ConstEvalResult init_result = eval_expr(variable_decl->init.get(), mode, depth + 1);
                if (init_result.status != ConstEvalStatus::Constant || !init_result.value.has_value()) {
                    return make_interp_fail_result(std::move(init_result));
                }
                initial_value = init_result.value.value();
            } else {
                initial_value = default_const_value_for_type(variable_decl->type);
            }
            if (!initial_value.has_value()) {
                return make_interp_fail_result(make_not_evaluated(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constexpr interpreter could not initialize local variable",
                    variable_decl->location));
            }

            auto casted = cast_const_value_to_type(initial_value.value(), variable_decl->type);
            if (!casted.has_value()) {
                return make_interp_fail_result(make_not_evaluated(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constexpr interpreter local initialization cast failed",
                    variable_decl->location));
            }

            if (!bind_interpreter_local(variable_decl->sym, variable_decl->name, casted.value())) {
                return make_interp_fail_result(make_not_evaluated(
                    ConstEvalDiagCode::UnsupportedExpression,
                    "constexpr interpreter failed to bind local variable",
                    variable_decl->location));
            }
        }
        return make_interp_continue_result();
    }

    if (auto* if_stmt = dyn_cast<IfStmt>(stmt)) {
        if (!if_stmt->condition) {
            return make_interp_fail_result(make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "if statement has no condition", if_stmt->location));
        }

        ConstEvalResult cond_result = eval_expr(if_stmt->condition.get(), mode, depth + 1);
        if (cond_result.status != ConstEvalStatus::Constant || !cond_result.value.has_value()) {
            return make_interp_fail_result(std::move(cond_result));
        }

        bool condition_truthy = false;
        if (!const_value_to_bool(cond_result.value.value(), condition_truthy)) {
            return make_interp_fail_result(make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "if condition must be scalar in constexpr interpreter",
                if_stmt->condition->location));
        }

        if (condition_truthy) {
            return eval_interpreter_stmt(if_stmt->then_stmt.get(), mode, depth + 1);
        }
        if (if_stmt->else_stmt) {
            return eval_interpreter_stmt(if_stmt->else_stmt.get(), mode, depth + 1);
        }
        return make_interp_continue_result();
    }

    if (auto* return_stmt = dyn_cast<ReturnStmt>(stmt)) {
        if (!return_stmt->expression) {
            return make_interp_fail_result(make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "constexpr interpreter does not support valueless return statements yet",
                return_stmt->location));
        }

        ConstEvalResult expr_result = eval_expr(return_stmt->expression.get(), mode, depth + 1);
        if (expr_result.status != ConstEvalStatus::Constant || !expr_result.value.has_value()) {
            return make_interp_fail_result(std::move(expr_result));
        }

        QualType return_type = nullptr;
        if (g_interpreter_session && !g_interpreter_session->frames.empty()) {
            return_type = extract_function_return_type(
                g_interpreter_session->frames.back().function_decl);
        }
        auto casted = cast_const_value_to_type(expr_result.value.value(), return_type);
        if (!casted.has_value()) {
            return make_interp_fail_result(make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "constexpr interpreter failed to convert return expression",
                return_stmt->location));
        }
        return make_interp_return_result(ConstEvalResult::constant(casted.value()));
    }

    if (isa<EmptyStmt>(stmt)) {
        return make_interp_continue_result();
    }

    if (auto* expr_stmt = dyn_cast<Expr>(stmt)) {
        ConstEvalResult expr_result = eval_expr(expr_stmt, mode, depth + 1);
        if (expr_result.status != ConstEvalStatus::Constant || !expr_result.value.has_value()) {
            return make_interp_fail_result(std::move(expr_result));
        }
        return make_interp_continue_result();
    }

    return make_interp_fail_result(make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
        "statement kind is not yet supported by constexpr interpreter", stmt->location));
}

// ====== Function call execution ======

ConstEvalResult eval_function_call_expr(FuncCall* call, ConstEvalMode mode, size_t depth) {
    if (!call || !call->func) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "unsupported function call expression", call ? call->location : SrcLoc());
    }
    if (!g_interpreter_session || !g_interpreter_session->state || !interpreter_mode_enabled(mode)) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr function interpreter is unavailable for this evaluation mode",
            call->location);
    }
    if (depth > kMaxConstEvalDepth) {
        return make_error(ConstEvalDiagCode::RecursionLimitExceeded,
            "constexpr recursion depth exceeded", call->location);
    }

    EvalState& state = *g_interpreter_session->state;
    if (!state.consume_step()) {
        return make_error(ConstEvalDiagCode::StepLimitExceeded,
            "constexpr function interpreter step limit exceeded",
            call->location);
    }

    std::string target_name = describe_function_call_target(call);
    InterpreterFrameGuard frame_guard(*g_interpreter_session, target_name, nullptr);
    if (!frame_guard.entered()) {
        return make_error(ConstEvalDiagCode::RecursionLimitExceeded,
            "constexpr function interpreter recursion limit exceeded",
            call->location);
    }

    Expr* callee_core = strip_noop_implicit_casts(call->func.get());
    auto* callee_ref = dyn_cast<VarRef>(callee_core);
    if (!callee_ref || !callee_ref->symref || callee_ref->symref->kind != SymbolKind::FUNCTION) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr interpreter currently supports direct named function calls only",
            call->location);
    }

    const FuncDecl* function_decl = callee_ref->symref->function_definition;
    if (!function_decl || !function_decl->body) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr interpreter cannot evaluate call without visible function definition",
            call->location);
    }
    if (!g_interpreter_session->frames.empty()) {
        g_interpreter_session->frames.back().function_decl = function_decl;
    }

    std::vector<const ParamDecl*> params;
    params.reserve(function_decl->parameters.size());
    for (const auto& param : function_decl->parameters) {
        auto* param_decl = dyn_cast<ParamDecl>(param.get());
        if (!param_decl) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "constexpr interpreter encountered unsupported parameter declaration",
                param ? param->location : function_decl->location);
        }
        params.push_back(param_decl);
    }

    bool has_void_sentinel = params.size() == 1 && is_void_parameter_sentinel(params.front());
    size_t required_param_count = has_void_sentinel ? 0 : params.size();
    if (call->args.size() != required_param_count) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr interpreter argument count mismatch for function call",
            call->location);
    }

    std::vector<ConstValue> argument_values;
    argument_values.reserve(call->args.size());
    for (const auto& arg : call->args) {
        ConstEvalResult arg_result = eval_expr(arg.get(), mode, depth + 1);
        if (arg_result.status != ConstEvalStatus::Constant || !arg_result.value.has_value()) {
            return arg_result;
        }
        argument_values.push_back(arg_result.value.value());
    }

    for (size_t i = 0; i < required_param_count; ++i) {
        const ParamDecl* param = params[i];
        auto casted = cast_const_value_to_type(argument_values[i], param->type);
        if (!casted.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "constexpr interpreter failed to convert argument to parameter type",
                call->location);
        }
        if (!bind_interpreter_local(param->sym, param->get_name(), casted.value())) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "constexpr interpreter failed to bind function parameter",
                call->location);
        }
    }

    InterpExecResult exec_result = eval_interpreter_stmt(function_decl->body.get(), mode, depth + 1);
    if (exec_result.kind == InterpExecResult::Kind::Fail) {
        return exec_result.value;
    }
    if (exec_result.kind != InterpExecResult::Kind::Return ||
        exec_result.value.status != ConstEvalStatus::Constant ||
        !exec_result.value.value.has_value()) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr interpreter reached end of function without a return value",
            function_decl->location);
    }

    auto casted_call_value = cast_const_value_to_type(exec_result.value.value.value(), call->get_type());
    if (!casted_call_value.has_value()) {
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "constexpr interpreter failed to convert call result to expression type",
            call->location);
    }
    return ConstEvalResult::constant(casted_call_value.value());
}

// ====== Main expression recursive evaluator ======

ConstEvalResult eval_expr(Expr* expr, ConstEvalMode mode, size_t depth) {
    if (!expr) {
        return make_error(ConstEvalDiagCode::NullExpression,
            "cannot evaluate a null expression", SrcLoc());
    }
    if (depth > kMaxConstEvalDepth) {
        return make_error(ConstEvalDiagCode::RecursionLimitExceeded,
            "constexpr recursion depth exceeded", expr->location);
    }

    if (auto* init_list = dyn_cast<InitListExpr>(expr)) {
        if (is_cpp_non_type_template_argument_mode(mode) &&
            init_list->type &&
            (init_list->type->kind == TypeKind::Object ||
             init_list->type->kind == TypeKind::Array)) {
            return eval_init_list_as_typed_const_value(
                init_list,
                init_list->type,
                mode,
                depth + 1);
        }
        if (!is_c23_constexpr_initializer_mode(mode)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "initializer list is not a constant expression in this mode",
                expr->location);
        }

        for (const auto& [_, value] : init_list->mappings) {
            if (!value) {
                continue;
            }
            ConstEvalResult value_res = eval_expr(value.get(), mode, depth + 1);
            if (value_res.status != ConstEvalStatus::Constant || !value_res.value.has_value()) {
                return value_res;
            }
        }

        // Non-scalar aggregate form accepted in this mode; payload value is a sentinel.
        return ConstEvalResult::constant(ConstValue::boolean(true));
    }

    if (isa<StringLiteral>(expr)) {
        if (!is_c23_constexpr_initializer_mode(mode)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "string literal is not a constant expression in this mode",
                expr->location);
        }
        // String literals are accepted as constant initializer leaves in C23 mode.
        return ConstEvalResult::constant(ConstValue::boolean(true));
    }

    if (auto* int_lit = dyn_cast<IntegerLiteral>(expr)) {
        auto parsed = parse_integer_literal_u64(int_lit->get_value());
        if (!parsed.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "unable to parse integer literal", expr->location);
        }
        IntShape shape = infer_integer_shape(int_lit->get_type());
        if (shape.is_unsigned) {
            return make_constant_int(ConstIntValue::from_unsigned(parsed.value(), shape.width));
        }
        return make_constant_int(ConstIntValue::from_signed(
            static_cast<int64_t>(parsed.value()), shape.width));
    }

    if (auto* float_lit = dyn_cast<FloatingLiteral>(expr)) {
        auto parsed = parse_floating_literal_ld(float_lit->value);
        if (!parsed.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "unable to parse floating literal", expr->location);
        }

        uint16_t width = 64;
        if (float_lit->get_type()) {
            int64_t type_width = float_lit->get_type()->getWidth();
            if (type_width > 0 && type_width <= std::numeric_limits<uint16_t>::max()) {
                width = static_cast<uint16_t>(type_width);
            }
        }
        return ConstEvalResult::constant(ConstValue::floating(*parsed, width));
    }

    if (auto* char_lit = dyn_cast<CharacterLiteral>(expr)) {
        IntShape shape = infer_integer_shape(char_lit->get_type());
        if (shape.is_unsigned) {
            return make_constant_int(ConstIntValue::from_unsigned(
                static_cast<uint64_t>(char_lit->int_value), shape.width));
        }
        return make_constant_int(ConstIntValue::from_signed(char_lit->int_value, shape.width));
    }

    if (auto* var_ref = dyn_cast<VarRef>(expr)) {
        ConstValue local_value;
        if (lookup_interpreter_local(var_ref, local_value)) {
            return ConstEvalResult::constant(local_value);
        }
        if (var_ref->symref && var_ref->symref->kind == SymbolKind::ENUM_CONSTANT) {
            IntShape shape = infer_integer_shape(var_ref->get_type());
            if (shape.is_unsigned) {
                return make_constant_int(ConstIntValue::from_unsigned(
                    static_cast<uint64_t>(var_ref->symref->enum_val), shape.width));
            }
            return make_constant_int(ConstIntValue::from_signed(var_ref->symref->enum_val, shape.width));
        }
        if (is_c23_constexpr_initializer_mode(mode) && var_ref->symref) {
            if (var_ref->symref->kind == SymbolKind::FUNCTION) {
                return ConstEvalResult::constant(ConstValue::boolean(true));
            }
            if (var_ref->symref->kind == SymbolKind::VARIABLE &&
                var_ref->get_type() &&
                var_ref->get_type()->kind == TypeKind::Array &&
                has_static_storage_duration(var_ref->symref.get())) {
                return ConstEvalResult::constant(ConstValue::boolean(true));
            }
        }
        if (is_cpp_non_type_template_argument_mode(mode) && var_ref->symref) {
            if (var_ref->symref->kind == SymbolKind::FUNCTION ||
                has_static_storage_duration(var_ref->symref.get())) {
                return ConstEvalResult::constant(
                    ConstValue::address(var_ref->symref));
            }
            ConstEvalResult constexpr_value =
                eval_local_constexpr_variable_initializer(
                    var_ref->symref.get(),
                    mode,
                    depth + 1);
            if (constexpr_value.status == ConstEvalStatus::Constant &&
                constexpr_value.value.has_value()) {
                return constexpr_value;
            }
        }
        return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
            "variable reference is not a constant expression", expr->location);
    }

    if (auto* call = dyn_cast<FuncCall>(expr)) {
        if (is_c23_constexpr_initializer_mode(mode)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "function call is not allowed in C23 constexpr initializer",
                expr->location);
        }
        if (!g_interpreter_session || !interpreter_mode_enabled(mode)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "function call is not a constant expression in this mode",
                expr->location);
        }
        return eval_function_call_expr(call, mode, depth + 1);
    }

    if (auto* call = dyn_cast<CppMemberCallExpr>(expr)) {
        if (!call->lowered_call) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "member call is not a constant expression in this mode",
                expr->location);
        }
        if (is_c23_constexpr_initializer_mode(mode)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "function call is not allowed in C23 constexpr initializer",
                expr->location);
        }
        if (!g_interpreter_session || !interpreter_mode_enabled(mode)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "member call is not a constant expression in this mode",
                expr->location);
        }
        return eval_function_call_expr(call->lowered_call.get(), mode, depth + 1);
    }

    if (auto* unary = dyn_cast<UnaryOperation>(expr)) {
        return eval_unary_expr(unary, mode, depth);
    }

    if (auto* binary = dyn_cast<BinaryOperation>(expr)) {
        return eval_binary_expr(binary, mode, depth);
    }

    if (auto* cond = dyn_cast<CondExpr>(expr)) {
        ConstEvalResult cond_res = eval_expr(cond->condition.get(), mode, depth + 1);
        if (cond_res.status != ConstEvalStatus::Constant || !cond_res.value.has_value()) {
            return cond_res;
        }
        bool truthy = false;
        if (!const_value_to_bool(cond_res.value.value(), truthy)) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "conditional expression requires scalar condition", cond->location);
        }
        if (truthy) {
            if (!cond->true_expr) {
                // GNU extension: omitted middle operand (`a ?: b`) yields `a` when truthy.
                return cond_res;
            }
            return eval_expr(cond->true_expr.get(), mode, depth + 1);
        }
        if (!cond->false_expr) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "missing false branch in conditional expression", cond->location);
        }
        return eval_expr(cond->false_expr.get(), mode, depth + 1);
    }

    if (auto* implicit_cast = dyn_cast<ImplicitCast>(expr)) {
        if (is_c23_constexpr_initializer_mode(mode) && implicit_cast->get_type() &&
            implicit_cast->get_type()->kind == TypeKind::Pointer) {
            if (implicit_cast->kind == ImplicitCastTypes::ARRAY_TO_POINTER ||
                implicit_cast->kind == ImplicitCastTypes::FUNCTION_TO_POINTER) {
                ConstEvalResult decayed = eval_expr(implicit_cast->expr.get(), mode, depth + 1);
                if (decayed.status == ConstEvalStatus::Constant && decayed.value.has_value()) {
                    return ConstEvalResult::constant(ConstValue::boolean(true));
                }
                return decayed;
            }
            if (implicit_cast->kind == ImplicitCastTypes::RAW_CAST ||
                implicit_cast->kind == ImplicitCastTypes::ARITH_CAST) {
                if (is_c23_address_constant_expr(implicit_cast->expr.get(), mode, depth + 1)) {
                    return ConstEvalResult::constant(ConstValue::boolean(true));
                }
                ConstEvalResult inner = eval_expr(implicit_cast->expr.get(), mode, depth + 1);
                if (inner.status != ConstEvalStatus::Constant || !inner.value.has_value()) {
                    return inner;
                }
                if (!is_zero_like_constant(inner.value.value())) {
                    return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                        "pointer cast operand is not a null pointer constant",
                        implicit_cast->location);
                }
                return ConstEvalResult::constant(ConstValue::boolean(true));
            }
        }
        if (is_cpp_non_type_template_argument_mode(mode) &&
            implicit_cast->get_type()) {
            if (implicit_cast->kind == ImplicitCastTypes::ARRAY_TO_POINTER ||
                implicit_cast->kind == ImplicitCastTypes::FUNCTION_TO_POINTER) {
                return eval_expr(implicit_cast->expr.get(), mode, depth + 1);
            }
            if (implicit_cast->kind == ImplicitCastTypes::RAW_CAST ||
                implicit_cast->kind == ImplicitCastTypes::ARITH_CAST) {
                return eval_cast_expr(
                    implicit_cast->expr.get(),
                    implicit_cast->get_type(),
                    implicit_cast->location,
                    mode,
                    depth,
                    false);
            }
        }
        return eval_cast_expr(implicit_cast->expr.get(), implicit_cast->get_type(),
            implicit_cast->location, mode, depth, false);
    }

    if (auto* explicit_cast = dyn_cast<ExplicitCast>(expr)) {
        return eval_cast_expr(explicit_cast->expr.get(), explicit_cast->get_type(),
            explicit_cast->location, mode, depth, true);
    }

    if (auto* member_ptr = dyn_cast<MemberPointerLiteralExpr>(expr)) {
        if (!is_cpp_non_type_template_argument_mode(mode)) {
            return make_not_evaluated(
                ConstEvalDiagCode::UnsupportedExpression,
                "member pointer is not a constant expression in this mode",
                expr->location);
        }
        return ConstEvalResult::constant(ConstValue::member_pointer(
            member_ptr->byte_offset,
            member_ptr->is_function_member,
            member_ptr->method_symbol,
            member_ptr->virtual_slot_index,
            member_ptr->member_name));
    }

    if (auto* compound_lit = dyn_cast<CompoundLiteralExpr>(expr)) {
        if (!compound_lit->init) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "compound literal has no initializer", expr->location);
        }
        if (is_cpp_non_type_template_argument_mode(mode) &&
            compound_lit->type &&
            (compound_lit->type->kind == TypeKind::Object ||
             compound_lit->type->kind == TypeKind::Array)) {
            return eval_expr_as_typed_const_value(
                compound_lit->init.get(),
                compound_lit->type,
                mode,
                depth + 1);
        }
        return eval_expr(compound_lit->init.get(), mode, depth + 1);
    }

    if (auto* sizeof_expr = dyn_cast<SizeOfExpr>(expr)) {
        auto val = evaluate_sizeof_expr(sizeof_expr);
        if (!val.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "sizeof expression is not a compile-time constant", expr->location);
        }
        return make_constant_int(ConstIntValue::from_signed(*val, 64));
    }

    if (auto* alignof_expr = dyn_cast<AlignOfExpr>(expr)) {
        auto val = evaluate_alignof_expr(alignof_expr);
        if (!val.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "alignof expression is not a compile-time constant", expr->location);
        }
        return make_constant_int(ConstIntValue::from_signed(*val, 64));
    }

    if (auto* offsetof_expr = dyn_cast<OffsetOfExpr>(expr)) {
        auto val = evaluate_offsetof_expr(offsetof_expr);
        if (!val.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "offsetof expression is not a compile-time constant", expr->location);
        }
        return make_constant_int(ConstIntValue::from_signed(*val, 64));
    }

    if (auto* builtin_call = dyn_cast<BuiltinCallExpr>(expr)) {
        if (!builtin_call->const_value.has_value()) {
            return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
                "builtin call is not a compile-time constant", expr->location);
        }
        return make_constant_int(ConstIntValue::from_signed(*builtin_call->const_value, 64));
    }

    return make_not_evaluated(ConstEvalDiagCode::UnsupportedExpression,
        "expression kind is not supported by consteval engine yet", expr->location);
}

} // namespace

// ====== Public API entry point ======

ConstEvalResult ConstEvalEngine::evaluate(const Expr* expr, ConstEvalMode mode) const {
    if (!is_enabled()) {
        ConstEvalResult result = ConstEvalResult::not_evaluated("constexpr engine is disabled");
        result.diagnostics.push_back(ConstEvalDiagnostic::make(
            ConstEvalDiagCode::EngineDisabled, result.message));
        return result;
    }
    if (expr == nullptr) {
        return ConstEvalResult::error("cannot evaluate a null expression",
            ConstEvalDiagCode::NullExpression);
    }

    if (lang_options_.enable_consteval_function_interpreter &&
        interpreter_mode_enabled(mode)) {
        EvalState state(
            lang_options_.consteval_step_limit,
            lang_options_.consteval_recursion_limit);
        InterpreterSession session;
        session.state = &state;
        session.mode = mode;
        InterpreterSessionGuard session_guard(&session);
        return eval_expr(const_cast<Expr*>(expr), mode, 0);
    }

    return eval_expr(const_cast<Expr*>(expr), mode, 0);
}
