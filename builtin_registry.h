#ifndef ABURI_BUILTIN_REGISTRY_H
#define ABURI_BUILTIN_REGISTRY_H

#include <string>
#include <string_view>
#include <unordered_map>

enum class BuiltinKind {
    // Tier 1: Critical kernel builtins
    EXPECT,
    CONSTANT_P,
    UNREACHABLE,
    TRAP,
    TYPES_COMPATIBLE_P,
    CHOOSE_EXPR,
    OBJECT_SIZE,
    DYNAMIC_OBJECT_SIZE,
    AVAILABLE,
    IS_CONSTANT_EVALUATED,
    IS_SAME,
    IS_FUNCTION,
    IS_REFERENCE,
    IS_LVALUE_REFERENCE,
    IS_RVALUE_REFERENCE,
    HAS_VIRTUAL_DESTRUCTOR,
    IS_ABSTRACT,
    IS_ARRAY,
    IS_UNION,
    IS_VOLATILE,
    IS_CONST,
    IS_EMPTY,
    IS_ENUM,
    IS_SCOPED_ENUM,
    IS_FUNDAMENTAL,
    IS_INTEGRAL,
    IS_ASSIGNABLE,
    IS_TRIVIALLY_ASSIGNABLE,
    IS_NOTHROW_ASSIGNABLE,
    IS_BASE_OF,
    IS_CLASS,
    IS_MEMBER_POINTER,
    IS_MEMBER_OBJECT_POINTER,
    IS_MEMBER_FUNCTION_POINTER,
    IS_NULL_POINTER,
    IS_OBJECT,
    IS_POINTER,
    IS_POLYMORPHIC,
    IS_STANDARD_LAYOUT,
    IS_TRIVIAL,
    IS_TRIVIALLY_COPYABLE,
    HAS_UNIQUE_OBJECT_REPRESENTATIONS,
    IS_POD,
    IS_SIGNED,
    IS_CONSTRUCTIBLE,
    IS_TRIVIALLY_CONSTRUCTIBLE,
    IS_NOTHROW_CONSTRUCTIBLE,
    IS_CONVERTIBLE,
    IS_CORE_CONVERTIBLE,
    IS_NOTHROW_CONVERTIBLE,
    IS_DESTRUCTIBLE,
    IS_TRIVIALLY_DESTRUCTIBLE,
    HAS_TRIVIAL_DESTRUCTOR,
    INTEGER_PACK,

    // Tier 2: Overflow builtins
    ADD_OVERFLOW,
    SUB_OVERFLOW,
    MUL_OVERFLOW,
    ADD_OVERFLOW_P,
    SUB_OVERFLOW_P,

    // Tier 2: Bit manipulation
    CLZ,
    CLZL,
    CLZLL,
    CTZ,
    CTZL,
    CTZLL,
    FFS,
    FFSL,
    FFSLL,
    POPCOUNT,
    POPCOUNTL,
    POPCOUNTLL,
    BSWAP16,
    BSWAP32,
    BSWAP64,
    IA32_BZHI_SI,

    // Tier 2: Memory/string
    STPCPY,
    MEMPCPY,
    MEMCPY,
    MEMMOVE,
    MEMSET,
    MEMCMP,
    MEMCMP_EQ,
    MEMCHR,
    BCOPY,
    BZERO,
    STRCMP,
    STRNCMP,
    STRLEN,
    STRCPY,
    STRNCPY,
    STRCAT,
    STRNCAT,
    STRCSPN,
    STRSPN,
    STRCHR,
    STRRCHR,
    STRSTR,
    STRDUP,
    STPNCPY,
    STRNDUP,
    STRNCASECMP,

    // Fortified (_chk) variants — ignore the extra object-size argument
    MEMCPY_CHK,
    MEMMOVE_CHK,
    MEMSET_CHK,
    STRNCPY_CHK,
    STRCPY_CHK,
    STPCPY_CHK,
    STRCAT_CHK,
    STRNCAT_CHK,
    SPRINTF_CHK,
    SNPRINTF_CHK,
    VSPRINTF_CHK,
    VSNPRINTF_CHK,

    // Tier 2: Stack/cache
    CLEAR_CACHE,
    CLEAR_PADDING,
    PREFETCH,
    RETURN_ADDRESS,
    FRAME_ADDRESS,
    EXTRACT_RETURN_ADDR,
    ALLOCA,
    STACK_SAVE,
    STACK_RESTORE,

    // Tier 3: Float builtins
    ISNAN,
    ISINF,
    ISINF_SIGN,
    ISFINITE,
    ISNORMAL,
    ISEQSIG,
    BUILTIN_HUGE_VAL,
    BUILTIN_HUGE_VALF,
    INF,
    INFF,
    INFL,
    BUILTIN_HUGE_VALL,
    NAN_BUILTIN,
    NANF,
    NANL,
    NANS,
    NANSF,
    NANSL,
    ABS,
    LABS,
    LLABS,
    FABS,
    FABSF,
    FABSL,
    COMPLEX,
    CONJF,
    ILOGB,

    // Math builtins
    POW,
    POWF,
    POWL,
    CPOW,
    CEXPI,
    SQRT,
    SQRTF,
    SQRTL,
    CBRT,
    CBRTF,
    CBRTL,
    SIN,
    SINF,
    COS,
    COSF,
    LOG,
    LOGF,
    LOG2,
    LOG2F,
    LOG10,
    LOG10F,
    EXP,
    EXPF,
    EXP2,
    EXP2F,
    CEIL,
    CEILF,
    FLOOR,
    FLOORF,
    ROUND,
    ROUNDF,
    COPYSIGN,
    COPYSIGNF,
    COPYSIGNL,
    HYPOT,
    HYPOTF,
    HYPOTL,
    FMIN,
    FMINF,
    FMINL,
    FMAX,
    FMAXF,
    FMAXL,

    MODF,
    MODFF,
    MODFL,
    TRUNC,
    TRUNCF,

    SIGNBIT,
    SIGNBITF,
    SIGNBITL,

    // Tier 3: Misc
    ASSUME_ALIGNED,
    CLASSIFY_TYPE,
    EXPECT_WITH_PROBABILITY,
    BUILTIN_FILE,
    BUILTIN_LINE,
    BUILTIN_FUNCTION,
    CLRSB,
    CLRSBL,
    CLRSBLL,
    PARITY,
    PARITYL,
    PARITYLL,
    CONVERTVECTOR,
    SHUFFLEVECTOR,
    VA_ARG_PACK,

    // Tier 4: Atomic builtins
    ATOMIC_LOAD_N,
    ATOMIC_STORE_N,
    ATOMIC_EXCHANGE_N,
    ATOMIC_COMPARE_EXCHANGE_N,
    ATOMIC_IS_LOCK_FREE,
    C11_ATOMIC_INIT,
    ATOMIC_FETCH_ADD,
    ATOMIC_FETCH_SUB,
    ATOMIC_FETCH_AND,
    ATOMIC_FETCH_OR,
    ATOMIC_FETCH_XOR,
    ATOMIC_FETCH_NAND,
    ATOMIC_ADD_FETCH,
    ATOMIC_SUB_FETCH,
    ATOMIC_AND_FETCH,
    ATOMIC_OR_FETCH,
    ATOMIC_XOR_FETCH,
    ATOMIC_NAND_FETCH,
    ATOMIC_THREAD_FENCE,
    ATOMIC_SIGNAL_FENCE,
    ATOMIC_TEST_AND_SET,
    ATOMIC_CLEAR,

    // Legacy __sync_* builtins
    SYNC_FETCH_AND_ADD,
    SYNC_FETCH_AND_SUB,
    SYNC_FETCH_AND_OR,
    SYNC_FETCH_AND_AND,
    SYNC_FETCH_AND_XOR,
    SYNC_FETCH_AND_NAND,
    SYNC_ADD_AND_FETCH,
    SYNC_SUB_AND_FETCH,
    SYNC_OR_AND_FETCH,
    SYNC_AND_AND_FETCH,
    SYNC_XOR_AND_FETCH,
    SYNC_NAND_AND_FETCH,
    SYNC_BOOL_COMPARE_AND_SWAP,
    SYNC_VAL_COMPARE_AND_SWAP,
    SYNC_SYNCHRONIZE,
    SYNC_LOCK_TEST_AND_SET,
    SYNC_LOCK_RELEASE,

    // I/O builtins
    PRINTF,
    PUTS,
    PUTCHAR,
    FPRINTF,
    SPRINTF,
    SNPRINTF,

    // Floating-point comparison builtins
    ISUNORDERED,
    ISLESS,
    ISLESSEQUAL,
    ISGREATER,
    ISGREATEREQUAL,
    ISLESSGREATER,

    // Memory allocation
    MALLOC,
    CALLOC,
    REALLOC,
    FREE,

    // Process control
    ABORT,
    EXIT,
};

struct BuiltinInfo {
    std::string_view name;
    BuiltinKind kind;
    int min_args;
    int max_args;        // -1 for unlimited
    bool takes_type_arg; // needs parser-level handling (parses types instead of expressions)
    bool is_compile_time_const; // evaluable by constexpr compatibility checks
};

class BuiltinRegistry {
public:
    static BuiltinRegistry& instance();

    const BuiltinInfo* lookup(std::string_view name) const;
    bool is_builtin(std::string_view name) const;

private:
    BuiltinRegistry();
    void register_builtin(BuiltinInfo info);

    std::unordered_map<std::string_view, BuiltinInfo> builtins;
};

bool is_builtin_type_trait_kind(BuiltinKind kind);

#endif //ABURI_BUILTIN_REGISTRY_H
