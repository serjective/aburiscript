#include "builtin_registry.h"

BuiltinRegistry& BuiltinRegistry::instance() {
    static BuiltinRegistry reg;
    return reg;
}

const BuiltinInfo* BuiltinRegistry::lookup(std::string_view name) const {
    auto it = builtins.find(name);
    if (it != builtins.end()) return &it->second;
    return nullptr;
}

bool BuiltinRegistry::is_builtin(std::string_view name) const {
    return builtins.count(name) > 0;
}

bool BuiltinRegistry::is_supported(std::string_view name) const {
    auto it = builtins.find(name);
    return it != builtins.end() && it->second.supported;
}

bool is_builtin_type_trait_kind(BuiltinKind kind) {
    switch (kind) {
        case BuiltinKind::IS_SAME:
        case BuiltinKind::IS_FUNCTION:
        case BuiltinKind::IS_REFERENCE:
        case BuiltinKind::IS_LVALUE_REFERENCE:
        case BuiltinKind::IS_RVALUE_REFERENCE:
        case BuiltinKind::HAS_VIRTUAL_DESTRUCTOR:
        case BuiltinKind::IS_ABSTRACT:
        case BuiltinKind::IS_ARRAY:
        case BuiltinKind::IS_BOUNDED_ARRAY:
        case BuiltinKind::IS_UNION:
        case BuiltinKind::IS_VOLATILE:
        case BuiltinKind::IS_CONST:
        case BuiltinKind::IS_EMPTY:
        case BuiltinKind::IS_ENUM:
        case BuiltinKind::IS_SCOPED_ENUM:
        case BuiltinKind::IS_FUNDAMENTAL:
        case BuiltinKind::IS_VOID:
        case BuiltinKind::IS_INTEGRAL:
        case BuiltinKind::IS_FLOATING_POINT:
        case BuiltinKind::IS_ARITHMETIC:
        case BuiltinKind::IS_SCALAR:
        case BuiltinKind::IS_COMPOUND:
        case BuiltinKind::IS_UNSIGNED:
        case BuiltinKind::IS_ASSIGNABLE:
        case BuiltinKind::IS_TRIVIALLY_ASSIGNABLE:
        case BuiltinKind::IS_NOTHROW_ASSIGNABLE:
        case BuiltinKind::IS_BASE_OF:
        case BuiltinKind::IS_CLASS:
        case BuiltinKind::IS_FINAL:
        case BuiltinKind::IS_AGGREGATE:
        case BuiltinKind::IS_MEMBER_POINTER:
        case BuiltinKind::IS_MEMBER_OBJECT_POINTER:
        case BuiltinKind::IS_MEMBER_FUNCTION_POINTER:
        case BuiltinKind::IS_NULL_POINTER:
        case BuiltinKind::IS_OBJECT:
        case BuiltinKind::IS_POINTER:
        case BuiltinKind::IS_POLYMORPHIC:
        case BuiltinKind::IS_STANDARD_LAYOUT:
        case BuiltinKind::IS_TRIVIAL:
        case BuiltinKind::IS_TRIVIALLY_COPYABLE:
        case BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS:
        case BuiltinKind::IS_POD:
        case BuiltinKind::IS_SIGNED:
        case BuiltinKind::IS_CONSTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE:
        case BuiltinKind::IS_CONVERTIBLE:
        case BuiltinKind::IS_CORE_CONVERTIBLE:
        case BuiltinKind::IS_NOTHROW_CONVERTIBLE:
        case BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY:
        case BuiltinKind::IS_DESTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_DESTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE:
        case BuiltinKind::HAS_TRIVIAL_DESTRUCTOR:
        case BuiltinKind::IS_LITERAL_TYPE:
            return true;
        default:
            return false;
    }
}

BuiltinSyntaxKind builtin_syntax_kind(BuiltinKind kind) {
    if (kind == BuiltinKind::AVAILABLE) {
        return BuiltinSyntaxKind::Available;
    }
    if (is_builtin_type_trait_kind(kind)) {
        return BuiltinSyntaxKind::TypeTrait;
    }
    switch (kind) {
        case BuiltinKind::MAKE_INTEGER_SEQ:
            return BuiltinSyntaxKind::IntegerSequenceType;
        case BuiltinKind::TYPE_PACK_ELEMENT:
            return BuiltinSyntaxKind::PackElementType;
        case BuiltinKind::REMOVE_CONST:
        case BuiltinKind::REMOVE_VOLATILE:
        case BuiltinKind::REMOVE_CV:
        case BuiltinKind::REMOVE_CVREF:
        case BuiltinKind::REMOVE_REFERENCE:
        case BuiltinKind::UNDERLYING_TYPE:
        case BuiltinKind::REMOVE_EXTENT:
        case BuiltinKind::REMOVE_ALL_EXTENTS:
        case BuiltinKind::ADD_LVALUE_REFERENCE:
        case BuiltinKind::ADD_RVALUE_REFERENCE:
        case BuiltinKind::ADD_POINTER:
        case BuiltinKind::DECAY:
            return BuiltinSyntaxKind::TypeTransform;
        case BuiltinKind::TYPES_COMPATIBLE_P:
            return BuiltinSyntaxKind::TypePredicate;
        case BuiltinKind::CHOOSE_EXPR:
            return BuiltinSyntaxKind::ChooseExpr;
        case BuiltinKind::OFFSETOF:
            return BuiltinSyntaxKind::Offsetof;
        case BuiltinKind::VA_ARG:
            return BuiltinSyntaxKind::VaArg;
        case BuiltinKind::BIT_CAST:
            return BuiltinSyntaxKind::BitCast;
        case BuiltinKind::CONVERTVECTOR:
            return BuiltinSyntaxKind::ConvertVector;
        default:
            return BuiltinSyntaxKind::Call;
    }
}

namespace {

struct LibcallEntry {
    BuiltinKind kind;
    BuiltinLibcall spec;
};

const LibcallEntry libcall_table[] = {
    {BuiltinKind::CBRT, {"cbrt", "dd"}},     {BuiltinKind::CBRTF, {"cbrtf", "ff"}},     {BuiltinKind::CBRTL, {"cbrtl", "ee"}},
    {BuiltinKind::TAN, {"tan", "dd"}},       {BuiltinKind::TANF, {"tanf", "ff"}},       {BuiltinKind::TANL, {"tanl", "ee"}},
    {BuiltinKind::ASIN, {"asin", "dd"}},     {BuiltinKind::ASINF, {"asinf", "ff"}},     {BuiltinKind::ASINL, {"asinl", "ee"}},
    {BuiltinKind::ACOS, {"acos", "dd"}},     {BuiltinKind::ACOSF, {"acosf", "ff"}},     {BuiltinKind::ACOSL, {"acosl", "ee"}},
    {BuiltinKind::ATAN, {"atan", "dd"}},     {BuiltinKind::ATANF, {"atanf", "ff"}},     {BuiltinKind::ATANL, {"atanl", "ee"}},
    {BuiltinKind::ATAN2, {"atan2", "ddd"}},  {BuiltinKind::ATAN2F, {"atan2f", "fff"}},  {BuiltinKind::ATAN2L, {"atan2l", "eee"}},
    {BuiltinKind::SINH, {"sinh", "dd"}},     {BuiltinKind::SINHF, {"sinhf", "ff"}},     {BuiltinKind::SINHL, {"sinhl", "ee"}},
    {BuiltinKind::COSH, {"cosh", "dd"}},     {BuiltinKind::COSHF, {"coshf", "ff"}},     {BuiltinKind::COSHL, {"coshl", "ee"}},
    {BuiltinKind::TANH, {"tanh", "dd"}},     {BuiltinKind::TANHF, {"tanhf", "ff"}},     {BuiltinKind::TANHL, {"tanhl", "ee"}},
    {BuiltinKind::ASINH, {"asinh", "dd"}},   {BuiltinKind::ASINHF, {"asinhf", "ff"}},   {BuiltinKind::ASINHL, {"asinhl", "ee"}},
    {BuiltinKind::ACOSH, {"acosh", "dd"}},   {BuiltinKind::ACOSHF, {"acoshf", "ff"}},   {BuiltinKind::ACOSHL, {"acoshl", "ee"}},
    {BuiltinKind::ATANH, {"atanh", "dd"}},   {BuiltinKind::ATANHF, {"atanhf", "ff"}},   {BuiltinKind::ATANHL, {"atanhl", "ee"}},
    {BuiltinKind::ERF, {"erf", "dd"}},       {BuiltinKind::ERFF, {"erff", "ff"}},       {BuiltinKind::ERFL, {"erfl", "ee"}},
    {BuiltinKind::ERFC, {"erfc", "dd"}},     {BuiltinKind::ERFCF, {"erfcf", "ff"}},     {BuiltinKind::ERFCL, {"erfcl", "ee"}},
    {BuiltinKind::LGAMMA, {"lgamma", "dd"}}, {BuiltinKind::LGAMMAF, {"lgammaf", "ff"}}, {BuiltinKind::LGAMMAL, {"lgammal", "ee"}},
    {BuiltinKind::TGAMMA, {"tgamma", "dd"}}, {BuiltinKind::TGAMMAF, {"tgammaf", "ff"}}, {BuiltinKind::TGAMMAL, {"tgammal", "ee"}},
    {BuiltinKind::EXPM1, {"expm1", "dd"}},   {BuiltinKind::EXPM1F, {"expm1f", "ff"}},   {BuiltinKind::EXPM1L, {"expm1l", "ee"}},
    {BuiltinKind::LOG1P, {"log1p", "dd"}},   {BuiltinKind::LOG1PF, {"log1pf", "ff"}},   {BuiltinKind::LOG1PL, {"log1pl", "ee"}},
    {BuiltinKind::LOGB, {"logb", "dd"}},     {BuiltinKind::LOGBF, {"logbf", "ff"}},     {BuiltinKind::LOGBL, {"logbl", "ee"}},
    {BuiltinKind::ILOGB, {"ilogb", "id"}},   {BuiltinKind::ILOGBF, {"ilogbf", "if"}},   {BuiltinKind::ILOGBL, {"ilogbl", "ie"}},
    {BuiltinKind::LDEXP, {"ldexp", "ddi"}},  {BuiltinKind::LDEXPF, {"ldexpf", "ffi"}},  {BuiltinKind::LDEXPL, {"ldexpl", "eei"}},
    {BuiltinKind::SCALBN, {"scalbn", "ddi"}},{BuiltinKind::SCALBNF, {"scalbnf", "ffi"}},{BuiltinKind::SCALBNL, {"scalbnl", "eei"}},
    {BuiltinKind::SCALBLN, {"scalbln", "ddl"}},{BuiltinKind::SCALBLNF, {"scalblnf", "ffl"}},{BuiltinKind::SCALBLNL, {"scalblnl", "eel"}},
    {BuiltinKind::FREXP, {"frexp", "ddI"}},  {BuiltinKind::FREXPF, {"frexpf", "ffI"}},  {BuiltinKind::FREXPL, {"frexpl", "eeI"}},
    {BuiltinKind::MODF, {"modf", "ddD"}},    {BuiltinKind::MODFF, {"modff", "ffF"}},    {BuiltinKind::MODFL, {"modfl", "eeE"}},
    {BuiltinKind::NEXTAFTER, {"nextafter", "ddd"}}, {BuiltinKind::NEXTAFTERF, {"nextafterf", "fff"}}, {BuiltinKind::NEXTAFTERL, {"nextafterl", "eee"}},
    {BuiltinKind::NEXTTOWARD, {"nexttoward", "dde"}}, {BuiltinKind::NEXTTOWARDF, {"nexttowardf", "ffe"}}, {BuiltinKind::NEXTTOWARDL, {"nexttowardl", "eee"}},
    {BuiltinKind::FDIM, {"fdim", "ddd"}},    {BuiltinKind::FDIMF, {"fdimf", "fff"}},    {BuiltinKind::FDIML, {"fdiml", "eee"}},
    {BuiltinKind::REMAINDER, {"remainder", "ddd"}}, {BuiltinKind::REMAINDERF, {"remainderf", "fff"}}, {BuiltinKind::REMAINDERL, {"remainderl", "eee"}},
    {BuiltinKind::REMQUO, {"remquo", "dddI"}}, {BuiltinKind::REMQUOF, {"remquof", "fffI"}}, {BuiltinKind::REMQUOL, {"remquol", "eeeI"}},
    {BuiltinKind::LRINT, {"lrint", "ld"}},   {BuiltinKind::LRINTF, {"lrintf", "lf"}},   {BuiltinKind::LRINTL, {"lrintl", "le"}},
    {BuiltinKind::LLRINT, {"llrint", "Ld"}}, {BuiltinKind::LLRINTF, {"llrintf", "Lf"}}, {BuiltinKind::LLRINTL, {"llrintl", "Le"}},
    {BuiltinKind::LROUND, {"lround", "ld"}}, {BuiltinKind::LROUNDF, {"lroundf", "lf"}}, {BuiltinKind::LROUNDL, {"lroundl", "le"}},
    {BuiltinKind::LLROUND, {"llround", "Ld"}}, {BuiltinKind::LLROUNDF, {"llroundf", "Lf"}}, {BuiltinKind::LLROUNDL, {"llroundl", "Le"}},
    {BuiltinKind::HYPOT, {"hypot", "ddd"}},  {BuiltinKind::HYPOTF, {"hypotf", "fff"}},  {BuiltinKind::HYPOTL, {"hypotl", "eee"}},
    {BuiltinKind::STRCMP, {"strcmp", "ipp"}},
    {BuiltinKind::STRNCMP, {"strncmp", "ippz"}},
    {BuiltinKind::STRCHR, {"strchr", "ppi"}},
    {BuiltinKind::STRRCHR, {"strrchr", "ppi"}},
    {BuiltinKind::STRSTR, {"strstr", "ppp"}},
    {BuiltinKind::STRCSPN, {"strcspn", "zpp"}},
    {BuiltinKind::STRSPN, {"strspn", "zpp"}},
    {BuiltinKind::STRNCASECMP, {"strncasecmp", "ippz"}},
    {BuiltinKind::STPNCPY, {"stpncpy", "pppz"}},
    {BuiltinKind::STRNDUP, {"strndup", "ppz"}},
    {BuiltinKind::STRCPY, {"strcpy", "ppp"}},
    {BuiltinKind::STRNCPY, {"strncpy", "pppz"}},
    {BuiltinKind::STRCAT, {"strcat", "ppp"}},
    {BuiltinKind::STRNCAT, {"strncat", "pppz"}},
    {BuiltinKind::STRDUP, {"strdup", "pp"}},
    {BuiltinKind::MEMCHR, {"memchr", "ppiz"}},
    {BuiltinKind::MEMCMP, {"memcmp", "iqqz"}},
    {BuiltinKind::MEMCMP_EQ, {"memcmp", "iqqz"}},
    {BuiltinKind::BZERO, {"bzero", "vpz"}},
    {BuiltinKind::BCOPY, {"bcopy", "vppz"}},
    {BuiltinKind::MALLOC, {"malloc", "pz"}},
    {BuiltinKind::FREE, {"free", "vp"}},
    {BuiltinKind::CALLOC, {"calloc", "pzz"}},
    {BuiltinKind::REALLOC, {"realloc", "ppz"}},
    {BuiltinKind::MEMPCPY, {"mempcpy", "pppz"}},
    {BuiltinKind::STPCPY, {"stpcpy", "ppp"}},
    {BuiltinKind::PUTS, {"puts", "ip"}},
    {BuiltinKind::PUTCHAR, {"putchar", "ii"}},
    {BuiltinKind::PRINTF, {"printf", "ip."}},
    {BuiltinKind::FPRINTF, {"fprintf", "ipp."}},
    {BuiltinKind::SPRINTF, {"sprintf", "ipp."}},
    {BuiltinKind::SNPRINTF, {"snprintf", "ipzp."}},
    {BuiltinKind::ABORT, {"abort", "v"}},
    {BuiltinKind::EXIT, {"exit", "vi"}},
};

} // namespace

const BuiltinLibcall* builtin_libcall(BuiltinKind kind) {
    for (const LibcallEntry& entry : libcall_table) {
        if (entry.kind == kind) {
            return &entry.spec;
        }
    }
    return nullptr;
}

bool is_supported_builtin_kind(BuiltinKind kind) {
    switch (kind) {
        case BuiltinKind::EXPECT:
        case BuiltinKind::EXPECT_WITH_PROBABILITY:
        case BuiltinKind::CONSTANT_P:
        case BuiltinKind::UNREACHABLE:
        case BuiltinKind::TRAP:
        case BuiltinKind::TYPES_COMPATIBLE_P:
        case BuiltinKind::CHOOSE_EXPR:
        case BuiltinKind::OBJECT_SIZE:
        case BuiltinKind::DYNAMIC_OBJECT_SIZE:
        case BuiltinKind::OFFSETOF:
        case BuiltinKind::IS_CONSTANT_EVALUATED:
        case BuiltinKind::SOURCE_LOCATION:
        case BuiltinKind::BIT_CAST:
        case BuiltinKind::LAUNDER:
        case BuiltinKind::CORO_DONE:
        case BuiltinKind::CORO_RESUME:
        case BuiltinKind::CORO_DESTROY:
        case BuiltinKind::CORO_PROMISE:
        case BuiltinKind::OPERATOR_NEW:
        case BuiltinKind::OPERATOR_DELETE:
        case BuiltinKind::METAFN_QUERY_INT:
        case BuiltinKind::METAFN_QUERY_INFO:
        case BuiltinKind::METAFN_NAME_DATA:
        case BuiltinKind::METAFN_NAME_SIZE:
        case BuiltinKind::METAFN_RANGE_COUNT:
        case BuiltinKind::METAFN_RANGE_AT:
        case BuiltinKind::IS_SAME:
        case BuiltinKind::IS_FUNCTION:
        case BuiltinKind::IS_REFERENCE:
        case BuiltinKind::IS_LVALUE_REFERENCE:
        case BuiltinKind::IS_RVALUE_REFERENCE:
        case BuiltinKind::IS_ARRAY:
        case BuiltinKind::IS_BOUNDED_ARRAY:
        case BuiltinKind::IS_UNION:
        case BuiltinKind::IS_VOLATILE:
        case BuiltinKind::IS_CONST:
        case BuiltinKind::IS_EMPTY:
        case BuiltinKind::IS_ENUM:
        case BuiltinKind::IS_SCOPED_ENUM:
        case BuiltinKind::IS_FUNDAMENTAL:
        case BuiltinKind::IS_VOID:
        case BuiltinKind::IS_INTEGRAL:
        case BuiltinKind::IS_FLOATING_POINT:
        case BuiltinKind::IS_ARITHMETIC:
        case BuiltinKind::IS_SCALAR:
        case BuiltinKind::IS_COMPOUND:
        case BuiltinKind::IS_UNSIGNED:
        case BuiltinKind::IS_ASSIGNABLE:
        case BuiltinKind::IS_TRIVIALLY_ASSIGNABLE:
        case BuiltinKind::IS_NOTHROW_ASSIGNABLE:
        case BuiltinKind::IS_BASE_OF:
        case BuiltinKind::IS_CLASS:
        case BuiltinKind::HAS_VIRTUAL_DESTRUCTOR:
        case BuiltinKind::IS_ABSTRACT:
        case BuiltinKind::IS_FINAL:
        case BuiltinKind::IS_AGGREGATE:
        case BuiltinKind::IS_MEMBER_POINTER:
        case BuiltinKind::IS_MEMBER_OBJECT_POINTER:
        case BuiltinKind::IS_MEMBER_FUNCTION_POINTER:
        case BuiltinKind::IS_NULL_POINTER:
        case BuiltinKind::IS_OBJECT:
        case BuiltinKind::IS_POINTER:
        case BuiltinKind::IS_POLYMORPHIC:
        case BuiltinKind::IS_STANDARD_LAYOUT:
        case BuiltinKind::IS_TRIVIAL:
        case BuiltinKind::IS_TRIVIALLY_COPYABLE:
        case BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS:
        case BuiltinKind::IS_POD:
        case BuiltinKind::IS_SIGNED:
        case BuiltinKind::IS_CONSTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE:
        case BuiltinKind::IS_CONVERTIBLE:
        case BuiltinKind::IS_CORE_CONVERTIBLE:
        case BuiltinKind::IS_NOTHROW_CONVERTIBLE:
        case BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY:
        case BuiltinKind::IS_DESTRUCTIBLE:
        case BuiltinKind::IS_NOTHROW_DESTRUCTIBLE:
        case BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE:
        case BuiltinKind::HAS_TRIVIAL_DESTRUCTOR:
        case BuiltinKind::IS_LITERAL_TYPE:
        case BuiltinKind::INTEGER_PACK:
        case BuiltinKind::MAKE_INTEGER_SEQ:
        case BuiltinKind::TYPE_PACK_ELEMENT:
        case BuiltinKind::REMOVE_CV:
        case BuiltinKind::REMOVE_CONST:
        case BuiltinKind::REMOVE_VOLATILE:
        case BuiltinKind::REMOVE_CVREF:
        case BuiltinKind::REMOVE_REFERENCE:
        case BuiltinKind::UNDERLYING_TYPE:
        case BuiltinKind::REMOVE_EXTENT:
        case BuiltinKind::REMOVE_ALL_EXTENTS:
        case BuiltinKind::ADD_LVALUE_REFERENCE:
        case BuiltinKind::ADD_RVALUE_REFERENCE:
        case BuiltinKind::ADD_POINTER:
        case BuiltinKind::DECAY:
        case BuiltinKind::ADDRESSOF:
        case BuiltinKind::ASSUME_ALIGNED:
        case BuiltinKind::MEMCPY:
        case BuiltinKind::MEMMOVE:
        case BuiltinKind::MEMSET:
        case BuiltinKind::CLZ:
        case BuiltinKind::CLZL:
        case BuiltinKind::CLZLL:
        case BuiltinKind::CLZG:
        case BuiltinKind::CTZ:
        case BuiltinKind::CTZL:
        case BuiltinKind::CTZLL:
        case BuiltinKind::CTZG:
        case BuiltinKind::FFS:
        case BuiltinKind::FFSL:
        case BuiltinKind::FFSLL:
        case BuiltinKind::POPCOUNT:
        case BuiltinKind::POPCOUNTL:
        case BuiltinKind::POPCOUNTLL:
        case BuiltinKind::POPCOUNTG:
        case BuiltinKind::BSWAP16:
        case BuiltinKind::BSWAP32:
        case BuiltinKind::BSWAP64:
        case BuiltinKind::CONVERTVECTOR:
        case BuiltinKind::REDUCE_AND:
        case BuiltinKind::SHUFFLEVECTOR:
        case BuiltinKind::VA_START:
        case BuiltinKind::VA_ARG:
        case BuiltinKind::VA_END:
        case BuiltinKind::VA_COPY:
        case BuiltinKind::VA_ARG_PACK:
        case BuiltinKind::MEMCPY_CHK:
        case BuiltinKind::MEMMOVE_CHK:
        case BuiltinKind::MEMSET_CHK:
        case BuiltinKind::STRCPY_CHK:
        case BuiltinKind::STPCPY_CHK:
        case BuiltinKind::STRCAT_CHK:
        case BuiltinKind::STRNCPY_CHK:
        case BuiltinKind::STRNCAT_CHK:
        case BuiltinKind::SPRINTF_CHK:
        case BuiltinKind::SNPRINTF_CHK:
        case BuiltinKind::ATOMIC_LOAD_N:
        case BuiltinKind::ATOMIC_STORE_N:
        case BuiltinKind::ATOMIC_EXCHANGE_N:
        case BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N:
        case BuiltinKind::ATOMIC_FETCH_ADD:
        case BuiltinKind::ATOMIC_FETCH_SUB:
        case BuiltinKind::ATOMIC_FETCH_AND:
        case BuiltinKind::ATOMIC_FETCH_OR:
        case BuiltinKind::ATOMIC_FETCH_XOR:
        case BuiltinKind::ATOMIC_FETCH_NAND:
        case BuiltinKind::ATOMIC_ADD_FETCH:
        case BuiltinKind::ATOMIC_SUB_FETCH:
        case BuiltinKind::ATOMIC_AND_FETCH:
        case BuiltinKind::ATOMIC_OR_FETCH:
        case BuiltinKind::ATOMIC_XOR_FETCH:
        case BuiltinKind::ATOMIC_NAND_FETCH:
        case BuiltinKind::C11_ATOMIC_FETCH_ADD:
        case BuiltinKind::C11_ATOMIC_FETCH_SUB:
        case BuiltinKind::C11_ATOMIC_INIT:
        case BuiltinKind::ATOMIC_TEST_AND_SET:
        case BuiltinKind::ATOMIC_CLEAR:
        case BuiltinKind::ATOMIC_THREAD_FENCE:
        case BuiltinKind::ATOMIC_SIGNAL_FENCE:
        case BuiltinKind::ATOMIC_IS_LOCK_FREE:
        case BuiltinKind::ATOMIC_ALWAYS_LOCK_FREE:
        case BuiltinKind::SYNC_FETCH_AND_ADD:
        case BuiltinKind::SYNC_FETCH_AND_SUB:
        case BuiltinKind::SYNC_FETCH_AND_OR:
        case BuiltinKind::SYNC_FETCH_AND_AND:
        case BuiltinKind::SYNC_FETCH_AND_XOR:
        case BuiltinKind::SYNC_FETCH_AND_NAND:
        case BuiltinKind::SYNC_ADD_AND_FETCH:
        case BuiltinKind::SYNC_SUB_AND_FETCH:
        case BuiltinKind::SYNC_OR_AND_FETCH:
        case BuiltinKind::SYNC_AND_AND_FETCH:
        case BuiltinKind::SYNC_XOR_AND_FETCH:
        case BuiltinKind::SYNC_NAND_AND_FETCH:
        case BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP:
        case BuiltinKind::SYNC_VAL_COMPARE_AND_SWAP:
        case BuiltinKind::SYNC_LOCK_TEST_AND_SET:
        case BuiltinKind::SYNC_LOCK_RELEASE:
        case BuiltinKind::SYNC_SYNCHRONIZE:
        case BuiltinKind::COMPLEX:
        case BuiltinKind::CONJF:
        case BuiltinKind::CPOW:
        case BuiltinKind::CEXPI:
        case BuiltinKind::STRLEN:
        case BuiltinKind::ALLOCA:
        case BuiltinKind::RETURN_ADDRESS:
        case BuiltinKind::FRAME_ADDRESS:
        case BuiltinKind::EXTRACT_RETURN_ADDR:
        case BuiltinKind::FLT_ROUNDS:
        case BuiltinKind::ISNAN:
        case BuiltinKind::ISINF:
        case BuiltinKind::ISINF_SIGN:
        case BuiltinKind::ISNORMAL:
        case BuiltinKind::ISFINITE:
        case BuiltinKind::ABS:
        case BuiltinKind::LABS:
        case BuiltinKind::LLABS:
        case BuiltinKind::FABS:
        case BuiltinKind::FABSF:
        case BuiltinKind::FABSL:
        case BuiltinKind::NAN_BUILTIN:
        case BuiltinKind::NANF:
        case BuiltinKind::NANL:
        case BuiltinKind::NANS:
        case BuiltinKind::NANSF:
        case BuiltinKind::NANSL:
        case BuiltinKind::BUILTIN_HUGE_VAL:
        case BuiltinKind::BUILTIN_HUGE_VALF:
        case BuiltinKind::BUILTIN_HUGE_VALL:
        case BuiltinKind::INF:
        case BuiltinKind::INFF:
        case BuiltinKind::INFL:
        case BuiltinKind::COPYSIGN:
        case BuiltinKind::COPYSIGNF:
        case BuiltinKind::COPYSIGNL:
        case BuiltinKind::CLASSIFY_TYPE:
        case BuiltinKind::CLRSB:
        case BuiltinKind::CLRSBL:
        case BuiltinKind::CLRSBLL:
        case BuiltinKind::PARITY:
        case BuiltinKind::PARITYL:
        case BuiltinKind::PARITYLL:
        case BuiltinKind::IA32_BZHI_SI:
        case BuiltinKind::ADD_OVERFLOW:
        case BuiltinKind::SUB_OVERFLOW:
        case BuiltinKind::MUL_OVERFLOW:
        case BuiltinKind::SQRT:
        case BuiltinKind::SQRTF:
        case BuiltinKind::SQRTL:
        case BuiltinKind::SIN:
        case BuiltinKind::SINF:
        case BuiltinKind::SINL:
        case BuiltinKind::COS:
        case BuiltinKind::COSF:
        case BuiltinKind::COSL:
        case BuiltinKind::POW:
        case BuiltinKind::POWF:
        case BuiltinKind::POWL:
        case BuiltinKind::EXP:
        case BuiltinKind::EXPF:
        case BuiltinKind::EXPL:
        case BuiltinKind::EXP2:
        case BuiltinKind::EXP2F:
        case BuiltinKind::EXP2L:
        case BuiltinKind::LOG:
        case BuiltinKind::LOGF:
        case BuiltinKind::LOGL:
        case BuiltinKind::LOG2:
        case BuiltinKind::LOG2F:
        case BuiltinKind::LOG2L:
        case BuiltinKind::LOG10:
        case BuiltinKind::LOG10F:
        case BuiltinKind::LOG10L:
        case BuiltinKind::FLOOR:
        case BuiltinKind::FLOORF:
        case BuiltinKind::FLOORL:
        case BuiltinKind::CEIL:
        case BuiltinKind::CEILF:
        case BuiltinKind::CEILL:
        case BuiltinKind::TRUNC:
        case BuiltinKind::TRUNCF:
        case BuiltinKind::TRUNCL:
        case BuiltinKind::RINT:
        case BuiltinKind::RINTF:
        case BuiltinKind::RINTL:
        case BuiltinKind::NEARBYINT:
        case BuiltinKind::NEARBYINTF:
        case BuiltinKind::NEARBYINTL:
        case BuiltinKind::ROUND:
        case BuiltinKind::ROUNDF:
        case BuiltinKind::ROUNDL:
        case BuiltinKind::FMA:
        case BuiltinKind::FMAF:
        case BuiltinKind::FMAL:
        case BuiltinKind::FMIN:
        case BuiltinKind::FMINF:
        case BuiltinKind::FMINL:
        case BuiltinKind::FMAX:
        case BuiltinKind::FMAXF:
        case BuiltinKind::FMAXL:
        case BuiltinKind::FMOD:
        case BuiltinKind::FMODF:
        case BuiltinKind::FMODL:
        case BuiltinKind::SUB_OVERFLOW_P:
        case BuiltinKind::ADD_OVERFLOW_P:
        case BuiltinKind::ISEQSIG:
        case BuiltinKind::CLEAR_CACHE:
        case BuiltinKind::PREFETCH:
        case BuiltinKind::SIGNBIT:
        case BuiltinKind::SIGNBITF:
        case BuiltinKind::SIGNBITL:
        case BuiltinKind::ISUNORDERED:
        case BuiltinKind::ISGREATER:
        case BuiltinKind::ISLESS:
        case BuiltinKind::ISLESSEQUAL:
        case BuiltinKind::ISLESSGREATER:
        case BuiltinKind::ISGREATEREQUAL:
        case BuiltinKind::STACK_SAVE:
        case BuiltinKind::STACK_RESTORE:
        case BuiltinKind::FPCLASSIFY:
        case BuiltinKind::CLEAR_PADDING:
        case BuiltinKind::AVAILABLE:
            return true;
        default:
            return builtin_libcall(kind) != nullptr;
    }
}

void BuiltinRegistry::register_builtin(BuiltinInfo info) {
    info.syntax = builtin_syntax_kind(info.kind);
    info.supported = is_supported_builtin_kind(info.kind);
    builtins[info.name] = info;
}

BuiltinRegistry::BuiltinRegistry() {

    register_builtin({"__builtin_expect", BuiltinKind::EXPECT, 2, 2, false, false});
    register_builtin({"__builtin_constant_p", BuiltinKind::CONSTANT_P, 1, 1, false, true});
    register_builtin({"__builtin_unreachable", BuiltinKind::UNREACHABLE, 0, 0, false, false});
    register_builtin({"__builtin_trap", BuiltinKind::TRAP, 0, 0, false, false});
    register_builtin({"__builtin_types_compatible_p", BuiltinKind::TYPES_COMPATIBLE_P, 2, 2, true, true});
    register_builtin({"__builtin_choose_expr", BuiltinKind::CHOOSE_EXPR, 3, 3, true, false});
    register_builtin({"__builtin_object_size", BuiltinKind::OBJECT_SIZE, 2, 2, false, false});
    register_builtin({"__builtin_dynamic_object_size", BuiltinKind::DYNAMIC_OBJECT_SIZE, 2, 2, false, false});
    register_builtin({"__builtin_offsetof", BuiltinKind::OFFSETOF, 2, 2, true, true});
    register_builtin({"__builtin_available", BuiltinKind::AVAILABLE, 1, -1, false, false});
    register_builtin({"__builtin_is_constant_evaluated", BuiltinKind::IS_CONSTANT_EVALUATED, 0, 0, false, false});
    register_builtin({"__builtin_source_location", BuiltinKind::SOURCE_LOCATION, 0, 0, false, true});
    register_builtin({"__builtin_coro_done", BuiltinKind::CORO_DONE, 1, 1, false, false});
    register_builtin({"__builtin_coro_resume", BuiltinKind::CORO_RESUME, 1, 1, false, false});
    register_builtin({"__builtin_coro_destroy", BuiltinKind::CORO_DESTROY, 1, 1, false, false});
    register_builtin({"__builtin_coro_promise", BuiltinKind::CORO_PROMISE, 3, 3, false, false});
    register_builtin({"__is_same", BuiltinKind::IS_SAME, 2, 2, true, true});
    register_builtin({"__is_function", BuiltinKind::IS_FUNCTION, 1, 1, true, true});
    register_builtin({"__is_reference", BuiltinKind::IS_REFERENCE, 1, 1, true, true});
    register_builtin({"__is_lvalue_reference", BuiltinKind::IS_LVALUE_REFERENCE, 1, 1, true, true});
    register_builtin({"__is_rvalue_reference", BuiltinKind::IS_RVALUE_REFERENCE, 1, 1, true, true});
    register_builtin({"__has_virtual_destructor", BuiltinKind::HAS_VIRTUAL_DESTRUCTOR, 1, 1, true, true});
    register_builtin({"__is_abstract", BuiltinKind::IS_ABSTRACT, 1, 1, true, true});
    register_builtin({"__is_array", BuiltinKind::IS_ARRAY, 1, 1, true, true});
    register_builtin({"__is_bounded_array", BuiltinKind::IS_BOUNDED_ARRAY, 1, 1, true, true});
    register_builtin({"__is_union", BuiltinKind::IS_UNION, 1, 1, true, true});
    register_builtin({"__is_volatile", BuiltinKind::IS_VOLATILE, 1, 1, true, true});
    register_builtin({"__is_const", BuiltinKind::IS_CONST, 1, 1, true, true});
    register_builtin({"__is_empty", BuiltinKind::IS_EMPTY, 1, 1, true, true});
    register_builtin({"__is_enum", BuiltinKind::IS_ENUM, 1, 1, true, true});
    register_builtin({"__is_scoped_enum", BuiltinKind::IS_SCOPED_ENUM, 1, 1, true, true});
    register_builtin({"__is_fundamental", BuiltinKind::IS_FUNDAMENTAL, 1, 1, true, true});
    register_builtin({"__is_void", BuiltinKind::IS_VOID, 1, 1, true, true});
    register_builtin({"__is_integral", BuiltinKind::IS_INTEGRAL, 1, 1, true, true});
    register_builtin({"__is_floating_point", BuiltinKind::IS_FLOATING_POINT, 1, 1, true, true});
    register_builtin({"__is_arithmetic", BuiltinKind::IS_ARITHMETIC, 1, 1, true, true});
    register_builtin({"__is_scalar", BuiltinKind::IS_SCALAR, 1, 1, true, true});
    register_builtin({"__is_compound", BuiltinKind::IS_COMPOUND, 1, 1, true, true});
    register_builtin({"__is_unsigned", BuiltinKind::IS_UNSIGNED, 1, 1, true, true});
    register_builtin({"__is_assignable", BuiltinKind::IS_ASSIGNABLE, 2, 2, true, true});
    register_builtin({"__is_trivially_assignable", BuiltinKind::IS_TRIVIALLY_ASSIGNABLE, 2, 2, true, true});
    register_builtin({"__is_nothrow_assignable", BuiltinKind::IS_NOTHROW_ASSIGNABLE, 2, 2, true, true});
    register_builtin({"__is_base_of", BuiltinKind::IS_BASE_OF, 2, 2, true, true});
    register_builtin({"__is_class", BuiltinKind::IS_CLASS, 1, 1, true, true});
    register_builtin({"__is_final", BuiltinKind::IS_FINAL, 1, 1, true, true});
    register_builtin({"__is_aggregate", BuiltinKind::IS_AGGREGATE, 1, 1, true, true});
    register_builtin({"__is_member_pointer", BuiltinKind::IS_MEMBER_POINTER, 1, 1, true, true});
    register_builtin({"__is_member_object_pointer", BuiltinKind::IS_MEMBER_OBJECT_POINTER, 1, 1, true, true});
    register_builtin({"__is_member_function_pointer", BuiltinKind::IS_MEMBER_FUNCTION_POINTER, 1, 1, true, true});
    register_builtin({"__is_null_pointer", BuiltinKind::IS_NULL_POINTER, 1, 1, true, true});
    register_builtin({"__is_object", BuiltinKind::IS_OBJECT, 1, 1, true, true});
    register_builtin({"__is_pointer", BuiltinKind::IS_POINTER, 1, 1, true, true});
    register_builtin({"__is_polymorphic", BuiltinKind::IS_POLYMORPHIC, 1, 1, true, true});
    register_builtin({"__is_standard_layout", BuiltinKind::IS_STANDARD_LAYOUT, 1, 1, true, true});
    register_builtin({"__is_trivial", BuiltinKind::IS_TRIVIAL, 1, 1, true, true});
    register_builtin({"__is_trivially_copyable", BuiltinKind::IS_TRIVIALLY_COPYABLE, 1, 1, true, true});
    register_builtin({"__has_unique_object_representations", BuiltinKind::HAS_UNIQUE_OBJECT_REPRESENTATIONS, 1, 1, true, true});
    register_builtin({"__is_pod", BuiltinKind::IS_POD, 1, 1, true, true});
    register_builtin({"__is_signed", BuiltinKind::IS_SIGNED, 1, 1, true, true});
    register_builtin({"__is_constructible", BuiltinKind::IS_CONSTRUCTIBLE, 1, -1, true, true});
    register_builtin({"__is_trivially_constructible", BuiltinKind::IS_TRIVIALLY_CONSTRUCTIBLE, 1, -1, true, true});
    register_builtin({"__is_nothrow_constructible", BuiltinKind::IS_NOTHROW_CONSTRUCTIBLE, 1, -1, true, true});
    register_builtin({"__is_convertible", BuiltinKind::IS_CONVERTIBLE, 2, 2, true, true});
    register_builtin({"__is_core_convertible", BuiltinKind::IS_CORE_CONVERTIBLE, 2, 2, true, true});
    register_builtin({"__is_nothrow_convertible", BuiltinKind::IS_NOTHROW_CONVERTIBLE, 2, 2, true, true});
    register_builtin({"__reference_binds_to_temporary", BuiltinKind::REFERENCE_BINDS_TO_TEMPORARY, 2, 2, true, true});
    register_builtin({"__is_destructible", BuiltinKind::IS_DESTRUCTIBLE, 1, 1, true, true});
    register_builtin({"__is_nothrow_destructible", BuiltinKind::IS_NOTHROW_DESTRUCTIBLE, 1, 1, true, true});
    register_builtin({"__is_trivially_destructible", BuiltinKind::IS_TRIVIALLY_DESTRUCTIBLE, 1, 1, true, true});
    register_builtin({"__has_trivial_destructor", BuiltinKind::HAS_TRIVIAL_DESTRUCTOR, 1, 1, true, true});
    register_builtin({"__is_literal_type", BuiltinKind::IS_LITERAL_TYPE, 1, 1, true, true});
    register_builtin({"__integer_pack", BuiltinKind::INTEGER_PACK, 1, 1, false, true});
    register_builtin({"__make_integer_seq", BuiltinKind::MAKE_INTEGER_SEQ, 3, 3, true, true});
    register_builtin({"__type_pack_element", BuiltinKind::TYPE_PACK_ELEMENT, 2, -1, true, true});
    register_builtin({"__remove_const", BuiltinKind::REMOVE_CONST, 1, 1, true, true});
    register_builtin({"__remove_volatile", BuiltinKind::REMOVE_VOLATILE, 1, 1, true, true});
    register_builtin({"__remove_cv", BuiltinKind::REMOVE_CV, 1, 1, true, true});
    register_builtin({"__remove_cvref", BuiltinKind::REMOVE_CVREF, 1, 1, true, true});
    register_builtin({"__remove_reference_t", BuiltinKind::REMOVE_REFERENCE, 1, 1, true, true});
    register_builtin({"__underlying_type", BuiltinKind::UNDERLYING_TYPE, 1, 1, true, true});
    register_builtin({"__remove_extent", BuiltinKind::REMOVE_EXTENT, 1, 1, true, true});
    register_builtin({"__remove_all_extents", BuiltinKind::REMOVE_ALL_EXTENTS, 1, 1, true, true});
    register_builtin({"__add_lvalue_reference", BuiltinKind::ADD_LVALUE_REFERENCE, 1, 1, true, true});
    register_builtin({"__add_rvalue_reference", BuiltinKind::ADD_RVALUE_REFERENCE, 1, 1, true, true});
    register_builtin({"__add_pointer", BuiltinKind::ADD_POINTER, 1, 1, true, true});
    register_builtin({"__decay", BuiltinKind::DECAY, 1, 1, true, true});

    register_builtin({"__builtin_add_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_sub_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_mul_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_sadd_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_uadd_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_saddl_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_uaddl_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_saddll_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_uaddll_overflow", BuiltinKind::ADD_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_ssub_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_usub_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_ssubl_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_usubl_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_ssubll_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_usubll_overflow", BuiltinKind::SUB_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_smul_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_umul_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_smull_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_umull_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_smulll_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_umulll_overflow", BuiltinKind::MUL_OVERFLOW, 3, 3, false, false});
    register_builtin({"__builtin_add_overflow_p", BuiltinKind::ADD_OVERFLOW_P, 3, 3, false, false});
    register_builtin({"__builtin_sub_overflow_p", BuiltinKind::SUB_OVERFLOW_P, 3, 3, false, false});

    register_builtin({"__builtin_clz", BuiltinKind::CLZ, 1, 1, false, false});
    register_builtin({"__builtin_clzl", BuiltinKind::CLZL, 1, 1, false, false});
    register_builtin({"__builtin_clzll", BuiltinKind::CLZLL, 1, 1, false, false});
    register_builtin({"__builtin_clzg", BuiltinKind::CLZG, 1, 2, false, false});
    register_builtin({"__builtin_ctz", BuiltinKind::CTZ, 1, 1, false, false});
    register_builtin({"__builtin_ctzl", BuiltinKind::CTZL, 1, 1, false, false});
    register_builtin({"__builtin_ctzll", BuiltinKind::CTZLL, 1, 1, false, false});
    register_builtin({"__builtin_ctzg", BuiltinKind::CTZG, 1, 2, false, false});
    register_builtin({"__builtin_ffs", BuiltinKind::FFS, 1, 1, false, false});
    register_builtin({"__builtin_ffsl", BuiltinKind::FFSL, 1, 1, false, false});
    register_builtin({"__builtin_ffsll", BuiltinKind::FFSLL, 1, 1, false, false});
    register_builtin({"__builtin_popcount", BuiltinKind::POPCOUNT, 1, 1, false, false});
    register_builtin({"__builtin_popcountl", BuiltinKind::POPCOUNTL, 1, 1, false, false});
    register_builtin({"__builtin_popcountll", BuiltinKind::POPCOUNTLL, 1, 1, false, false});
    register_builtin({"__builtin_popcountg", BuiltinKind::POPCOUNTG, 1, 1, false, false});
    register_builtin({"__builtin_bswap16", BuiltinKind::BSWAP16, 1, 1, false, false});
    register_builtin({"__builtin_bswap32", BuiltinKind::BSWAP32, 1, 1, false, false});
    register_builtin({"__builtin_bswap64", BuiltinKind::BSWAP64, 1, 1, false, false});
    register_builtin({"__builtin_bit_cast", BuiltinKind::BIT_CAST, 2, 2, true, true});
    register_builtin({"__builtin_ia32_bzhi_si", BuiltinKind::IA32_BZHI_SI, 2, 2, false, false});

    register_builtin({"__builtin_addressof", BuiltinKind::ADDRESSOF, 1, 1, false, false});
    register_builtin({"__builtin_launder", BuiltinKind::LAUNDER, 1, 1, false, true});
    register_builtin({"__builtin_memcpy", BuiltinKind::MEMCPY, 3, 3, false, false});
    register_builtin({"__builtin_memmove", BuiltinKind::MEMMOVE, 3, 3, false, false});
    register_builtin({"__builtin_memset", BuiltinKind::MEMSET, 3, 3, false, false});
    register_builtin({"__builtin_memcmp", BuiltinKind::MEMCMP, 3, 3, false, false});
    register_builtin({"__builtin_memcmp_eq", BuiltinKind::MEMCMP_EQ, 3, 3, false, false});
    register_builtin({"__builtin_bcmp", BuiltinKind::MEMCMP, 3, 3, false, false});
    register_builtin({"__builtin_bcopy", BuiltinKind::BCOPY, 3, 3, false, false});
    register_builtin({"__builtin_bzero", BuiltinKind::BZERO, 2, 2, false, false});
    register_builtin({"__builtin_memchr", BuiltinKind::MEMCHR, 3, 3, false, false});
    register_builtin({"__builtin_strlen", BuiltinKind::STRLEN, 1, 1, false, false});
    register_builtin({"__builtin_strcpy", BuiltinKind::STRCPY, 2, 2, false, false});
    register_builtin({"__builtin_strncpy", BuiltinKind::STRNCPY, 3, 3, false, false});
    register_builtin({"__builtin_strcat", BuiltinKind::STRCAT, 2, 2, false, false});
    register_builtin({"__builtin_strncat", BuiltinKind::STRNCAT, 3, 3, false, false});
    register_builtin({"__builtin_strcspn", BuiltinKind::STRCSPN, 2, 2, false, false});
    register_builtin({"__builtin_strspn", BuiltinKind::STRSPN, 2, 2, false, false});
    register_builtin({"__builtin_strchr", BuiltinKind::STRCHR, 2, 2, false, false});
    register_builtin({"__builtin_strrchr", BuiltinKind::STRRCHR, 2, 2, false, false});
    register_builtin({"__builtin_strstr", BuiltinKind::STRSTR, 2, 2, false, false});
    register_builtin({"__builtin_strdup", BuiltinKind::STRDUP, 1, 1, false, false});
    register_builtin({"__builtin_stpncpy", BuiltinKind::STPNCPY, 3, 3, false, false});
    register_builtin({"__builtin_strndup", BuiltinKind::STRNDUP, 2, 2, false, false});
    register_builtin({"__builtin_strncasecmp", BuiltinKind::STRNCASECMP, 3, 3, false, false});
    register_builtin({"__builtin_strcmp", BuiltinKind::STRCMP, 2, 2, false, false});
    register_builtin({"__builtin_strncmp", BuiltinKind::STRNCMP, 3, 3, false, false});
    register_builtin({"__builtin_stpcpy", BuiltinKind::STPCPY, 2, 2, false, false});
    register_builtin({"__builtin_mempcpy", BuiltinKind::MEMPCPY, 3, 3, false, false});

    register_builtin({"__builtin___memcpy_chk", BuiltinKind::MEMCPY_CHK, 4, 4, false, false});
    register_builtin({"__builtin___memmove_chk", BuiltinKind::MEMMOVE_CHK, 4, 4, false, false});
    register_builtin({"__builtin___memset_chk", BuiltinKind::MEMSET_CHK, 4, 4, false, false});
    register_builtin({"__builtin___strncpy_chk", BuiltinKind::STRNCPY_CHK, 4, 4, false, false});
    register_builtin({"__builtin___strcpy_chk", BuiltinKind::STRCPY_CHK, 3, 3, false, false});
    register_builtin({"__builtin___stpcpy_chk", BuiltinKind::STPCPY_CHK, 3, 3, false, false});
    register_builtin({"__builtin___strcat_chk", BuiltinKind::STRCAT_CHK, 3, 3, false, false});
    register_builtin({"__builtin___strncat_chk", BuiltinKind::STRNCAT_CHK, 4, 4, false, false});

    register_builtin({"__builtin___sprintf_chk", BuiltinKind::SPRINTF_CHK, 4, -1, false, false});

    register_builtin({"__builtin___snprintf_chk", BuiltinKind::SNPRINTF_CHK, 5, -1, false, false});

    register_builtin({"__builtin___vsprintf_chk", BuiltinKind::VSPRINTF_CHK, 5, 5, false, false});

    register_builtin({"__builtin___vsnprintf_chk", BuiltinKind::VSNPRINTF_CHK, 6, 6, false, false});

    register_builtin({"__builtin___clear_cache", BuiltinKind::CLEAR_CACHE, 2, 2, false, false});
    register_builtin({"__builtin_clear_padding", BuiltinKind::CLEAR_PADDING, 1, 1, false, false});
    register_builtin({"__builtin_prefetch", BuiltinKind::PREFETCH, 1, 3, false, false});
    register_builtin({"__builtin_return_address", BuiltinKind::RETURN_ADDRESS, 1, 1, false, false});
    register_builtin({"__builtin_frame_address", BuiltinKind::FRAME_ADDRESS, 1, 1, false, false});
    register_builtin({"__builtin_extract_return_addr", BuiltinKind::EXTRACT_RETURN_ADDR, 1, 1, false, false});
    register_builtin({"__builtin_alloca", BuiltinKind::ALLOCA, 1, 1, false, false});
    register_builtin({"alloca", BuiltinKind::ALLOCA, 1, 1, false, false});
    register_builtin({"__builtin_stack_save", BuiltinKind::STACK_SAVE, 0, 0, false, false});
    register_builtin({"__builtin_stack_restore", BuiltinKind::STACK_RESTORE, 1, 1, false, false});

    register_builtin({"__builtin_flt_rounds", BuiltinKind::FLT_ROUNDS, 0, 0, false, true});
    register_builtin({"__builtin_isnan", BuiltinKind::ISNAN, 1, 1, false, false});
    register_builtin({"__builtin_isinf", BuiltinKind::ISINF, 1, 1, false, false});
    register_builtin({"__builtin_isinf_sign", BuiltinKind::ISINF_SIGN, 1, 1, false, false});
    register_builtin({"__builtin_isfinite", BuiltinKind::ISFINITE, 1, 1, false, false});
    register_builtin({"__builtin_isnormal", BuiltinKind::ISNORMAL, 1, 1, false, false});
    register_builtin({"__builtin_fpclassify", BuiltinKind::FPCLASSIFY, 6, 6, false, false});
    register_builtin({"__builtin_iseqsig", BuiltinKind::ISEQSIG, 2, 2, false, false});
    register_builtin({"__builtin_huge_val", BuiltinKind::BUILTIN_HUGE_VAL, 0, 0, false, true});
    register_builtin({"__builtin_huge_valf", BuiltinKind::BUILTIN_HUGE_VALF, 0, 0, false, true});
    register_builtin({"__builtin_inf", BuiltinKind::INF, 0, 0, false, true});
    register_builtin({"__builtin_inff", BuiltinKind::INFF, 0, 0, false, true});
    register_builtin({"__builtin_infl", BuiltinKind::INFL, 0, 0, false, true});
    register_builtin({"__builtin_huge_vall", BuiltinKind::BUILTIN_HUGE_VALL, 0, 0, false, true});
    register_builtin({"__builtin_nan", BuiltinKind::NAN_BUILTIN, 1, 1, false, true});
    register_builtin({"__builtin_nanf", BuiltinKind::NANF, 1, 1, false, true});
    register_builtin({"__builtin_nanl", BuiltinKind::NANL, 1, 1, false, true});
    register_builtin({"__builtin_nans", BuiltinKind::NANS, 1, 1, false, true});
    register_builtin({"__builtin_nansf", BuiltinKind::NANSF, 1, 1, false, true});
    register_builtin({"__builtin_nansl", BuiltinKind::NANSL, 1, 1, false, true});
    register_builtin({"__builtin_abs", BuiltinKind::ABS, 1, 1, false, false});
    register_builtin({"__builtin_labs", BuiltinKind::LABS, 1, 1, false, false});
    register_builtin({"__builtin_llabs", BuiltinKind::LLABS, 1, 1, false, false});
    register_builtin({"abs", BuiltinKind::ABS, 1, 1, false, false});
    register_builtin({"labs", BuiltinKind::LABS, 1, 1, false, false});
    register_builtin({"llabs", BuiltinKind::LLABS, 1, 1, false, false});
    register_builtin({"__builtin_fabs", BuiltinKind::FABS, 1, 1, false, false});
    register_builtin({"__builtin_fabsf", BuiltinKind::FABSF, 1, 1, false, false});
    register_builtin({"__builtin_fabsl", BuiltinKind::FABSL, 1, 1, false, false});
    register_builtin({"__builtin_complex", BuiltinKind::COMPLEX, 2, 2, false, false});
    register_builtin({"__builtin_conjf", BuiltinKind::CONJF, 1, 1, false, false});
    register_builtin({"__builtin_ilogb", BuiltinKind::ILOGB, 1, 1, false, false});
    register_builtin({"__builtin_ilogbf", BuiltinKind::ILOGBF, 1, 1, false, false});
    register_builtin({"__builtin_ilogbl", BuiltinKind::ILOGBL, 1, 1, false, false});

    register_builtin({"__builtin_pow", BuiltinKind::POW, 2, 2, false, false});
    register_builtin({"__builtin_powf", BuiltinKind::POWF, 2, 2, false, false});
    register_builtin({"__builtin_powl", BuiltinKind::POWL, 2, 2, false, false});
    register_builtin({"__builtin_cpow", BuiltinKind::CPOW, 2, 2, false, false});
    register_builtin({"__builtin_cexpi", BuiltinKind::CEXPI, 1, 1, false, false});
    register_builtin({"__builtin_sqrt", BuiltinKind::SQRT, 1, 1, false, false});
    register_builtin({"__builtin_sqrtf", BuiltinKind::SQRTF, 1, 1, false, false});
    register_builtin({"__builtin_sqrtl", BuiltinKind::SQRTL, 1, 1, false, false});
    register_builtin({"__builtin_cbrt", BuiltinKind::CBRT, 1, 1, false, false});
    register_builtin({"__builtin_cbrtf", BuiltinKind::CBRTF, 1, 1, false, false});
    register_builtin({"__builtin_cbrtl", BuiltinKind::CBRTL, 1, 1, false, false});
    register_builtin({"__builtin_sin", BuiltinKind::SIN, 1, 1, false, false});
    register_builtin({"__builtin_sinf", BuiltinKind::SINF, 1, 1, false, false});
    register_builtin({"__builtin_sinl", BuiltinKind::SINL, 1, 1, false, false});
    register_builtin({"__builtin_cos", BuiltinKind::COS, 1, 1, false, false});
    register_builtin({"__builtin_cosf", BuiltinKind::COSF, 1, 1, false, false});
    register_builtin({"__builtin_cosl", BuiltinKind::COSL, 1, 1, false, false});
    register_builtin({"__builtin_tan", BuiltinKind::TAN, 1, 1, false, false});
    register_builtin({"__builtin_tanf", BuiltinKind::TANF, 1, 1, false, false});
    register_builtin({"__builtin_tanl", BuiltinKind::TANL, 1, 1, false, false});
    register_builtin({"__builtin_asin", BuiltinKind::ASIN, 1, 1, false, false});
    register_builtin({"__builtin_asinf", BuiltinKind::ASINF, 1, 1, false, false});
    register_builtin({"__builtin_asinl", BuiltinKind::ASINL, 1, 1, false, false});
    register_builtin({"__builtin_acos", BuiltinKind::ACOS, 1, 1, false, false});
    register_builtin({"__builtin_acosf", BuiltinKind::ACOSF, 1, 1, false, false});
    register_builtin({"__builtin_acosl", BuiltinKind::ACOSL, 1, 1, false, false});
    register_builtin({"__builtin_atan", BuiltinKind::ATAN, 1, 1, false, false});
    register_builtin({"__builtin_atanf", BuiltinKind::ATANF, 1, 1, false, false});
    register_builtin({"__builtin_atanl", BuiltinKind::ATANL, 1, 1, false, false});
    register_builtin({"__builtin_atan2", BuiltinKind::ATAN2, 2, 2, false, false});
    register_builtin({"__builtin_atan2f", BuiltinKind::ATAN2F, 2, 2, false, false});
    register_builtin({"__builtin_atan2l", BuiltinKind::ATAN2L, 2, 2, false, false});
    register_builtin({"__builtin_sinh", BuiltinKind::SINH, 1, 1, false, false});
    register_builtin({"__builtin_sinhf", BuiltinKind::SINHF, 1, 1, false, false});
    register_builtin({"__builtin_sinhl", BuiltinKind::SINHL, 1, 1, false, false});
    register_builtin({"__builtin_cosh", BuiltinKind::COSH, 1, 1, false, false});
    register_builtin({"__builtin_coshf", BuiltinKind::COSHF, 1, 1, false, false});
    register_builtin({"__builtin_coshl", BuiltinKind::COSHL, 1, 1, false, false});
    register_builtin({"__builtin_tanh", BuiltinKind::TANH, 1, 1, false, false});
    register_builtin({"__builtin_tanhf", BuiltinKind::TANHF, 1, 1, false, false});
    register_builtin({"__builtin_tanhl", BuiltinKind::TANHL, 1, 1, false, false});
    register_builtin({"__builtin_asinh", BuiltinKind::ASINH, 1, 1, false, false});
    register_builtin({"__builtin_asinhf", BuiltinKind::ASINHF, 1, 1, false, false});
    register_builtin({"__builtin_asinhl", BuiltinKind::ASINHL, 1, 1, false, false});
    register_builtin({"__builtin_acosh", BuiltinKind::ACOSH, 1, 1, false, false});
    register_builtin({"__builtin_acoshf", BuiltinKind::ACOSHF, 1, 1, false, false});
    register_builtin({"__builtin_acoshl", BuiltinKind::ACOSHL, 1, 1, false, false});
    register_builtin({"__builtin_atanh", BuiltinKind::ATANH, 1, 1, false, false});
    register_builtin({"__builtin_atanhf", BuiltinKind::ATANHF, 1, 1, false, false});
    register_builtin({"__builtin_atanhl", BuiltinKind::ATANHL, 1, 1, false, false});
    register_builtin({"__builtin_log", BuiltinKind::LOG, 1, 1, false, false});
    register_builtin({"__builtin_logf", BuiltinKind::LOGF, 1, 1, false, false});
    register_builtin({"__builtin_logl", BuiltinKind::LOGL, 1, 1, false, false});
    register_builtin({"__builtin_log2", BuiltinKind::LOG2, 1, 1, false, false});
    register_builtin({"__builtin_log2f", BuiltinKind::LOG2F, 1, 1, false, false});
    register_builtin({"__builtin_log2l", BuiltinKind::LOG2L, 1, 1, false, false});
    register_builtin({"__builtin_log10", BuiltinKind::LOG10, 1, 1, false, false});
    register_builtin({"__builtin_log10f", BuiltinKind::LOG10F, 1, 1, false, false});
    register_builtin({"__builtin_log10l", BuiltinKind::LOG10L, 1, 1, false, false});
    register_builtin({"__builtin_log1p", BuiltinKind::LOG1P, 1, 1, false, false});
    register_builtin({"__builtin_log1pf", BuiltinKind::LOG1PF, 1, 1, false, false});
    register_builtin({"__builtin_log1pl", BuiltinKind::LOG1PL, 1, 1, false, false});
    register_builtin({"__builtin_logb", BuiltinKind::LOGB, 1, 1, false, false});
    register_builtin({"__builtin_logbf", BuiltinKind::LOGBF, 1, 1, false, false});
    register_builtin({"__builtin_logbl", BuiltinKind::LOGBL, 1, 1, false, false});
    register_builtin({"__builtin_exp", BuiltinKind::EXP, 1, 1, false, false});
    register_builtin({"__builtin_expf", BuiltinKind::EXPF, 1, 1, false, false});
    register_builtin({"__builtin_expl", BuiltinKind::EXPL, 1, 1, false, false});
    register_builtin({"__builtin_exp2", BuiltinKind::EXP2, 1, 1, false, false});
    register_builtin({"__builtin_exp2f", BuiltinKind::EXP2F, 1, 1, false, false});
    register_builtin({"__builtin_exp2l", BuiltinKind::EXP2L, 1, 1, false, false});
    register_builtin({"__builtin_expm1", BuiltinKind::EXPM1, 1, 1, false, false});
    register_builtin({"__builtin_expm1f", BuiltinKind::EXPM1F, 1, 1, false, false});
    register_builtin({"__builtin_expm1l", BuiltinKind::EXPM1L, 1, 1, false, false});
    register_builtin({"__builtin_frexp", BuiltinKind::FREXP, 2, 2, false, false});
    register_builtin({"__builtin_frexpf", BuiltinKind::FREXPF, 2, 2, false, false});
    register_builtin({"__builtin_frexpl", BuiltinKind::FREXPL, 2, 2, false, false});
    register_builtin({"__builtin_ldexp", BuiltinKind::LDEXP, 2, 2, false, false});
    register_builtin({"__builtin_ldexpf", BuiltinKind::LDEXPF, 2, 2, false, false});
    register_builtin({"__builtin_ldexpl", BuiltinKind::LDEXPL, 2, 2, false, false});
    register_builtin({"__builtin_scalbn", BuiltinKind::SCALBN, 2, 2, false, false});
    register_builtin({"__builtin_scalbnf", BuiltinKind::SCALBNF, 2, 2, false, false});
    register_builtin({"__builtin_scalbnl", BuiltinKind::SCALBNL, 2, 2, false, false});
    register_builtin({"__builtin_scalbln", BuiltinKind::SCALBLN, 2, 2, false, false});
    register_builtin({"__builtin_scalblnf", BuiltinKind::SCALBLNF, 2, 2, false, false});
    register_builtin({"__builtin_scalblnl", BuiltinKind::SCALBLNL, 2, 2, false, false});
    register_builtin({"__builtin_ceil", BuiltinKind::CEIL, 1, 1, false, false});
    register_builtin({"__builtin_ceilf", BuiltinKind::CEILF, 1, 1, false, false});
    register_builtin({"__builtin_ceill", BuiltinKind::CEILL, 1, 1, false, false});
    register_builtin({"__builtin_floor", BuiltinKind::FLOOR, 1, 1, false, false});
    register_builtin({"__builtin_floorf", BuiltinKind::FLOORF, 1, 1, false, false});
    register_builtin({"__builtin_floorl", BuiltinKind::FLOORL, 1, 1, false, false});
    register_builtin({"__builtin_round", BuiltinKind::ROUND, 1, 1, false, false});
    register_builtin({"__builtin_roundf", BuiltinKind::ROUNDF, 1, 1, false, false});
    register_builtin({"__builtin_roundl", BuiltinKind::ROUNDL, 1, 1, false, false});
    register_builtin({"__builtin_rint", BuiltinKind::RINT, 1, 1, false, false});
    register_builtin({"__builtin_rintf", BuiltinKind::RINTF, 1, 1, false, false});
    register_builtin({"__builtin_rintl", BuiltinKind::RINTL, 1, 1, false, false});
    register_builtin({"__builtin_nearbyint", BuiltinKind::NEARBYINT, 1, 1, false, false});
    register_builtin({"__builtin_nearbyintf", BuiltinKind::NEARBYINTF, 1, 1, false, false});
    register_builtin({"__builtin_nearbyintl", BuiltinKind::NEARBYINTL, 1, 1, false, false});
    register_builtin({"__builtin_lrint", BuiltinKind::LRINT, 1, 1, false, false});
    register_builtin({"__builtin_lrintf", BuiltinKind::LRINTF, 1, 1, false, false});
    register_builtin({"__builtin_lrintl", BuiltinKind::LRINTL, 1, 1, false, false});
    register_builtin({"__builtin_lround", BuiltinKind::LROUND, 1, 1, false, false});
    register_builtin({"__builtin_lroundf", BuiltinKind::LROUNDF, 1, 1, false, false});
    register_builtin({"__builtin_lroundl", BuiltinKind::LROUNDL, 1, 1, false, false});
    register_builtin({"__builtin_llrint", BuiltinKind::LLRINT, 1, 1, false, false});
    register_builtin({"__builtin_llrintf", BuiltinKind::LLRINTF, 1, 1, false, false});
    register_builtin({"__builtin_llrintl", BuiltinKind::LLRINTL, 1, 1, false, false});
    register_builtin({"__builtin_llround", BuiltinKind::LLROUND, 1, 1, false, false});
    register_builtin({"__builtin_llroundf", BuiltinKind::LLROUNDF, 1, 1, false, false});
    register_builtin({"__builtin_llroundl", BuiltinKind::LLROUNDL, 1, 1, false, false});
    register_builtin({"__builtin_copysign", BuiltinKind::COPYSIGN, 2, 2, false, false});
    register_builtin({"__builtin_copysignf", BuiltinKind::COPYSIGNF, 2, 2, false, false});
    register_builtin({"__builtin_copysignl", BuiltinKind::COPYSIGNL, 2, 2, false, false});
    register_builtin({"__builtin_hypot", BuiltinKind::HYPOT, 2, 2, false, false});
    register_builtin({"__builtin_hypotf", BuiltinKind::HYPOTF, 2, 2, false, false});
    register_builtin({"__builtin_hypotl", BuiltinKind::HYPOTL, 2, 2, false, false});
    register_builtin({"__builtin_fmin", BuiltinKind::FMIN, 2, 2, false, false});
    register_builtin({"__builtin_fminf", BuiltinKind::FMINF, 2, 2, false, false});
    register_builtin({"__builtin_fminl", BuiltinKind::FMINL, 2, 2, false, false});
    register_builtin({"__builtin_fmax", BuiltinKind::FMAX, 2, 2, false, false});
    register_builtin({"__builtin_fmaxf", BuiltinKind::FMAXF, 2, 2, false, false});
    register_builtin({"__builtin_fmaxl", BuiltinKind::FMAXL, 2, 2, false, false});
    register_builtin({"__builtin_fdim", BuiltinKind::FDIM, 2, 2, false, false});
    register_builtin({"__builtin_fdimf", BuiltinKind::FDIMF, 2, 2, false, false});
    register_builtin({"__builtin_fdiml", BuiltinKind::FDIML, 2, 2, false, false});
    register_builtin({"__builtin_fma", BuiltinKind::FMA, 3, 3, false, false});
    register_builtin({"__builtin_fmaf", BuiltinKind::FMAF, 3, 3, false, false});
    register_builtin({"__builtin_fmal", BuiltinKind::FMAL, 3, 3, false, false});
    register_builtin({"__builtin_fmod", BuiltinKind::FMOD, 2, 2, false, false});
    register_builtin({"__builtin_fmodf", BuiltinKind::FMODF, 2, 2, false, false});
    register_builtin({"__builtin_fmodl", BuiltinKind::FMODL, 2, 2, false, false});
    register_builtin({"__builtin_remainder", BuiltinKind::REMAINDER, 2, 2, false, false});
    register_builtin({"__builtin_remainderf", BuiltinKind::REMAINDERF, 2, 2, false, false});
    register_builtin({"__builtin_remainderl", BuiltinKind::REMAINDERL, 2, 2, false, false});
    register_builtin({"__builtin_remquo", BuiltinKind::REMQUO, 3, 3, false, false});
    register_builtin({"__builtin_remquof", BuiltinKind::REMQUOF, 3, 3, false, false});
    register_builtin({"__builtin_remquol", BuiltinKind::REMQUOL, 3, 3, false, false});
    register_builtin({"__builtin_nextafter", BuiltinKind::NEXTAFTER, 2, 2, false, false});
    register_builtin({"__builtin_nextafterf", BuiltinKind::NEXTAFTERF, 2, 2, false, false});
    register_builtin({"__builtin_nextafterl", BuiltinKind::NEXTAFTERL, 2, 2, false, false});
    register_builtin({"__builtin_nexttoward", BuiltinKind::NEXTTOWARD, 2, 2, false, false});
    register_builtin({"__builtin_nexttowardf", BuiltinKind::NEXTTOWARDF, 2, 2, false, false});
    register_builtin({"__builtin_nexttowardl", BuiltinKind::NEXTTOWARDL, 2, 2, false, false});
    register_builtin({"__builtin_erf", BuiltinKind::ERF, 1, 1, false, false});
    register_builtin({"__builtin_erff", BuiltinKind::ERFF, 1, 1, false, false});
    register_builtin({"__builtin_erfl", BuiltinKind::ERFL, 1, 1, false, false});
    register_builtin({"__builtin_erfc", BuiltinKind::ERFC, 1, 1, false, false});
    register_builtin({"__builtin_erfcf", BuiltinKind::ERFCF, 1, 1, false, false});
    register_builtin({"__builtin_erfcl", BuiltinKind::ERFCL, 1, 1, false, false});
    register_builtin({"__builtin_lgamma", BuiltinKind::LGAMMA, 1, 1, false, false});
    register_builtin({"__builtin_lgammaf", BuiltinKind::LGAMMAF, 1, 1, false, false});
    register_builtin({"__builtin_lgammal", BuiltinKind::LGAMMAL, 1, 1, false, false});
    register_builtin({"__builtin_tgamma", BuiltinKind::TGAMMA, 1, 1, false, false});
    register_builtin({"__builtin_tgammaf", BuiltinKind::TGAMMAF, 1, 1, false, false});
    register_builtin({"__builtin_tgammal", BuiltinKind::TGAMMAL, 1, 1, false, false});

    register_builtin({"__builtin_modf", BuiltinKind::MODF, 2, 2, false, false});
    register_builtin({"__builtin_modff", BuiltinKind::MODFF, 2, 2, false, false});
    register_builtin({"__builtin_modfl", BuiltinKind::MODFL, 2, 2, false, false});
    register_builtin({"__builtin_trunc", BuiltinKind::TRUNC, 1, 1, false, false});
    register_builtin({"__builtin_truncf", BuiltinKind::TRUNCF, 1, 1, false, false});
    register_builtin({"__builtin_truncl", BuiltinKind::TRUNCL, 1, 1, false, false});

    register_builtin({"__builtin_signbit", BuiltinKind::SIGNBIT, 1, 1, false, false});
    register_builtin({"__builtin_signbitf", BuiltinKind::SIGNBITF, 1, 1, false, false});
    register_builtin({"__builtin_signbitl", BuiltinKind::SIGNBITL, 1, 1, false, false});

    register_builtin({"__builtin_assume_aligned", BuiltinKind::ASSUME_ALIGNED, 2, 3, false, false});
    register_builtin({"__builtin_classify_type", BuiltinKind::CLASSIFY_TYPE, 1, 1, false, true});
    register_builtin({"__builtin_expect_with_probability", BuiltinKind::EXPECT_WITH_PROBABILITY, 3, 3, false, false});
    register_builtin({"__builtin_FILE", BuiltinKind::BUILTIN_FILE, 0, 0, false, true});
    register_builtin({"__builtin_LINE", BuiltinKind::BUILTIN_LINE, 0, 0, false, true});
    register_builtin({"__builtin_FUNCTION", BuiltinKind::BUILTIN_FUNCTION, 0, 0, false, true});
    register_builtin({"__builtin_clrsb", BuiltinKind::CLRSB, 1, 1, false, false});
    register_builtin({"__builtin_clrsbl", BuiltinKind::CLRSBL, 1, 1, false, false});
    register_builtin({"__builtin_clrsbll", BuiltinKind::CLRSBLL, 1, 1, false, false});
    register_builtin({"__builtin_parity", BuiltinKind::PARITY, 1, 1, false, false});
    register_builtin({"__builtin_parityl", BuiltinKind::PARITYL, 1, 1, false, false});
    register_builtin({"__builtin_parityll", BuiltinKind::PARITYLL, 1, 1, false, false});
    register_builtin({"__builtin_convertvector", BuiltinKind::CONVERTVECTOR, 2, 2, true, false});
    register_builtin({"__builtin_reduce_and", BuiltinKind::REDUCE_AND, 1, 1, false, false});
    register_builtin({"__builtin_shufflevector", BuiltinKind::SHUFFLEVECTOR, 2, -1, false, false});
    register_builtin({"__builtin_va_start", BuiltinKind::VA_START, 2, 2, false, false});
    register_builtin({"__builtin_va_arg", BuiltinKind::VA_ARG, 2, 2, true, false});
    register_builtin({"__builtin_va_end", BuiltinKind::VA_END, 1, 1, false, false});
    register_builtin({"__builtin_va_copy", BuiltinKind::VA_COPY, 2, 2, false, false});
    register_builtin({"__builtin_va_arg_pack", BuiltinKind::VA_ARG_PACK, 0, 0, false, false});

    register_builtin({"__atomic_load", BuiltinKind::ATOMIC_LOAD_N, 3, 3, false, false});
    register_builtin({"__atomic_load_n", BuiltinKind::ATOMIC_LOAD_N, 2, 2, false, false});
    register_builtin({"__atomic_store", BuiltinKind::ATOMIC_STORE_N, 3, 3, false, false});
    register_builtin({"__atomic_store_n", BuiltinKind::ATOMIC_STORE_N, 3, 3, false, false});
    register_builtin({"__atomic_exchange", BuiltinKind::ATOMIC_EXCHANGE_N, 4, 4, false, false});
    register_builtin({"__atomic_exchange_n", BuiltinKind::ATOMIC_EXCHANGE_N, 3, 3, false, false});
    register_builtin({"__atomic_compare_exchange", BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N, 6, 6, false, false});
    register_builtin({"__atomic_compare_exchange_n", BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N, 6, 6, false, false});
    register_builtin({"__atomic_is_lock_free", BuiltinKind::ATOMIC_IS_LOCK_FREE, 2, 2, false, false});
    register_builtin({"__atomic_always_lock_free", BuiltinKind::ATOMIC_ALWAYS_LOCK_FREE, 2, 2, false, true});
    register_builtin({"__atomic_fetch_add", BuiltinKind::ATOMIC_FETCH_ADD, 3, 3, false, false});
    register_builtin({"__atomic_fetch_sub", BuiltinKind::ATOMIC_FETCH_SUB, 3, 3, false, false});
    register_builtin({"__atomic_fetch_and", BuiltinKind::ATOMIC_FETCH_AND, 3, 3, false, false});
    register_builtin({"__atomic_fetch_or", BuiltinKind::ATOMIC_FETCH_OR, 3, 3, false, false});
    register_builtin({"__atomic_fetch_xor", BuiltinKind::ATOMIC_FETCH_XOR, 3, 3, false, false});
    register_builtin({"__atomic_fetch_nand", BuiltinKind::ATOMIC_FETCH_NAND, 3, 3, false, false});
    register_builtin({"__atomic_add_fetch", BuiltinKind::ATOMIC_ADD_FETCH, 3, 3, false, false});
    register_builtin({"__atomic_sub_fetch", BuiltinKind::ATOMIC_SUB_FETCH, 3, 3, false, false});
    register_builtin({"__atomic_and_fetch", BuiltinKind::ATOMIC_AND_FETCH, 3, 3, false, false});
    register_builtin({"__atomic_or_fetch", BuiltinKind::ATOMIC_OR_FETCH, 3, 3, false, false});
    register_builtin({"__atomic_xor_fetch", BuiltinKind::ATOMIC_XOR_FETCH, 3, 3, false, false});
    register_builtin({"__atomic_nand_fetch", BuiltinKind::ATOMIC_NAND_FETCH, 3, 3, false, false});
    register_builtin({"__atomic_thread_fence", BuiltinKind::ATOMIC_THREAD_FENCE, 1, 1, false, false});
    register_builtin({"__atomic_signal_fence", BuiltinKind::ATOMIC_SIGNAL_FENCE, 1, 1, false, false});
    register_builtin({"__atomic_test_and_set", BuiltinKind::ATOMIC_TEST_AND_SET, 2, 2, false, false});
    register_builtin({"__atomic_clear", BuiltinKind::ATOMIC_CLEAR, 2, 2, false, false});

    register_builtin({"__c11_atomic_init", BuiltinKind::C11_ATOMIC_INIT, 2, 2, false, false});
    register_builtin({"__c11_atomic_is_lock_free", BuiltinKind::ATOMIC_IS_LOCK_FREE, 1, 1, false, false});
    register_builtin({"__c11_atomic_thread_fence", BuiltinKind::ATOMIC_THREAD_FENCE, 1, 1, false, false});
    register_builtin({"__c11_atomic_signal_fence", BuiltinKind::ATOMIC_SIGNAL_FENCE, 1, 1, false, false});
    register_builtin({"__c11_atomic_load", BuiltinKind::ATOMIC_LOAD_N, 2, 2, false, false});
    register_builtin({"__c11_atomic_store", BuiltinKind::ATOMIC_STORE_N, 3, 3, false, false});
    register_builtin({"__c11_atomic_exchange", BuiltinKind::ATOMIC_EXCHANGE_N, 3, 3, false, false});
    register_builtin({"__c11_atomic_compare_exchange_strong", BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N, 5, 5, false, false});
    register_builtin({"__c11_atomic_compare_exchange_weak", BuiltinKind::ATOMIC_COMPARE_EXCHANGE_N, 5, 5, false, false});
    register_builtin({"__c11_atomic_fetch_add", BuiltinKind::C11_ATOMIC_FETCH_ADD, 3, 3, false, false});
    register_builtin({"__c11_atomic_fetch_sub", BuiltinKind::C11_ATOMIC_FETCH_SUB, 3, 3, false, false});
    register_builtin({"__c11_atomic_fetch_or", BuiltinKind::ATOMIC_FETCH_OR, 3, 3, false, false});
    register_builtin({"__c11_atomic_fetch_xor", BuiltinKind::ATOMIC_FETCH_XOR, 3, 3, false, false});
    register_builtin({"__c11_atomic_fetch_and", BuiltinKind::ATOMIC_FETCH_AND, 3, 3, false, false});

    register_builtin({"__sync_fetch_and_add", BuiltinKind::SYNC_FETCH_AND_ADD, 2, 2, false, false});
    register_builtin({"__sync_fetch_and_sub", BuiltinKind::SYNC_FETCH_AND_SUB, 2, 2, false, false});
    register_builtin({"__sync_fetch_and_or", BuiltinKind::SYNC_FETCH_AND_OR, 2, 2, false, false});
    register_builtin({"__sync_fetch_and_and", BuiltinKind::SYNC_FETCH_AND_AND, 2, 2, false, false});
    register_builtin({"__sync_fetch_and_xor", BuiltinKind::SYNC_FETCH_AND_XOR, 2, 2, false, false});
    register_builtin({"__sync_fetch_and_nand", BuiltinKind::SYNC_FETCH_AND_NAND, 2, 2, false, false});
    register_builtin({"__sync_add_and_fetch", BuiltinKind::SYNC_ADD_AND_FETCH, 2, 2, false, false});
    register_builtin({"__sync_sub_and_fetch", BuiltinKind::SYNC_SUB_AND_FETCH, 2, 2, false, false});
    register_builtin({"__sync_or_and_fetch", BuiltinKind::SYNC_OR_AND_FETCH, 2, 2, false, false});
    register_builtin({"__sync_and_and_fetch", BuiltinKind::SYNC_AND_AND_FETCH, 2, 2, false, false});
    register_builtin({"__sync_xor_and_fetch", BuiltinKind::SYNC_XOR_AND_FETCH, 2, 2, false, false});
    register_builtin({"__sync_nand_and_fetch", BuiltinKind::SYNC_NAND_AND_FETCH, 2, 2, false, false});
    register_builtin({"__sync_bool_compare_and_swap", BuiltinKind::SYNC_BOOL_COMPARE_AND_SWAP, 3, 3, false, false});
    register_builtin({"__sync_val_compare_and_swap", BuiltinKind::SYNC_VAL_COMPARE_AND_SWAP, 3, 3, false, false});
    register_builtin({"__sync_synchronize", BuiltinKind::SYNC_SYNCHRONIZE, 0, 0, false, false});
    register_builtin({"__sync_lock_test_and_set", BuiltinKind::SYNC_LOCK_TEST_AND_SET, 2, -1, false, false});
    register_builtin({"__sync_lock_release", BuiltinKind::SYNC_LOCK_RELEASE, 1, -1, false, false});

    register_builtin({"__builtin_printf", BuiltinKind::PRINTF, 1, -1, false, false});
    register_builtin({"__builtin_puts", BuiltinKind::PUTS, 1, 1, false, false});
    register_builtin({"__builtin_putchar", BuiltinKind::PUTCHAR, 1, 1, false, false});
    register_builtin({"__builtin_fprintf", BuiltinKind::FPRINTF, 2, -1, false, false});
    register_builtin({"__builtin_sprintf", BuiltinKind::SPRINTF, 2, -1, false, false});
    register_builtin({"__builtin_snprintf", BuiltinKind::SNPRINTF, 3, -1, false, false});

    register_builtin({"__builtin_isunordered", BuiltinKind::ISUNORDERED, 2, 2, false, false});
    register_builtin({"__builtin_isless", BuiltinKind::ISLESS, 2, 2, false, false});
    register_builtin({"__builtin_islessequal", BuiltinKind::ISLESSEQUAL, 2, 2, false, false});
    register_builtin({"__builtin_isgreater", BuiltinKind::ISGREATER, 2, 2, false, false});
    register_builtin({"__builtin_isgreaterequal", BuiltinKind::ISGREATEREQUAL, 2, 2, false, false});
    register_builtin({"__builtin_islessgreater", BuiltinKind::ISLESSGREATER, 2, 2, false, false});

    register_builtin({"__builtin_malloc", BuiltinKind::MALLOC, 1, 1, false, false});
    register_builtin({"__builtin_calloc", BuiltinKind::CALLOC, 2, 2, false, false});
    register_builtin({"__builtin_realloc", BuiltinKind::REALLOC, 2, 2, false, false});
    register_builtin({"__builtin_free", BuiltinKind::FREE, 1, 1, false, false});
    register_builtin({"__builtin_operator_new", BuiltinKind::OPERATOR_NEW, 1, -1, false, false});
    register_builtin({"__builtin_operator_delete", BuiltinKind::OPERATOR_DELETE, 1, -1, false, false});

    register_builtin({"__metafn_query_int", BuiltinKind::METAFN_QUERY_INT, 2, 3, false, false});
    register_builtin({"__metafn_query_info", BuiltinKind::METAFN_QUERY_INFO, 2, 3, false, false});
    register_builtin({"__metafn_name_data", BuiltinKind::METAFN_NAME_DATA, 2, 2, false, false});
    register_builtin({"__metafn_name_size", BuiltinKind::METAFN_NAME_SIZE, 2, 2, false, false});
    register_builtin({"__metafn_range_count", BuiltinKind::METAFN_RANGE_COUNT, 2, 2, false, false});
    register_builtin({"__metafn_range_at", BuiltinKind::METAFN_RANGE_AT, 3, 3, false, false});

    register_builtin({"__builtin_abort", BuiltinKind::ABORT, 0, 0, false, false});
    register_builtin({"__builtin_exit", BuiltinKind::EXIT, 1, 1, false, false});
}
