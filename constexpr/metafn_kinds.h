#ifndef ABURI_METAFN_KINDS_H
#define ABURI_METAFN_KINDS_H

#include <cstdint>

enum class MetafnIntQuery : int64_t {
    SizeOf = 0,
    AlignOf = 1,
    OffsetOf = 2,
    BitOffsetOf = 3,
    BitSizeOf = 4,
    IsType = 10,
    IsNamespace = 11,
    IsTemplate = 12,
    IsFunction = 13,
    IsVariable = 14,
    IsEnumerator = 15,
    IsNonstaticDataMember = 16,
    IsStaticDataMember = 17,
    IsClassType = 18,
    IsUnionType = 19,
    IsEnumType = 20,
    IsConstructor = 21,
    IsDestructor = 22,
    IsValue = 23,
    TypeIsIntegral = 40,
    TypeIsFloatingPoint = 41,
    TypeIsPointer = 42,
    TypeIsLValueReference = 43,
    TypeIsRValueReference = 44,
    TypeIsReference = 45,
    TypeIsArithmetic = 46,
    TypeIsConst = 47,
    TypeIsVolatile = 48,
    TypeIsFunction = 49,
    TypeIsArray = 50,
    TypeIsScalar = 51,
    TypeIsSame = 52,
};

enum class MetafnInfoQuery : int64_t {
    TypeOf = 0,
    ParentOf = 1,
    Dealias = 2,
    RemoveConst = 10,
    RemoveVolatile = 11,
    RemoveCv = 12,
    AddConst = 13,
    AddVolatile = 14,
    AddCv = 15,
    AddPointer = 16,
    RemovePointer = 17,
    RemoveReference = 18,
    AddLValueReference = 19,
    AddRValueReference = 20,
    RemoveCvref = 21,
};

enum class MetafnNameQuery : int64_t {
    NameOf = 0,
    QualifiedNameOf = 1,
    DisplayNameOf = 2,
};

enum class MetafnRangeQuery : int64_t {
    MembersOf = 0,
    NonstaticDataMembersOf = 1,
    StaticDataMembersOf = 2,
    BasesOf = 3,
    EnumeratorsOf = 4,
};

#endif // ABURI_METAFN_KINDS_H
