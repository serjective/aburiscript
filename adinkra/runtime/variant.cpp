#include <variant>

_ADINKRA_BEGIN_NAMESPACE_STD

const char* bad_variant_access::what() const noexcept {
    return "bad_variant_access";
}

void __throw_bad_variant_access() {
    throw bad_variant_access();
}

_ADINKRA_END_NAMESPACE_STD
