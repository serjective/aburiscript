#ifndef ADINKRA_CXXABI_H
#define ADINKRA_CXXABI_H

#include <cstddef>

namespace __cxxabiv1 {

extern "C" char* __cxa_demangle(
    const char* mangled_name,
    char* output_buffer,
    std::size_t* length,
    int* status);

} // namespace __cxxabiv1

namespace abi = __cxxabiv1;

#endif
