#include <__adinkra/fstream>
#include <ios>

#include <stdio.h>

_ADINKRA_BEGIN_NAMESPACE_STD

namespace __fstream {

namespace {

const char* fopen_mode(unsigned int mode) noexcept {
    const bool input = (mode & ios_base::in) != 0;
    const bool output = (mode & ios_base::out) != 0;
    const bool append = (mode & ios_base::app) != 0;
    const bool truncate = (mode & ios_base::trunc) != 0;
    const bool binary = (mode & ios_base::binary) != 0;

    if (input && output) {
        if (append) {
            return binary ? "a+b" : "a+";
        }
        if (truncate) {
            return binary ? "w+b" : "w+";
        }
        return binary ? "r+b" : "r+";
    }
    if (output) {
        if (append) {
            return binary ? "ab" : "a";
        }
        return binary ? "wb" : "w";
    }
    return binary ? "rb" : "r";
}

} // namespace

void* open(const char* filename, unsigned int mode) noexcept {
    if (filename == nullptr) {
        return nullptr;
    }
    FILE* stream = ::fopen(filename, fopen_mode(mode));
    if (stream != nullptr && (mode & ios_base::ate) != 0 &&
        ::fseeko(stream, 0, SEEK_END) != 0) {
        ::fclose(stream);
        return nullptr;
    }
    return stream;
}

bool close(void* stream) noexcept {
    return stream != nullptr &&
           ::fclose(static_cast<FILE*>(stream)) == 0;
}

} // namespace __fstream

_ADINKRA_END_NAMESPACE_STD
