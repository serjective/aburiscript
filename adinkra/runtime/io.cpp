#include <__adinkra/io>
#include <iostream>

#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

_ADINKRA_BEGIN_NAMESPACE_STD

namespace __io {

struct ios_word_storage {
    struct entry {
        long integer = 0;
        void* pointer = nullptr;
    };

    entry* entries = nullptr;
    size_t size = 0;
};

namespace {

FILE* as_file(void* stream) noexcept {
    return static_cast<FILE*>(stream);
}

ios_word_storage::entry& ensure_word(
    ios_word_storage*& storage, int index) {
    static ios_word_storage::entry invalid;
    if (index < 0) {
        return invalid;
    }

    const size_t requested = static_cast<size_t>(index) + 1;
    if (storage == nullptr) {
        storage = new ios_word_storage;
    }
    if (requested <= storage->size) {
        return storage->entries[index];
    }

    size_t capacity = storage->size == 0 ? 4 : storage->size;
    while (capacity < requested) {
        capacity =
            capacity > static_cast<size_t>(-1) / 2
                ? requested
                : capacity * 2;
    }
    auto* replacement = new ios_word_storage::entry[capacity]{};
    for (size_t position = 0; position < storage->size; ++position) {
        replacement[position] = storage->entries[position];
    }
    delete[] storage->entries;
    storage->entries = replacement;
    storage->size = capacity;
    return storage->entries[index];
}

bool write_buffer(void* stream, const char* buffer, int count) noexcept {
    return stream != nullptr && count >= 0 &&
           ::fwrite(
               buffer, 1, static_cast<size_t>(count),
               as_file(stream)) == static_cast<size_t>(count);
}

} // namespace

int ios_xalloc() noexcept {
    static int next_index = 0;
    return __atomic_fetch_add(
        &next_index, 1, __ATOMIC_RELAXED);
}

void ios_storage_destroy(ios_word_storage* storage) noexcept {
    if (storage != nullptr) {
        delete[] storage->entries;
        delete storage;
    }
}

ios_word_storage* ios_storage_copy(
    const ios_word_storage* storage) {
    if (storage == nullptr) {
        return nullptr;
    }

    auto* result = new ios_word_storage;
    try {
        if (storage->size != 0) {
            result->entries =
                new ios_word_storage::entry[storage->size]{};
            result->size = storage->size;
            for (size_t position = 0;
                 position < storage->size; ++position) {
                result->entries[position] =
                    storage->entries[position];
            }
        }
    } catch (...) {
        ios_storage_destroy(result);
        throw;
    }
    return result;
}

long& ios_iword(ios_word_storage*& storage, int index) {
    return ensure_word(storage, index).integer;
}

void*& ios_pword(ios_word_storage*& storage, int index) {
    return ensure_word(storage, index).pointer;
}

bool write(void* stream, const char* value, size_t count) noexcept {
    if (stream == nullptr) {
        return false;
    }
    return ::fwrite(value, 1, count, as_file(stream)) == count;
}

bool put(void* stream, char value) noexcept {
    if (stream == nullptr) {
        return false;
    }
    return ::fputc(
               static_cast<unsigned char>(value),
               as_file(stream)) != EOF;
}

bool flush(void* stream) noexcept {
    if (stream == nullptr) {
        return false;
    }
    return ::fflush(as_file(stream)) == 0;
}

bool write_signed(
    void* stream, long long value, int base,
    bool uppercase_value, bool show_base,
    bool show_positive) noexcept {
    char format[8] = {'%', '\0', '\0', '\0', '\0', '\0', '\0', '\0'};
    int position = 1;
    if (show_positive) {
        format[position++] = '+';
    }
    if (show_base) {
        format[position++] = '#';
    }
    format[position++] = 'l';
    format[position++] = 'l';
    format[position++] =
        base == 16 ? (uppercase_value ? 'X' : 'x')
      : base == 8  ? 'o'
                   : 'd';
    format[position] = '\0';

    char buffer[96];
    const int count = ::snprintf(
        buffer, sizeof(buffer), format, value);
    return write_buffer(stream, buffer, count);
}

bool write_unsigned(
    void* stream, unsigned long long value, int base,
    bool uppercase_value, bool show_base,
    bool show_positive) noexcept {
    char format[8] = {'%', '\0', '\0', '\0', '\0', '\0', '\0', '\0'};
    int position = 1;
    if (show_positive) {
        format[position++] = '+';
    }
    if (show_base) {
        format[position++] = '#';
    }
    format[position++] = 'l';
    format[position++] = 'l';
    format[position++] =
        base == 16 ? (uppercase_value ? 'X' : 'x')
      : base == 8  ? 'o'
                   : 'u';
    format[position] = '\0';

    char buffer[96];
    const int count = ::snprintf(
        buffer, sizeof(buffer), format, value);
    return write_buffer(stream, buffer, count);
}

bool write_floating(
    void* stream, long double value, int precision,
    bool uppercase_value, bool scientific_value, bool fixed_value,
    bool show_point, bool show_positive) noexcept {
    char format[16] = {'%', '\0'};
    int position = 1;
    if (show_positive) {
        format[position++] = '+';
    }
    if (show_point) {
        format[position++] = '#';
    }
    format[position++] = '.';
    format[position++] = '*';
    format[position++] = 'L';
    format[position++] =
        scientific_value && fixed_value
            ? (uppercase_value ? 'A' : 'a')
      : scientific_value ? (uppercase_value ? 'E' : 'e')
      : fixed_value      ? (uppercase_value ? 'F' : 'f')
                         : (uppercase_value ? 'G' : 'g');
    format[position] = '\0';

    char buffer[256];
    const int count = ::snprintf(
        buffer, sizeof(buffer), format, precision, value);
    return write_buffer(stream, buffer, count);
}

bool write_pointer(
    void* stream, const void* value, bool uppercase_value) noexcept {
    char buffer[64];
    int count = ::snprintf(buffer, sizeof(buffer), "%p", value);
    if (uppercase_value && count > 0) {
        for (int index = 0; index < count; ++index) {
            buffer[index] = static_cast<char>(
                ::toupper(
                    static_cast<unsigned char>(buffer[index])));
        }
    }
    return write_buffer(stream, buffer, count);
}

int get(void* stream) noexcept {
    if (stream == nullptr) {
        return EOF;
    }
    return ::fgetc(as_file(stream));
}

bool unget(void* stream, char value) noexcept {
    if (stream == nullptr) {
        return false;
    }
    return ::ungetc(
               static_cast<unsigned char>(value),
               as_file(stream)) != EOF;
}

bool skip_whitespace(void* stream) noexcept {
    for (;;) {
        const int value = get(stream);
        if (value == EOF) {
            return false;
        }
        if (!::isspace(static_cast<unsigned char>(value))) {
            return unget(stream, static_cast<char>(value));
        }
    }
}

bool read_token(
    void* stream, char* destination, size_t capacity) noexcept {
    if (capacity == 0) {
        return false;
    }
    size_t size = 0;
    for (;;) {
        const int value = get(stream);
        if (value == EOF ||
            ::isspace(static_cast<unsigned char>(value))) {
            break;
        }
        if (size + 1 >= capacity) {
            destination[capacity - 1] = '\0';
            return false;
        }
        destination[size++] = static_cast<char>(value);
    }
    destination[size] = '\0';
    return size != 0;
}

bool read_signed(void* stream, long long& value, int base) noexcept {
    char token[128];
    if (!read_token(stream, token, sizeof(token))) {
        return false;
    }
    char* end = nullptr;
    errno = 0;
    const long long parsed = ::strtoll(token, &end, base);
    if (errno == ERANGE || end == token || *end != '\0') {
        return false;
    }
    value = parsed;
    return true;
}

bool read_unsigned(
    void* stream, unsigned long long& value, int base) noexcept {
    char token[128];
    if (!read_token(stream, token, sizeof(token))) {
        return false;
    }
    char* end = nullptr;
    errno = 0;
    const unsigned long long parsed =
        ::strtoull(token, &end, base);
    if (errno == ERANGE || end == token || *end != '\0') {
        return false;
    }
    value = parsed;
    return true;
}

bool read_floating(void* stream, long double& value) noexcept {
    char token[128];
    if (!read_token(stream, token, sizeof(token))) {
        return false;
    }
    char* end = nullptr;
    errno = 0;
    const long double parsed = ::strtold(token, &end);
    if ((errno == ERANGE && __builtin_isinf(parsed)) ||
        end == token || *end != '\0') {
        return false;
    }
    value = parsed;
    return true;
}

long long tell(void* stream) noexcept {
    if (stream == nullptr) {
        return -1;
    }
    return static_cast<long long>(::ftello(as_file(stream)));
}

bool seek(
    void* stream, long long offset, unsigned int direction) noexcept {
    if (stream == nullptr) {
        return false;
    }
    const int origin =
        direction == 0 ? SEEK_SET
      : direction == 1 ? SEEK_CUR
                       : SEEK_END;
    return ::fseeko(
               as_file(stream), static_cast<off_t>(offset), origin) == 0;
}

} // namespace __io

namespace {

class native_streambuf final : public streambuf {
public:
    explicit native_streambuf(void* stream) noexcept
        : stream_(stream) {}

protected:
    int_type underflow() override {
        const int value = __io::get(stream_);
        if (value == EOF) {
            return traits_type::eof();
        }
        if (!__io::unget(stream_, static_cast<char>(value))) {
            return traits_type::eof();
        }
        return traits_type::to_int_type(static_cast<char>(value));
    }

    int_type uflow() override {
        const int value = __io::get(stream_);
        return value == EOF
                   ? traits_type::eof()
                   : traits_type::to_int_type(
                         static_cast<char>(value));
    }

    int_type pbackfail(int_type value) override {
        if (traits_type::eq_int_type(value, traits_type::eof())) {
            return traits_type::eof();
        }
        return __io::unget(
                   stream_, traits_type::to_char_type(value))
                   ? value
                   : traits_type::eof();
    }

    streamsize xsgetn(
        char* destination, streamsize count) override {
        streamsize read = 0;
        while (read < count) {
            const int value = __io::get(stream_);
            if (value == EOF) {
                break;
            }
            destination[read++] = static_cast<char>(value);
        }
        return read;
    }

    int_type overflow(int_type value) override {
        if (traits_type::eq_int_type(value, traits_type::eof())) {
            return __io::flush(stream_)
                       ? traits_type::not_eof(value)
                       : traits_type::eof();
        }
        return __io::put(
                   stream_, traits_type::to_char_type(value))
                   ? value
                   : traits_type::eof();
    }

    streamsize xsputn(
        const char* source, streamsize count) override {
        if (count < 0) {
            return 0;
        }
        return __io::write(
                   stream_, source, static_cast<size_t>(count))
                   ? count
                   : 0;
    }

    int sync() override {
        return __io::flush(stream_) ? 0 : -1;
    }

    pos_type seekoff(
        off_type offset, ios_base::seekdir direction,
        ios_base::openmode) override {
        if (!__io::seek(
                stream_, static_cast<long long>(offset), direction)) {
            return pos_type(-1);
        }
        const long long position = __io::tell(stream_);
        return position < 0 ? pos_type(-1) : pos_type(position);
    }

private:
    void* stream_;
};

native_streambuf input_buffer(stdin);
native_streambuf output_buffer(stdout);
native_streambuf error_buffer(stderr);

} // namespace

istream cin(&input_buffer);
ostream cout(&output_buffer);
ostream cerr(&error_buffer);
ostream clog(&error_buffer);

namespace {

struct configure_standard_streams {
    configure_standard_streams() {
        cin.tie(&cout);
        cerr.setf(ios_base::unitbuf);
    }
};

configure_standard_streams configure_streams;

} // namespace

_ADINKRA_END_NAMESPACE_STD
