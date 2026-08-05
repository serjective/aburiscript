#include <locale>

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <cwchar>
#include <locale.h>
#include <new>
#include <string>
#include <vector>
#include <wctype.h>

namespace std {
inline namespace __adinkra_v1 {

namespace __locale_runtime {

namespace {

struct locale_handle {
    locale_t value;
};

class locale_scope {
public:
    explicit locale_scope(locale_t value) noexcept
        : previous_(::uselocale(value)) {}

    ~locale_scope() {
        ::uselocale(previous_);
    }

private:
    locale_t previous_;
};

constexpr uint64_t mask_space = 1ULL << 0;
constexpr uint64_t mask_print = 1ULL << 1;
constexpr uint64_t mask_cntrl = 1ULL << 2;
constexpr uint64_t mask_upper = 1ULL << 3;
constexpr uint64_t mask_lower = 1ULL << 4;
constexpr uint64_t mask_alpha = 1ULL << 5;
constexpr uint64_t mask_digit = 1ULL << 6;
constexpr uint64_t mask_punct = 1ULL << 7;
constexpr uint64_t mask_xdigit = 1ULL << 8;
constexpr uint64_t mask_blank = 1ULL << 9;

} // namespace

void* create(const char* name) {
    if (name == nullptr) {
        throw runtime_error("invalid locale name");
    }
    locale_t value = ::newlocale(LC_ALL_MASK, name, nullptr);
    if (value == nullptr) {
        throw runtime_error("locale is not available");
    }
    locale_handle* result = new locale_handle{value};
    return result;
}

void destroy(void* handle) noexcept {
    if (handle == nullptr) {
        return;
    }
    locale_handle* value = static_cast<locale_handle*>(handle);
    ::freelocale(value->value);
    delete value;
}

uint64_t classify(const void* handle, uint32_t value) noexcept {
    const locale_t location =
        static_cast<const locale_handle*>(handle)->value;
    const locale_scope scope(location);
    const wint_t character = static_cast<wint_t>(value);
    uint64_t result = 0;
    if (::iswspace(character)) {
        result |= mask_space;
    }
    if (::iswprint(character)) {
        result |= mask_print;
    }
    if (::iswcntrl(character)) {
        result |= mask_cntrl;
    }
    if (::iswupper(character)) {
        result |= mask_upper;
    }
    if (::iswlower(character)) {
        result |= mask_lower;
    }
    if (::iswalpha(character)) {
        result |= mask_alpha;
    }
    if (::iswdigit(character)) {
        result |= mask_digit;
    }
    if (::iswpunct(character)) {
        result |= mask_punct;
    }
    if (::iswxdigit(character)) {
        result |= mask_xdigit;
    }
    if (character == static_cast<wint_t>(' ') ||
        character == static_cast<wint_t>('\t')) {
        result |= mask_blank;
    }
    return result;
}

uint32_t lower(const void* handle, uint32_t value) noexcept {
    const locale_scope scope(
        static_cast<const locale_handle*>(handle)->value);
    return static_cast<uint32_t>(
        ::towlower(static_cast<wint_t>(value)));
}

uint32_t upper(const void* handle, uint32_t value) noexcept {
    const locale_scope scope(
        static_cast<const locale_handle*>(handle)->value);
    return static_cast<uint32_t>(
        ::towupper(static_cast<wint_t>(value)));
}

int compare(
    const void* handle,
    const uint32_t* left,
    size_t left_size,
    const uint32_t* right,
    size_t right_size) {
    vector<wchar_t> left_value;
    vector<wchar_t> right_value;
    left_value.reserve(left_size + 1);
    right_value.reserve(right_size + 1);
    for (size_t index = 0; index < left_size; ++index) {
        left_value.push_back(static_cast<wchar_t>(left[index]));
    }
    for (size_t index = 0; index < right_size; ++index) {
        right_value.push_back(static_cast<wchar_t>(right[index]));
    }
    left_value.push_back(L'\0');
    right_value.push_back(L'\0');
    const locale_scope scope(
        static_cast<const locale_handle*>(handle)->value);
    const int result = ::wcscoll(
        left_value.data(), right_value.data());
    return result < 0 ? -1 : result > 0 ? 1 : 0;
}

size_t transform(
    const void* handle,
    const void* input,
    size_t input_size,
    void* output,
    size_t output_size,
    bool narrow) {
    const locale_scope scope(
        static_cast<const locale_handle*>(handle)->value);
    if (narrow) {
        const char* input_char =
            static_cast<const char*>(input);
        vector<char> source;
        source.reserve(input_size + 1);
        for (size_t index = 0; index < input_size; ++index) {
            source.push_back(input_char[index]);
        }
        source.push_back('\0');
        const size_t size = ::strxfrm(nullptr, source.data(), 0);
        if (output == nullptr || output_size == 0) {
            return size;
        }
        vector<char> key(size + 1);
        ::strxfrm(key.data(), source.data(), key.size());
        const size_t copied = size < output_size ? size : output_size;
        char* output_char = static_cast<char*>(output);
        for (size_t index = 0; index < copied; ++index) {
            output_char[index] = key[index];
        }
        return size;
    }

    const wchar_t* input_wide =
        static_cast<const wchar_t*>(input);
    vector<wchar_t> source;
    source.reserve(input_size + 1);
    for (size_t index = 0; index < input_size; ++index) {
        source.push_back(input_wide[index]);
    }
    source.push_back(L'\0');
    const size_t size = ::wcsxfrm(nullptr, source.data(), 0);
    if (output == nullptr || output_size == 0) {
        return size;
    }
    vector<wchar_t> key(size + 1);
    ::wcsxfrm(key.data(), source.data(), key.size());
    const size_t copied = size < output_size ? size : output_size;
    wchar_t* output_wide = static_cast<wchar_t*>(output);
    for (size_t index = 0; index < copied; ++index) {
        output_wide[index] = key[index];
    }
    return size;
}

} // namespace __locale_runtime

struct locale::storage {
    size_t references;
    size_t size;
    facet** facets;
    char* name;
};

size_t next_locale_id = 0;

locale::storage* locale::allocate_storage(
    size_t size, const char* name) {
    auto* result = static_cast<storage*>(
        ::malloc(sizeof(storage)));
    if (result == nullptr) {
        throw bad_alloc();
    }

    result->references = 1;
    result->size = size;
    const size_t name_size = ::strlen(name);
    result->name = static_cast<char*>(::malloc(name_size + 1));
    if (result->name == nullptr) {
        ::free(result);
        throw bad_alloc();
    }
    ::memcpy(result->name, name, name_size + 1);
    result->facets = static_cast<locale::facet**>(
        ::calloc(size, sizeof(locale::facet*)));
    if (size != 0 && result->facets == nullptr) {
        ::free(result->name);
        ::free(result);
        throw bad_alloc();
    }
    return result;
}

template<class Character>
string numpunct<Character>::grouping() const {
    return do_grouping();
}

template<class Character>
Character numpunct<Character>::decimal_point() const {
    return do_decimal_point();
}

template<class Character>
Character numpunct<Character>::thousands_sep() const {
    return do_thousands_sep();
}

template<class Character>
typename numpunct<Character>::string_type
numpunct<Character>::truename() const {
    return do_truename();
}

template<class Character>
typename numpunct<Character>::string_type
numpunct<Character>::falsename() const {
    return do_falsename();
}

template<class Character>
string numpunct<Character>::do_grouping() const {
    return string();
}

template<class Character>
Character numpunct<Character>::do_decimal_point() const {
    return static_cast<Character>('.');
}

template<class Character>
Character numpunct<Character>::do_thousands_sep() const {
    return static_cast<Character>(',');
}

template<class Character>
typename numpunct<Character>::string_type
numpunct<Character>::do_truename() const {
    const char value[] = "true";
    string_type result;
    for (char character : value) {
        if (character != '\0') {
            result.push_back(static_cast<Character>(character));
        }
    }
    return result;
}

template<class Character>
typename numpunct<Character>::string_type
numpunct<Character>::do_falsename() const {
    const char value[] = "false";
    string_type result;
    for (char character : value) {
        if (character != '\0') {
            result.push_back(static_cast<Character>(character));
        }
    }
    return result;
}

template class numpunct<char>;
template class numpunct<wchar_t>;

locale::facet::~facet() = default;

void locale::facet::retain() const noexcept {
    __atomic_add_fetch(&references_, static_cast<size_t>(1),
                       __ATOMIC_RELAXED);
}

void locale::facet::release() const noexcept {
    const size_t remaining = __atomic_sub_fetch(
        &references_, static_cast<size_t>(1), __ATOMIC_ACQ_REL);
    if (remaining == 0 && delete_when_unused_) {
        delete this;
    }
}

size_t locale::id::__index() const noexcept {
    size_t current = __atomic_load_n(&value_, __ATOMIC_ACQUIRE);
    if (current != 0) {
        return current - 1;
    }

    const size_t assigned = __atomic_add_fetch(
        &next_locale_id, static_cast<size_t>(1), __ATOMIC_RELAXED);
    size_t expected = 0;
    if (!__atomic_compare_exchange_n(
            &value_, &expected, assigned, false,
            __ATOMIC_RELEASE, __ATOMIC_ACQUIRE)) {
        return expected - 1;
    }
    return assigned - 1;
}

locale::storage* locale::classic_storage() noexcept {
    static storage* value = [] {
        const size_t narrow = numpunct<char>::id.__index();
        const size_t wide = numpunct<wchar_t>::id.__index();
        const size_t narrow_ctype = std::ctype<char>::id.__index();
        const size_t wide_ctype = std::ctype<wchar_t>::id.__index();
        const size_t narrow_collate =
            std::collate<char>::id.__index();
        const size_t wide_collate =
            std::collate<wchar_t>::id.__index();
        size_t size = narrow > wide ? narrow : wide;
        size = size > narrow_ctype ? size : narrow_ctype;
        size = size > wide_ctype ? size : wide_ctype;
        size = size > narrow_collate ? size : narrow_collate;
        size = size > wide_collate ? size : wide_collate;
        ++size;
        storage* result = allocate_storage(size, "C");
        result->facets[narrow] = new numpunct<char>(1);
        result->facets[wide] = new numpunct<wchar_t>(1);
        result->facets[narrow_ctype] =
            new std::ctype<char>(1);
        result->facets[wide_ctype] =
            new std::ctype<wchar_t>(1);
        result->facets[narrow_collate] =
            new std::collate<char>(1);
        result->facets[wide_collate] =
            new std::collate<wchar_t>(1);
        result->facets[narrow]->retain();
        result->facets[wide]->retain();
        result->facets[narrow_ctype]->retain();
        result->facets[wide_ctype]->retain();
        result->facets[narrow_collate]->retain();
        result->facets[wide_collate]->retain();
        return result;
    }();
    return value;
}

locale::storage*& locale::global_storage() noexcept {
    static storage* value = [] {
        storage* result = classic_storage();
        retain_storage(result);
        return result;
    }();
    return value;
}

void locale::retain_storage(storage* value) noexcept {
    __atomic_add_fetch(
        &value->references, static_cast<size_t>(1), __ATOMIC_RELAXED);
}

void locale::release_storage(storage* value) noexcept {
    if (__atomic_sub_fetch(
            &value->references, static_cast<size_t>(1),
            __ATOMIC_ACQ_REL) != 0) {
        return;
    }

    for (size_t index = 0; index < value->size; ++index) {
        if (value->facets[index] != nullptr) {
            value->facets[index]->release();
        }
    }
    ::free(value->facets);
    ::free(value->name);
    ::free(value);
}

locale::storage* locale::copy_with_facet(
    storage* source, size_t index, facet* value) {
    if (value == nullptr) {
        retain_storage(source);
        return source;
    }

    const size_t size =
        source->size > index ? source->size : index + 1;
    storage* result = allocate_storage(size, source->name);
    for (size_t current = 0; current < source->size; ++current) {
        result->facets[current] = source->facets[current];
        if (result->facets[current] != nullptr) {
            result->facets[current]->retain();
        }
    }

    if (result->facets[index] != nullptr) {
        result->facets[index]->release();
    }
    result->facets[index] = value;
    value->retain();
    return result;
}

const locale::facet* locale::find_facet(
    const storage* source, size_t index) noexcept {
    return index < source->size ? source->facets[index] : nullptr;
}

locale::locale() noexcept : storage_(global_storage()) {
    retain_storage(storage_);
}

locale::locale(const locale& other) noexcept
    : storage_(other.storage_) {
    retain_storage(storage_);
}

locale& locale::operator=(const locale& other) noexcept {
    if (this != &other) {
        retain_storage(other.storage_);
        release_storage(storage_);
        storage_ = other.storage_;
    }
    return *this;
}

locale::~locale() {
    release_storage(storage_);
}

locale::locale(const char* name) : storage_(nullptr) {
    void* validation = __locale_runtime::create(name);
    __locale_runtime::destroy(validation);

    const size_t narrow = numpunct<char>::id.__index();
    const size_t wide = numpunct<wchar_t>::id.__index();
    const size_t narrow_ctype = std::ctype<char>::id.__index();
    const size_t wide_ctype = std::ctype<wchar_t>::id.__index();
    const size_t narrow_collate =
        std::collate<char>::id.__index();
    const size_t wide_collate =
        std::collate<wchar_t>::id.__index();
    size_t size = narrow > wide ? narrow : wide;
    size = size > narrow_ctype ? size : narrow_ctype;
    size = size > wide_ctype ? size : wide_ctype;
    size = size > narrow_collate ? size : narrow_collate;
    size = size > wide_collate ? size : wide_collate;
    storage_ = allocate_storage(size + 1, name);
    storage_->facets[narrow] = new numpunct<char>();
    storage_->facets[wide] = new numpunct<wchar_t>();
    storage_->facets[narrow_ctype] = new ctype_byname<char>(name);
    storage_->facets[wide_ctype] = new ctype_byname<wchar_t>(name);
    storage_->facets[narrow_collate] =
        new collate_byname<char>(name);
    storage_->facets[wide_collate] =
        new collate_byname<wchar_t>(name);
    for (size_t index = 0; index < storage_->size; ++index) {
        if (storage_->facets[index] != nullptr) {
            storage_->facets[index]->retain();
        }
    }
}

locale::locale(const string& name)
    : locale(name.c_str()) {}

locale::locale(
    const locale& other,
    const char* name,
    category selected)
    : locale(name) {
    if (selected == all) {
        return;
    }
    if (selected == none) {
        *this = other;
        return;
    }

    storage* named = storage_;
    const size_t size =
        named->size > other.storage_->size
            ? named->size
            : other.storage_->size;
    storage* combined = allocate_storage(size, "*");
    const size_t narrow_ctype = std::ctype<char>::id.__index();
    const size_t wide_ctype = std::ctype<wchar_t>::id.__index();
    const size_t narrow_collate =
        std::collate<char>::id.__index();
    const size_t wide_collate =
        std::collate<wchar_t>::id.__index();
    const size_t narrow_numeric = numpunct<char>::id.__index();
    const size_t wide_numeric = numpunct<wchar_t>::id.__index();
    for (size_t index = 0; index < size; ++index) {
        bool take_named = false;
        if ((selected & ctype) != 0 &&
            (index == narrow_ctype || index == wide_ctype)) {
            take_named = true;
        }
        if ((selected & collate) != 0 &&
            (index == narrow_collate ||
             index == wide_collate)) {
            take_named = true;
        }
        if ((selected & numeric) != 0 &&
            (index == narrow_numeric ||
             index == wide_numeric)) {
            take_named = true;
        }
        storage* source = take_named ? named : other.storage_;
        if (index < source->size) {
            combined->facets[index] = source->facets[index];
            if (combined->facets[index] != nullptr) {
                combined->facets[index]->retain();
            }
        }
    }
    storage_ = combined;
    release_storage(named);
}

locale::locale(
    const locale& other,
    const string& name,
    category selected)
    : locale(other, name.c_str(), selected) {}

string locale::name() const {
    return string(storage_->name);
}

locale::locale(storage* value, retain_storage_t) noexcept
    : storage_(value) {
    retain_storage(storage_);
}

const locale& locale::classic() noexcept {
    static const locale value(
        classic_storage(), retain_storage_t{});
    return value;
}

locale locale::global(const locale& value) {
    storage*& current = global_storage();
    locale previous(current, retain_storage_t{});
    retain_storage(value.storage_);
    release_storage(current);
    current = value.storage_;
    return previous;
}

} // namespace __adinkra_v1
} // namespace std
