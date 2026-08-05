#ifndef ABURI_LIBABURI_SERIALIZE_FORMAT_H
#define ABURI_LIBABURI_SERIALIZE_FORMAT_H

#include <cstdint>
#include <cstring>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aburi::serialize {

inline constexpr uint32_t kArtifactMagic = 0x494d4241u;
inline constexpr uint32_t kArtifactFormatVersion = 2;

constexpr uint32_t section_tag(char a, char b, char c, char d) {
    return static_cast<uint32_t>(static_cast<unsigned char>(a)) |
           (static_cast<uint32_t>(static_cast<unsigned char>(b)) << 8) |
           (static_cast<uint32_t>(static_cast<unsigned char>(c)) << 16) |
           (static_cast<uint32_t>(static_cast<unsigned char>(d)) << 24);
}

inline constexpr uint32_t kSectionCompat = section_tag('C', 'O', 'M', 'P');
inline constexpr uint32_t kSectionDeps = section_tag('D', 'E', 'P', 'S');
inline constexpr uint32_t kSectionMeta = section_tag('M', 'E', 'T', 'A');
inline constexpr uint32_t kSectionTokens = section_tag('T', 'O', 'K', 'S');
inline constexpr uint32_t kSectionSpellings = section_tag('B', 'L', 'O', 'B');
inline constexpr uint32_t kSectionSourceLocs = section_tag('S', 'L', 'O', 'C');
inline constexpr uint32_t kSectionMacros = section_tag('M', 'A', 'C', ' ');

inline constexpr uint32_t kSectionGraph = section_tag('C', 'I', 'R', 'S');
inline constexpr uint32_t kSectionTemplates = section_tag('T', 'M', 'P', 'L');

class ByteWriter {
public:
    void u8(uint8_t value) { out_.push_back(static_cast<char>(value)); }
    void u16(uint16_t value) { append(&value, sizeof value); }
    void u32(uint32_t value) { append(&value, sizeof value); }
    void u64(uint64_t value) { append(&value, sizeof value); }
    void bytes(std::string_view value) {
        out_.append(value.data(), value.size());
    }
    void sized_string(std::string_view value) {
        u32(static_cast<uint32_t>(value.size()));
        bytes(value);
    }
    const std::string& buffer() const { return out_; }
    std::string take() { return std::move(out_); }

private:
    void append(const void* data, size_t size) {

        out_.append(static_cast<const char*>(data), size);
    }
    std::string out_;
};

class ByteReader {
public:
    explicit ByteReader(std::string_view bytes) : bytes_(bytes) {}
    uint8_t u8() { return static_cast<uint8_t>(take(1)[0]); }
    uint16_t u16() { return scalar<uint16_t>(); }
    uint32_t u32() { return scalar<uint32_t>(); }
    uint64_t u64() { return scalar<uint64_t>(); }
    std::string_view sized_string() {
        uint32_t size = u32();
        return take(size);
    }
    std::string_view raw(size_t size) { return take(size); }
    bool ok() const { return ok_; }
    bool at_end() const { return position_ == bytes_.size(); }

private:
    template <typename T>
    T scalar() {
        std::string_view view = take(sizeof(T));
        T value{};
        if (ok_) {
            std::memcpy(&value, view.data(), sizeof(T));
        }
        return value;
    }
    std::string_view take(size_t size) {
        if (!ok_ || bytes_.size() - position_ < size) {
            ok_ = false;
            return {};
        }
        std::string_view view = bytes_.substr(position_, size);
        position_ += size;
        return view;
    }
    std::string_view bytes_;
    size_t position_ = 0;
    bool ok_ = true;
};

class ArtifactWriter {
public:
    explicit ArtifactWriter(uint64_t compat_hash)
        : compat_hash_(compat_hash) {}
    void add_section(uint32_t tag, std::string bytes) {
        sections_.emplace_back(tag, std::move(bytes));
    }
    std::string finish() const {
        ByteWriter header;
        header.u32(kArtifactMagic);
        header.u32(kArtifactFormatVersion);
        header.u64(compat_hash_);
        header.u32(static_cast<uint32_t>(sections_.size()));
        uint64_t offset = header.buffer().size() + sections_.size() * 20;
        ByteWriter directory;
        for (const auto& [tag, bytes] : sections_) {
            directory.u32(tag);
            directory.u64(offset);
            directory.u64(bytes.size());
            offset += bytes.size();
        }
        std::string out = header.buffer();
        out += directory.buffer();
        for (const auto& [tag, bytes] : sections_) {
            out += bytes;
        }
        return out;
    }

private:
    uint64_t compat_hash_;
    std::vector<std::pair<uint32_t, std::string>> sections_;
};

struct ArtifactView {
    bool valid = false;
    uint32_t version = 0;
    uint64_t compat_hash = 0;
    std::map<uint32_t, std::string_view> sections;

    std::string_view section(uint32_t tag) const {
        auto found = sections.find(tag);
        return found == sections.end() ? std::string_view() : found->second;
    }

    static ArtifactView parse(std::string_view bytes) {
        ArtifactView view;
        ByteReader reader(bytes);
        if (reader.u32() != kArtifactMagic) {
            return view;
        }
        view.version = reader.u32();
        view.compat_hash = reader.u64();
        uint32_t count = reader.u32();
        if (!reader.ok() || view.version != kArtifactFormatVersion) {
            return view;
        }
        for (uint32_t i = 0; i < count; ++i) {
            uint32_t tag = reader.u32();
            uint64_t offset = reader.u64();
            uint64_t size = reader.u64();
            if (!reader.ok() || offset > bytes.size() ||
                size > bytes.size() - offset) {
                return view;
            }
            view.sections.emplace(tag, bytes.substr(offset, size));
        }
        view.valid = reader.ok();
        return view;
    }
};

} // namespace aburi::serialize

#endif // ABURI_LIBABURI_SERIALIZE_FORMAT_H
