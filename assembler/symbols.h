#ifndef ABURI_ASSEMBLER_SYMBOLS_H
#define ABURI_ASSEMBLER_SYMBOLS_H

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace aburi::assembler {

using SymId = uint32_t;
inline constexpr SymId no_sym = UINT32_MAX;

enum class SymState : uint8_t {
    Undefined,
    Label,
    Constant,
};

struct AsmSymbol {
    std::string name;
    SymState state = SymState::Undefined;
    int section = -1;
    uint64_t offset = 0;
    uint32_t deferred_seq = 0;
    int64_t value = 0;
    bool global = false;
    bool weak = false;
    bool hidden = false;
    bool from_set = false;
    bool referenced = false;
    bool internal = false;
};

class SymbolTable {
public:
    SymId intern(std::string_view name);

    SymId make_internal(std::string display_name);

    AsmSymbol& sym(SymId id) { return symbols_[id]; }
    const AsmSymbol& sym(SymId id) const { return symbols_[id]; }
    SymId size() const { return static_cast<SymId>(symbols_.size()); }

private:
    struct StringHash {
        using is_transparent = void;
        size_t operator()(std::string_view text) const {
            return std::hash<std::string_view>{}(text);
        }
    };

    std::unordered_map<std::string, SymId, StringHash, std::equal_to<>> index_;
    std::vector<AsmSymbol> symbols_;
};

}

#endif
