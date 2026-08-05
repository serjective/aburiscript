#include "symbols.h"

namespace aburi::assembler {

SymId SymbolTable::intern(std::string_view name) {
    auto found = index_.find(name);
    if (found != index_.end()) {
        return found->second;
    }
    SymId id = static_cast<SymId>(symbols_.size());
    AsmSymbol symbol;
    symbol.name = std::string(name);
    symbols_.push_back(std::move(symbol));
    index_.emplace(symbols_.back().name, id);
    return id;
}

SymId SymbolTable::make_internal(std::string display_name) {
    SymId id = static_cast<SymId>(symbols_.size());
    AsmSymbol symbol;
    symbol.name = std::move(display_name);
    symbol.internal = true;
    symbols_.push_back(std::move(symbol));
    return id;
}

}
