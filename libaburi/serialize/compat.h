#ifndef ABURI_LIBABURI_SERIALIZE_COMPAT_H
#define ABURI_LIBABURI_SERIALIZE_COMPAT_H

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "../../lang_options.h"

struct SourceManager;

namespace aburi::serialize {

struct CompatIdentity {
    std::string text;
    uint64_t hash = 0;

    static CompatIdentity build(
        std::string_view compiler_version,
        std::string_view target_triple,
        const LangOptions& lang_options,
        const std::vector<std::pair<std::string, std::string>>& defines,
        const std::vector<std::string>& undefines);
};

std::string describe_compat_mismatch(std::string_view ours,
                                     std::string_view theirs);

struct DependencyRecord {
    std::string path;
    uint64_t size = 0;
    uint64_t content_hash = 0;
};

std::string write_dependency_section(const SourceManager& source_manager);
std::vector<DependencyRecord> read_dependency_section(std::string_view bytes);
uint64_t hash_bytes(std::string_view bytes);

} // namespace aburi::serialize

#endif // ABURI_LIBABURI_SERIALIZE_COMPAT_H
