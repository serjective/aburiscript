#ifndef ABURI_CIR_GRAPH_SERIALIZE_H
#define ABURI_CIR_GRAPH_SERIALIZE_H

#include <memory>
#include <string>
#include <string_view>

struct TargetInfo;

namespace aburi::cir {

class File;

uint64_t module_graph_schema_version();

bool module_graph_serializable(const File& file);

bool write_module_graph(const File& file, std::string& out);

std::unique_ptr<File> read_module_graph(std::string_view bytes,
                                        std::shared_ptr<TargetInfo> target);

} // namespace aburi::cir

#endif // ABURI_CIR_GRAPH_SERIALIZE_H
