#include "collect.h"

#include <vector>

namespace aburi::collect {

cir::File collect_translation_unit(const syntax::Tree& tree,
                                   const std::vector<Token>& tokens,
                                   const LangOptions& lang_opts) {
    (void)tree;
    (void)tokens;
    Session session(lang_opts);
    session.report_error("post-tree Collect is disabled; use parser-driven Collect");
    return session.finish_file();
}

} // namespace aburi::collect
