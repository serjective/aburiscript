#include "collect_templates_internal.h"

#include <string>

namespace template_sema_internal {

TemplateInstantiationDepthGuard::TemplateInstantiationDepthGuard(
    ASTContext* ast_ctx,
    const Collect* collect,
    std::string_view template_kind,
    std::string_view template_name,
    SrcLoc loc,
    TemplateInstantiationDepthDiagnostic diagnostic)
    : ast_ctx_(ast_ctx) {
    if (!ast_ctx_) {
        return;
    }
    if (ast_ctx_->push_template_instantiation_frame()) {
        active_ = true;
        ok_ = true;
        return;
    }
    if (diagnostic == TemplateInstantiationDepthDiagnostic::Report &&
        collect) {
        collect->report_error(
            "template instantiation depth exceeded while instantiating " +
                std::string(template_kind) + " template '" +
                std::string(template_name) + "'",
            loc);
    }
}

TemplateInstantiationDepthGuard::~TemplateInstantiationDepthGuard() {
    if (active_) {
        ast_ctx_->pop_template_instantiation_frame();
    }
}

} // namespace template_sema_internal
