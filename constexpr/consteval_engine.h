#ifndef ABURI_CONSTEVAL_ENGINE_H
#define ABURI_CONSTEVAL_ENGINE_H

#include "../cir/file.h"

#include <functional>
#include <utility>
#include <vector>

#include "../lang_options.h"
#include "consteval_mode.h"
#include "consteval_result.h"

struct ConstEvalContext {
    const aburi::cir::File* file = nullptr;
    aburi::cir::File* mutable_file = nullptr;
    LangOptions lang_options{};
    std::function<bool(aburi::cir::EntityId, SrcLoc)>
        demand_function_definition;
};

struct ConstEvalRequest {
    ConstEvalMode mode = ConstEvalMode::c_ice();
    aburi::cir::TypeId target_type{};
    SrcLoc loc{};
    bool required = false;
};

struct ConstEvalObjectSeed {
    aburi::cir::EntityId entity{};
    aburi::cir::TypeId type{};
    ConstValue value{};
    SrcLoc loc{};
};

class ConstEvalEngine {
public:
    explicit ConstEvalEngine(ConstEvalContext context)
        : context_(std::move(context)) {}

    explicit ConstEvalEngine(const aburi::cir::File& file,
                             LangOptions options = LangOptions())
        : context_{&file, nullptr, std::move(options)} {}

    explicit ConstEvalEngine(aburi::cir::File& file,
                             LangOptions options = LangOptions())
        : context_{&file, &file, std::move(options)} {}

    const LangOptions& lang_options() const {
        return context_.lang_options;
    }

    bool is_enabled() const {
        return context_.lang_options.enable_consteval_engine;
    }

    ConstEvalResult evaluate_inst(aburi::cir::InstId inst,
                                  ConstEvalRequest request) const;
    ConstEvalResult evaluate_fragment(const aburi::cir::Fragment& fragment,
                                      aburi::cir::ValueRef result,
                                      ConstEvalRequest request) const;
    ConstEvalResult evaluate_fragment_with_object_seeds(
        const aburi::cir::Fragment& fragment,
        aburi::cir::ValueRef result,
        ConstEvalRequest request,
        const std::vector<ConstEvalObjectSeed>& object_seeds) const;

private:
    ConstEvalContext context_;
};

#endif // ABURI_CONSTEVAL_ENGINE_H
