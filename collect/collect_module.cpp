// The C++20 module invariant permits only this collector to mutate
// ActiveModuleContext, keeping entity stamping uniform across declarations.
#include "collect.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <utility>

#include "../libaburi/modules/loader.h"

namespace aburi::collect {

void Session::collect_global_module_fragment(SrcLoc loc) {
    cir::File::ActiveModuleContext active = file_.active_module_context();
    if (active.unit.valid() || module_state_.seen_module_declaration) {
        report_error(
            "the global module fragment must be the first declaration of a "
            "module unit",
            loc);
        return;
    }

    cir::ModuleUnitFact fact;
    fact.loc = loc;
    module_state_.unit = file_.add_module_unit(std::move(fact));
    file_.set_active_module_context(
        {module_state_.unit, cir::ModuleFragment::Global, 0});
    active_module_visibility_frame().unit = module_state_.unit;
    sync_module_visibility();
}

void Session::collect_module_declaration(std::string_view module_name,
                                         std::string_view partition_name,
                                         bool has_partition,
                                         bool exported,
                                         bool at_start,
                                         SrcLoc loc) {
    cir::File::ActiveModuleContext active = file_.active_module_context();
    if (module_state_.seen_module_declaration ||
        (active.unit.valid() &&
         active.fragment != cir::ModuleFragment::Global)) {
        report_error(
            "translation unit already contains a module declaration", loc);
        return;
    }
    if (!active.unit.valid() && !at_start) {
        report_error(
            "a module declaration must be the first declaration of the "
            "translation unit",
            loc);
        return;
    }
    if (!active.unit.valid()) {

        cir::ModuleUnitFact fact;
        fact.loc = loc;
        module_state_.unit = file_.add_module_unit(std::move(fact));
    }
    cir::ModuleUnitFact* fact = file_.module_unit_mut(module_state_.unit);
    fact->module_name = file_.intern_name(module_name);
    if (has_partition) {
        fact->partition_name = file_.intern_name(partition_name);
    }
    if (exported) {
        fact->kind = has_partition
            ? cir::ModuleUnitFact::Kind::InterfacePartition
            : cir::ModuleUnitFact::Kind::PrimaryInterface;
    } else {
        fact->kind = has_partition
            ? cir::ModuleUnitFact::Kind::ImplementationPartition
            : cir::ModuleUnitFact::Kind::Implementation;
    }
    bool implicit_primary_import =
        fact->kind == cir::ModuleUnitFact::Kind::Implementation;
    module_state_.seen_module_declaration = true;
    file_.set_active_module_context(
        {module_state_.unit, cir::ModuleFragment::Purview, 0});
    active_module_visibility_frame().unit = module_state_.unit;
    sync_module_visibility();
    if (implicit_primary_import) {

        collect_module_import(std::string(module_name), false, false, loc);
    }
}

void Session::collect_private_module_fragment(SrcLoc loc) {
    cir::File::ActiveModuleContext active = file_.active_module_context();
    if (module_state_.seen_private_fragment) {
        report_error(
            "translation unit already contains a private module fragment",
            loc);
        return;
    }
    const cir::ModuleUnitFact& fact = file_.module_unit(module_state_.unit);
    if (!active.unit.valid() ||
        active.fragment != cir::ModuleFragment::Purview ||
        fact.kind != cir::ModuleUnitFact::Kind::PrimaryInterface) {
        report_error(
            "a private module fragment can only appear in a primary module "
            "interface unit",
            loc);
        return;
    }
    if (active.export_depth > 0) {
        report_error(
            "a private module fragment cannot appear in an export declaration",
            loc);
        return;
    }
    module_state_.seen_private_fragment = true;
    file_.set_active_module_context(
        {module_state_.unit, cir::ModuleFragment::Private, 0});
}

Session::ModuleVisibilityFrame& Session::active_module_visibility_frame() {
    if (module_visibility_stack_.empty()) {
        module_visibility_stack_.push_back({});
    }
    return module_visibility_stack_.back();
}

void Session::sync_module_visibility() {
    ModuleVisibilityFrame& frame = active_module_visibility_frame();
    file_.set_active_module_visibility(frame.unit,
                                       frame.visible_unit_indexes);
}

void Session::make_module_unit_visible(cir::ModuleAttachmentId unit) {
    if (!unit.valid()) {
        return;
    }
    ModuleVisibilityFrame& frame = active_module_visibility_frame();
    if (std::find(frame.visible_unit_indexes.begin(),
                  frame.visible_unit_indexes.end(),
                  unit.index) != frame.visible_unit_indexes.end()) {
        return;
    }
    frame.visible_unit_indexes.push_back(unit.index);

    for (cir::ModuleAttachmentId exported :
         file_.module_unit(unit).exported_imports) {
        make_module_unit_visible(exported);
    }
    sync_module_visibility();
}

cir::ModuleAttachmentId Session::import_module_unit_by_key(
    const std::string& module_name,
    const std::string& partition_name,
    SrcLoc loc) {
    std::string key = partition_name.empty()
        ? module_name
        : module_name + ":" + partition_name;
    auto known = imported_units_.find(key);
    if (known != imported_units_.end()) {
        return known->second;
    }
    if (!module_loader_) {
        report_error(
            "import of module '" + key +
                "' requires compiling all module units in one driver "
                "invocation",
            loc);
        return {};
    }
    std::string error;
    const aburi::modules::LoadedModuleUnit* loaded =
        module_loader_->load(module_name, partition_name, &error);
    if (!loaded) {
        report_error(error.empty() ? "module '" + key + "' not found"
                                   : error,
                     loc);
        return {};
    }
    cir::ModuleAttachmentId unit = replay_imported_unit(*loaded, loc);
    if (unit.valid()) {
        imported_units_.emplace(key, unit);
    }
    return unit;
}

cir::ModuleAttachmentId Session::replay_imported_unit(
    const aburi::modules::LoadedModuleUnit& loaded, SrcLoc loc) {
    if (!module_unit_replay_callback_ || !source_manager_) {
        report_error("module import is unavailable in this frontend context",
                     loc);
        return {};
    }
    if (!loaded.tokens || !loaded.source_manager) {
        report_error("module interface tokens are unavailable", loc);
        return {};
    }
    uint32_t delta =
        source_manager_->import_foreign_block(*loaded.source_manager);
    auto rebase_tokens = [&loaded, delta]() {
        auto rebased = std::make_unique<std::vector<Token>>();
        rebased->reserve(loaded.tokens->size());
        for (Token token : *loaded.tokens) {
            if (!token.loc.isInvalid()) {
                token.loc.offset += delta;
            }

            token.ident = 0;
            token.hide_set = 0;
            rebased->push_back(token);
        }
        return rebased;
    };
    const char* graph_mode = std::getenv("ABURI_MODULE_GRAPH_IMPORT");
    bool graph_enabled = !(graph_mode && graph_mode[0] == '0');
    const bool debug_import =
        std::getenv("ABURI_DEBUG_MODULE_IMPORT") != nullptr;

    if (loaded.cir != nullptr && loaded.template_state != nullptr &&
        graph_enabled) {
        bool has_templates =
            template_state_has_templates(loaded.template_state.get());
        bool adoptable = !has_templates ||
            template_state_adoptable(loaded.template_state.get(),
                                     *loaded.cir);
        std::string module_key = loaded.partition_name.empty()
            ? loaded.module_name
            : loaded.module_name + ":" + loaded.partition_name;
        if (adoptable) {

            for (cir::ModuleAttachmentId source_unit :
                 loaded.cir->module_unit_ids()) {
                if (source_unit.index < 2) {
                    continue;
                }
                const cir::ModuleUnitFact& fact =
                    loaded.cir->module_unit(source_unit);
                if (!fact.module_name.valid()) {
                    continue;
                }
                std::string dependency_module(
                    loaded.cir->name(fact.module_name));
                std::string dependency_partition =
                    fact.partition_name.valid()
                        ? std::string(loaded.cir->name(fact.partition_name))
                        : std::string();
                (void)import_module_unit_by_key(dependency_module,
                                                dependency_partition, loc);
            }
            cir::File::ModuleGraphImportResult imported =
                file_.import_module_graph(*loaded.cir, module_key, delta,
                                          lookup_generation_,
                                          /*allow_templates=*/has_templates);
            if (imported.unit.valid()) {
                if (debug_import) {
                    std::fprintf(stderr,
                                 "aburi: module '%s': graph import%s\n",
                                 module_key.c_str(),
                                 has_templates ? " (templates adopted)"
                                               : "");
                }

                auto rebased = rebase_tokens();

                adopt_imported_templates(
                    loaded.template_state.get(), imported.remap,
                    *loaded.cir, imported.first_imported_entity_index);
                if (module_unit_register_callback_) {
                    module_unit_register_callback_(*rebased, imported.unit);
                }
                imported_unit_tokens_.push_back(std::move(rebased));

                {
                    ModuleVisibilityFrame unit_frame;
                    unit_frame.unit = imported.unit;
                    module_visibility_stack_.push_back(
                        std::move(unit_frame));
                    const cir::ModuleUnitFact& fact =
                        file_.module_unit(imported.unit);
                    for (cir::ModuleAttachmentId edge : fact.direct_imports) {
                        make_module_unit_visible(edge);
                    }
                    for (cir::ModuleAttachmentId edge :
                         fact.exported_imports) {
                        make_module_unit_visible(edge);
                    }
                    unit_visibility_frames_[imported.unit.index] =
                        module_visibility_stack_.back();
                    module_visibility_stack_.pop_back();
                }
                bump_lookup_generation();
                sync_module_visibility();
                return imported.unit;
            }
            if (debug_import) {
                std::fprintf(stderr,
                             "aburi: module '%s': token replay (%s)\n",
                             module_key.c_str(),
                             imported.refusal.c_str());
            }
        } else if (debug_import) {
            std::fprintf(stderr,
                         "aburi: module '%s': token replay (template "
                         "state not adoptable)\n",
                         module_key.c_str());
        }
    }
    auto rebased = rebase_tokens();

    ModuleState saved_state = module_state_;
    module_state_ = {};
    cir::File::ActiveModuleContext saved_context =
        file_.active_module_context();
    file_.set_active_module_context({});
    module_visibility_stack_.push_back({});
    size_t first_replay_entity = file_.entity_table_size();
    bool replay_ok = module_unit_replay_callback_(*rebased);

    file_.note_imported_definitions_since(first_replay_entity);
    cir::ModuleAttachmentId unit = module_state_.unit;
    if (unit.valid()) {
        unit_visibility_frames_[unit.index] = module_visibility_stack_.back();
    }
    module_visibility_stack_.pop_back();
    module_state_ = saved_state;
    file_.set_active_module_context(saved_context);
    sync_module_visibility();
    imported_unit_tokens_.push_back(std::move(rebased));
    if (!replay_ok || !unit.valid()) {
        report_error("imported module interface failed to compile here", loc);
        return {};
    }
    return unit;
}

void Session::collect_module_import(std::string_view target,
                                    bool is_partition,
                                    bool exported,
                                    SrcLoc loc) {
    std::string partition_name;
    std::string module_name(target);
    if (is_partition) {

        if (!module_state_.unit.valid() ||
            !file_.module_unit(module_state_.unit).module_name.valid()) {
            report_error(
                "a module partition can only be imported by a unit of its "
                "own module",
                loc);
            return;
        }
        partition_name = std::string(target.substr(target.front() == ':' ? 1 : 0));
        module_name = std::string(
            file_.name(file_.module_unit(module_state_.unit).module_name));
    }
    cir::ModuleAttachmentId unit =
        import_module_unit_by_key(module_name, partition_name, loc);
    if (!unit.valid()) {
        return;
    }

    if (module_state_.unit.valid() && file_.valid(module_state_.unit)) {
        cir::ModuleUnitFact* fact = file_.module_unit_mut(module_state_.unit);
        std::vector<cir::ModuleAttachmentId>& edges =
            exported ? fact->exported_imports : fact->direct_imports;
        if (std::find(edges.begin(), edges.end(), unit) == edges.end()) {
            edges.push_back(unit);
        }
    }
    make_module_unit_visible(unit);
}

Session::ModuleVisibilityOverride::ModuleVisibilityOverride(
    Session& session, cir::ModuleAttachmentId unit)
    : session_(session) {
    if (!unit.valid() ||
        session.active_module_visibility_frame().unit == unit) {
        return;
    }
    auto saved = session.unit_visibility_frames_.find(unit.index);
    ModuleVisibilityFrame frame;
    frame.unit = unit;
    if (saved != session.unit_visibility_frames_.end()) {
        frame = saved->second;
    }
    session.module_visibility_stack_.push_back(std::move(frame));
    session.sync_module_visibility();
    active_ = true;
}

Session::ModuleVisibilityOverride::~ModuleVisibilityOverride() {
    if (!active_) {
        return;
    }
    session_.module_visibility_stack_.pop_back();
    session_.sync_module_visibility();
}

void Session::note_module_hidden_name(std::string_view name, SrcLoc loc) {
    (void)loc;
    if (!file_.has_module_units()) {
        return;
    }
    cir::File::ModuleVisibilityBypass bypass(file_);
    const cir::Binding* hidden =
        file_.lookup_ordinary_binding(current_decl_context(), name, true);
    if (!hidden) {
        return;
    }
    for (cir::EntityId id : hidden->entities) {
        if (!file_.valid(id) || file_.entity_lookup_visible(id)) {
            continue;
        }
        const cir::Entity& entity = file_.entity(id);
        if (!entity.origin_unit.valid()) {
            continue;
        }
        const cir::ModuleUnitFact& unit =
            file_.module_unit(entity.origin_unit);
        if (!unit.module_name.valid()) {
            continue;
        }
        report_note("'" + std::string(name) + "' is declared in module '" +
                        std::string(file_.name(unit.module_name)) +
                        "' but is not exported",
                    entity.loc);
        return;
    }
}

bool Session::in_module_interface_purview() const {
    const cir::File::ActiveModuleContext& active =
        file_.active_module_context();
    if (!active.unit.valid() ||
        active.fragment != cir::ModuleFragment::Purview) {
        return false;
    }
    const cir::ModuleUnitFact& fact = file_.module_unit(module_state_.unit);
    return fact.kind == cir::ModuleUnitFact::Kind::PrimaryInterface ||
           fact.kind == cir::ModuleUnitFact::Kind::InterfacePartition;
}

bool Session::begin_export_region(SrcLoc loc) {
    cir::File::ActiveModuleContext active = file_.active_module_context();
    if (active.export_depth > 0) {

        report_error("export declaration cannot appear inside another export "
                     "declaration",
                     loc);
        return false;
    }
    if (!in_module_interface_purview()) {
        report_error("export declaration can only appear in the purview of a "
                     "module interface unit",
                     loc);
        return false;
    }
    active.export_depth = 1;
    file_.set_active_module_context(active);
    return true;
}

void Session::end_export_region() {
    cir::File::ActiveModuleContext active = file_.active_module_context();
    if (active.export_depth > 0) {
        active.export_depth = 0;
        file_.set_active_module_context(active);
    }
}

} // namespace aburi::collect
