#include "ast_context.h"
#include "ast.h"
#include "abi/target_info.h"

// Static empty list returned by get_attrs when no attributes exist for a node
static const AttributeList empty_attr_list{};

namespace {
// Threading: g_active_side_table_ast_context is thread_local, so it is safe
// for per-thread use.  However, the registration map and ID counter below
// are plain globals with NO synchronization.  They are safe only under the
// current single-threaded compilation model.  If parallel compilation is
// introduced, protect with a mutex or move into a session-owned context.
thread_local ASTContext* g_active_side_table_ast_context = nullptr;
std::unordered_map<uint32_t, ASTContext*> g_registered_ast_contexts;
uint32_t g_next_ast_context_registry_id = 1;

ASTContext* lookup_registered_ast_context(uint32_t registry_id) {
    if (registry_id == 0) {
        return nullptr;
    }
    auto it = g_registered_ast_contexts.find(registry_id);
    if (it == g_registered_ast_contexts.end()) {
        return nullptr;
    }
    return it->second;
}

template<typename Map, typename Key>
typename Map::mapped_type* find_external_semantic_info(Map& map, const Key* key) {
    if (!key) {
        return nullptr;
    }
    auto it = map.find(key);
    if (it == map.end()) {
        return nullptr;
    }
    return &it->second;
}

template<typename Map, typename Key>
const typename Map::mapped_type* find_external_semantic_info(const Map& map,
                                                             const Key* key) {
    if (!key) {
        return nullptr;
    }
    auto it = map.find(key);
    if (it == map.end()) {
        return nullptr;
    }
    return &it->second;
}

template<typename Map, typename Key>
void erase_external_semantic_info_if_empty(Map& map, const Key* key) {
    if (!key) {
        return;
    }
    auto it = map.find(key);
    if (it != map.end() && it->second.empty()) {
        map.erase(it);
    }
}

void erase_func_decl_owner_if_unused(const ASTContext* context, const FuncDecl* decl) {
    if (!context || !decl) {
        return;
    }
    if (context->get_func_decl_cxx_qualifier_prefix(decl) != nullptr) {
        return;
    }
    if (context->get_func_decl_owner_record_type(decl)) {
        return;
    }
    if (context->get_func_decl_function_template_specialization(decl) != nullptr) {
        return;
    }
    if (decl->external_semantic_owner_id == context->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_symbol_owner_if_unused(const ASTContext* context, const Symbol* sym) {
    if (!context || !sym) {
        return;
    }
    if (context->get_symbol_cxx_qualifier_prefix(sym) != nullptr) {
        return;
    }
    if (context->get_symbol_owner_record_type(sym)) {
        return;
    }
    if (context->get_symbol_function_template_specialization(sym) != nullptr) {
        return;
    }
    if (context->get_symbol_cpp_default_arguments(sym) != nullptr) {
        return;
    }
    if (sym->external_semantic_owner_id == context->registry_id()) {
        sym->external_semantic_owner_id = 0;
    }
}

void erase_template_decl_owner_if_unused(const ASTContext* context,
                                         const TemplateDecl* decl) {
    if (!context || !decl) {
        return;
    }
    if (!decl->merged_default_arguments.empty()) {
        return;
    }
    const TemplateDecl* canonical = context->get_template_decl_canonical_decl(decl);
    if (canonical && canonical != decl) {
        return;
    }
    if (decl->external_semantic_owner_id == context->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_template_parameter_decl_owner_if_unused(const ASTContext* context,
                                                   const TemplateParameterDecl* decl) {
    if (!context || !decl) {
        return;
    }
    if (decl->default_argument.has_value()) {
        return;
    }
    if (decl->external_semantic_owner_id == context->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}

void erase_param_decl_owner_if_unused(const ASTContext* context,
                                      const ParamDecl* decl) {
    if (!context || !decl) {
        return;
    }
    if (context->get_param_decl_default_argument(decl) != nullptr) {
        return;
    }
    if (decl->external_semantic_owner_id == context->registry_id()) {
        decl->external_semantic_owner_id = 0;
    }
}
} // namespace

ASTContext* get_active_side_table_ast_context() {
    return g_active_side_table_ast_context;
}

ASTContext* get_side_table_ast_context_for(const FuncDecl* decl) {
    return decl ? lookup_registered_ast_context(decl->external_semantic_owner_id)
                : nullptr;
}

ASTContext* get_side_table_ast_context_for(const TemplateDecl* decl) {
    return decl ? lookup_registered_ast_context(decl->external_semantic_owner_id)
                : nullptr;
}

ASTContext* get_side_table_ast_context_for(const TemplateParameterDecl* decl) {
    return decl ? lookup_registered_ast_context(decl->external_semantic_owner_id)
                : nullptr;
}

ASTContext* get_side_table_ast_context_for(const ParamDecl* decl) {
    return decl ? lookup_registered_ast_context(decl->external_semantic_owner_id)
                : nullptr;
}

ASTContext* get_side_table_ast_context_for(const Symbol* sym) {
    return sym ? lookup_registered_ast_context(sym->external_semantic_owner_id)
               : nullptr;
}

ASTContextSideTableScope::ASTContextSideTableScope(ASTContext* context)
    : previous_context_(g_active_side_table_ast_context) {
    g_active_side_table_ast_context = context;
}

ASTContextSideTableScope::~ASTContextSideTableScope() {
    g_active_side_table_ast_context = previous_context_;
}

ASTContext::ASTContext()
    : type_ctx(std::make_shared<TypeContext>()),
      global_tracker(std::make_shared<GlobalIdentTracker>()),
      abi_policy(std::make_shared<AbiPolicy>()) {
    registry_id_ = g_next_ast_context_registry_id++;
    g_registered_ast_contexts[registry_id_] = this;
    if (type_ctx && type_ctx->target) {
        *abi_policy = abi_policy_for_target(*type_ctx->target);
    }
}

ASTContext::ASTContext(std::shared_ptr<TargetInfo> ti)
    : type_ctx(std::make_shared<TypeContext>(std::move(ti))),
      global_tracker(std::make_shared<GlobalIdentTracker>()),
      abi_policy(std::make_shared<AbiPolicy>()) {
    registry_id_ = g_next_ast_context_registry_id++;
    g_registered_ast_contexts[registry_id_] = this;
    if (type_ctx && type_ctx->target) {
        *abi_policy = abi_policy_for_target(*type_ctx->target);
    }
}

ASTContext::~ASTContext() {
    if (g_active_side_table_ast_context == this) {
        g_active_side_table_ast_context = nullptr;
    }
    if (registry_id_ != 0) {
        auto it = g_registered_ast_contexts.find(registry_id_);
        if (it != g_registered_ast_contexts.end() && it->second == this) {
            g_registered_ast_contexts.erase(it);
        }
    }
}

const std::string* ASTContext::intern_identifier(std::string_view spelling) {
    auto [it, inserted] = identifier_pool_.emplace(spelling);
    if (inserted) {
        identifier_pool_string_storage_bytes_ += it->capacity() + 1;
    }
    return &(*it);
}

size_t ASTContext::identifier_pool_memory_usage_bytes() const {
    return sizeof(identifier_pool_) +
           identifier_pool_.bucket_count() * sizeof(void*) +
           identifier_pool_.size() * sizeof(std::string) +
           identifier_pool_string_storage_bytes_;
}

void ASTContext::set_func_decl_cxx_qualifier_prefix(
    const FuncDecl* decl,
    std::optional<std::string> prefix) {
    if (!decl) {
        return;
    }
    auto& info = func_decl_semantic_info_map_[decl];
    if (!prefix.has_value() || prefix->empty()) {
        info.cxx_qualifier_prefix = nullptr;
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
        return;
    }
    auto [it, _] = external_qualifier_pool_.emplace(std::move(*prefix));
    info.cxx_qualifier_prefix = &(*it);
    decl->external_semantic_owner_id = registry_id_;
}

const std::string* ASTContext::get_func_decl_cxx_qualifier_prefix(
    const FuncDecl* decl) const {
    const auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
    if (!info) {
        return nullptr;
    }
    return info->cxx_qualifier_prefix;
}

void ASTContext::clear_func_decl_cxx_qualifier_prefixes() {
    std::vector<const FuncDecl*> decls;
    decls.reserve(func_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : func_decl_semantic_info_map_) {
        if (info.cxx_qualifier_prefix != nullptr) {
            decls.push_back(decl);
        }
    }
    for (const FuncDecl* decl : decls) {
        auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
        if (info) {
            info->cxx_qualifier_prefix = nullptr;
        }
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
    }
}

void ASTContext::set_func_decl_owner_record_type(const FuncDecl* decl,
                                                 QualType owner_type) {
    if (!decl) {
        return;
    }
    auto& info = func_decl_semantic_info_map_[decl];
    if (!owner_type) {
        info.owner_record_type = QualType();
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
        return;
    }
    info.owner_record_type = owner_type;
    decl->external_semantic_owner_id = registry_id_;
}

QualType ASTContext::get_func_decl_owner_record_type(const FuncDecl* decl) const {
    const auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
    if (!info) {
        return QualType();
    }
    return info->owner_record_type;
}

void ASTContext::clear_func_decl_owner_record_types() {
    std::vector<const FuncDecl*> decls;
    decls.reserve(func_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : func_decl_semantic_info_map_) {
        if (info.owner_record_type) {
            decls.push_back(decl);
        }
    }
    for (const FuncDecl* decl : decls) {
        auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
        if (info) {
            info->owner_record_type = QualType();
        }
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
    }
}

void ASTContext::set_func_decl_function_template_specialization(
    const FuncDecl* decl,
    FunctionTemplateSpecializationInfo info) {
    if (!decl) {
        return;
    }
    auto& decl_info = func_decl_semantic_info_map_[decl];
    if (!info.primary_template) {
        decl_info.function_template_specialization.reset();
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
        return;
    }
    decl_info.function_template_specialization = std::move(info);
    decl->external_semantic_owner_id = registry_id_;
}

const FunctionTemplateSpecializationInfo*
ASTContext::get_func_decl_function_template_specialization(
    const FuncDecl* decl) const {
    const auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
    if (!info || !info->function_template_specialization.has_value()) {
        return nullptr;
    }
    return &(*info->function_template_specialization);
}

void ASTContext::clear_func_decl_function_template_specializations() {
    std::vector<const FuncDecl*> decls;
    decls.reserve(func_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : func_decl_semantic_info_map_) {
        if (info.function_template_specialization.has_value()) {
            decls.push_back(decl);
        }
    }
    for (const FuncDecl* decl : decls) {
        auto* info = find_external_semantic_info(func_decl_semantic_info_map_, decl);
        if (info) {
            info->function_template_specialization.reset();
        }
        erase_external_semantic_info_if_empty(func_decl_semantic_info_map_, decl);
        erase_func_decl_owner_if_unused(this, decl);
    }
}

void ASTContext::set_template_decl_canonical_decl(
    const TemplateDecl* decl,
    const TemplateDecl* canonical_decl) {
    if (!decl) {
        return;
    }
    tracked_template_decls_.insert(decl);
    if (canonical_decl) {
        tracked_template_decls_.insert(canonical_decl);
    }
    if (!canonical_decl) {
        decl->canonical_decl = nullptr;
        erase_template_decl_owner_if_unused(this, decl);
        return;
    }
    decl->canonical_decl = canonical_decl;
    decl->external_semantic_owner_id = registry_id_;
    canonical_decl->external_semantic_owner_id = registry_id_;
}

const TemplateDecl* ASTContext::get_template_decl_canonical_decl(
    const TemplateDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    const TemplateDecl* current = decl;
    for (size_t depth = 0; depth < 64; ++depth) {
        const TemplateDecl* next = current->canonical_decl;
        if (!next) {
            return current;
        }
        if (next == current) {
            return current;
        }
        current = next;
    }
    return current;
}

void ASTContext::clear_template_decl_canonical_decls() {
    std::vector<const TemplateDecl*> decls(
        tracked_template_decls_.begin(),
        tracked_template_decls_.end());
    for (const TemplateDecl* decl : decls) {
        if (decl) {
            decl->canonical_decl = nullptr;
        }
    }
    for (const TemplateDecl* decl : decls) {
        erase_template_decl_owner_if_unused(this, decl);
    }
}

void ASTContext::set_template_parameter_default_argument(
    const TemplateParameterDecl* decl,
    std::optional<TemplateArgument> argument) {
    if (!decl) {
        return;
    }
    tracked_template_parameter_decls_.insert(decl);
    if (!argument.has_value()) {
        decl->default_argument.reset();
        erase_template_parameter_decl_owner_if_unused(this, decl);
        return;
    }
    decl->default_argument = std::move(*argument);
    decl->external_semantic_owner_id = registry_id_;
}

const TemplateArgument* ASTContext::get_template_parameter_default_argument(
    const TemplateParameterDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    if (!decl->default_argument.has_value()) {
        return nullptr;
    }
    return &(*decl->default_argument);
}

void ASTContext::clear_template_parameter_default_arguments() {
    std::vector<const TemplateParameterDecl*> decls(
        tracked_template_parameter_decls_.begin(),
        tracked_template_parameter_decls_.end());
    for (const TemplateParameterDecl* decl : decls) {
        if (decl) {
            decl->default_argument.reset();
        }
    }
    for (const TemplateParameterDecl* decl : decls) {
        erase_template_parameter_decl_owner_if_unused(this, decl);
    }
}

bool ASTContext::merge_template_decl_default_arguments(
    const TemplateDecl* decl,
    size_t* conflict_param_index) {
    if (!decl) {
        return true;
    }

    const TemplateDecl* canonical = get_template_decl_canonical_decl(decl);
    if (!canonical) {
        canonical = decl;
    }

    tracked_template_decls_.insert(canonical);
    canonical->external_semantic_owner_id = registry_id_;
    auto& merged_defaults = canonical->merged_default_arguments;
    if (merged_defaults.size() < decl->parameters.size()) {
        merged_defaults.resize(decl->parameters.size());
    }

    for (size_t index = 0; index < decl->parameters.size(); ++index) {
        const auto* parameter = decl->parameters[index].get();
        const TemplateArgument* incoming_default =
            parameter ? get_template_parameter_default_argument(parameter) : nullptr;
        if (!incoming_default) {
            continue;
        }
        if (merged_defaults[index].has_value()) {
            if (conflict_param_index) {
                *conflict_param_index = index;
            }
            return false;
        }
        merged_defaults[index] = *incoming_default;
    }
    return true;
}

const std::vector<std::optional<TemplateArgument>>*
ASTContext::get_template_decl_default_arguments(const TemplateDecl* decl) const {
    if (!decl) {
        return nullptr;
    }
    const TemplateDecl* canonical = get_template_decl_canonical_decl(decl);
    const TemplateDecl* owner = canonical ? canonical : decl;
    if (!owner || owner->merged_default_arguments.empty()) {
        return nullptr;
    }
    return &owner->merged_default_arguments;
}

void ASTContext::clear_template_decl_default_arguments() {
    for (const TemplateDecl* decl : tracked_template_decls_) {
        if (decl) {
            decl->merged_default_arguments.clear();
        }
    }
    for (const TemplateDecl* decl : tracked_template_decls_) {
        erase_template_decl_owner_if_unused(this, decl);
    }
}

void ASTContext::set_param_decl_default_argument(const ParamDecl* decl,
                                                 std::unique_ptr<Expr> expr) {
    if (!decl) {
        return;
    }
    auto& info = param_decl_semantic_info_map_[decl];
    if (!expr) {
        info.default_argument.reset();
        erase_external_semantic_info_if_empty(param_decl_semantic_info_map_, decl);
        erase_param_decl_owner_if_unused(this, decl);
        return;
    }
    info.default_argument = std::move(expr);
    decl->external_semantic_owner_id = registry_id_;
}

const Expr* ASTContext::get_param_decl_default_argument(
    const ParamDecl* decl) const {
    const auto* info = find_external_semantic_info(param_decl_semantic_info_map_, decl);
    if (!info || !info->default_argument) {
        return nullptr;
    }
    return info->default_argument.get();
}

void ASTContext::clear_param_decl_default_arguments() {
    std::vector<const ParamDecl*> decls;
    decls.reserve(param_decl_semantic_info_map_.size());
    for (const auto& [decl, info] : param_decl_semantic_info_map_) {
        if (info.default_argument) {
            decls.push_back(decl);
        }
    }
    for (const ParamDecl* decl : decls) {
        auto* info = find_external_semantic_info(param_decl_semantic_info_map_, decl);
        if (info) {
            info->default_argument.reset();
        }
        erase_external_semantic_info_if_empty(param_decl_semantic_info_map_, decl);
        erase_param_decl_owner_if_unused(this, decl);
    }
}

void ASTContext::set_symbol_cxx_qualifier_prefix(
    const Symbol* sym,
    std::optional<std::string> prefix) {
    if (!sym) {
        return;
    }
    auto& info = symbol_semantic_info_map_[sym];
    if (!prefix.has_value() || prefix->empty()) {
        info.cxx_qualifier_prefix = nullptr;
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    auto [it, _] = external_qualifier_pool_.emplace(std::move(*prefix));
    info.cxx_qualifier_prefix = &(*it);
    sym->external_semantic_owner_id = registry_id_;
}

const std::string* ASTContext::get_symbol_cxx_qualifier_prefix(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info) {
        return nullptr;
    }
    return info->cxx_qualifier_prefix;
}

void ASTContext::clear_symbol_cxx_qualifier_prefixes() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.cxx_qualifier_prefix != nullptr) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->cxx_qualifier_prefix = nullptr;
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void ASTContext::set_symbol_owner_record_type(const Symbol* sym,
                                              QualType owner_type) {
    if (!sym) {
        return;
    }
    auto& info = symbol_semantic_info_map_[sym];
    if (!owner_type) {
        info.owner_record_type = QualType();
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    info.owner_record_type = owner_type;
    sym->external_semantic_owner_id = registry_id_;
}

QualType ASTContext::get_symbol_owner_record_type(const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info) {
        return QualType();
    }
    return info->owner_record_type;
}

void ASTContext::clear_symbol_owner_record_types() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.owner_record_type) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->owner_record_type = QualType();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void ASTContext::set_symbol_function_template_specialization(
    const Symbol* sym,
    FunctionTemplateSpecializationInfo info) {
    if (!sym) {
        return;
    }
    auto& sym_info = symbol_semantic_info_map_[sym];
    if (!info.primary_template) {
        sym_info.function_template_specialization.reset();
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
        return;
    }
    sym_info.function_template_specialization = std::move(info);
    sym->external_semantic_owner_id = registry_id_;
}

const FunctionTemplateSpecializationInfo*
ASTContext::get_symbol_function_template_specialization(const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info || !info->function_template_specialization.has_value()) {
        return nullptr;
    }
    return &(*info->function_template_specialization);
}

void ASTContext::clear_symbol_function_template_specializations() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (info.function_template_specialization.has_value()) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->function_template_specialization.reset();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

bool ASTContext::merge_symbol_cpp_default_arguments(
    const Symbol* sym,
    const std::vector<const Expr*>& defaults,
    size_t* conflict_param_index) {
    if (!sym) {
        return true;
    }

    auto [it, inserted] = symbol_semantic_info_map_.try_emplace(sym);
    sym->external_semantic_owner_id = registry_id_;
    auto& merged_defaults = it->second.cpp_default_arguments;
    if (inserted) {
        merged_defaults.assign(defaults.begin(), defaults.end());
        return true;
    }

    if (merged_defaults.size() < defaults.size()) {
        merged_defaults.resize(defaults.size(), nullptr);
    }

    for (size_t index = 0; index < defaults.size(); ++index) {
        const Expr* incoming_default = defaults[index];
        if (!incoming_default) {
            continue;
        }
        if (merged_defaults[index]) {
            if (conflict_param_index) {
                *conflict_param_index = index;
            }
            return false;
        }
        merged_defaults[index] = incoming_default;
    }

    return true;
}

const std::vector<const Expr*>* ASTContext::get_symbol_cpp_default_arguments(
    const Symbol* sym) const {
    const auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
    if (!info || info->cpp_default_arguments.empty()) {
        return nullptr;
    }
    return &info->cpp_default_arguments;
}

void ASTContext::clear_symbol_cpp_default_arguments() {
    std::vector<const Symbol*> symbols;
    symbols.reserve(symbol_semantic_info_map_.size());
    for (const auto& [sym, info] : symbol_semantic_info_map_) {
        if (!info.cpp_default_arguments.empty()) {
            symbols.push_back(sym);
        }
    }
    for (const Symbol* sym : symbols) {
        auto* info = find_external_semantic_info(symbol_semantic_info_map_, sym);
        if (info) {
            info->cpp_default_arguments.clear();
        }
        erase_external_semantic_info_if_empty(symbol_semantic_info_map_, sym);
        erase_symbol_owner_if_unused(this, sym);
    }
}

void ASTContext::set_template_specialization_resolved_type(
    const TemplateSpecializationType* type,
    std::shared_ptr<CType> resolved_type) {
    if (!type) {
        return;
    }
    if (!resolved_type) {
        template_specialization_resolved_type_map_.erase(type);
        return;
    }
    template_specialization_resolved_type_map_[type] = std::move(resolved_type);
}

std::shared_ptr<CType> ASTContext::get_template_specialization_resolved_type(
    const TemplateSpecializationType* type) const {
    if (!type) {
        return nullptr;
    }
    auto it = template_specialization_resolved_type_map_.find(type);
    if (it == template_specialization_resolved_type_map_.end()) {
        return nullptr;
    }
    return it->second;
}

void ASTContext::clear_template_specialization_resolved_types() {
    template_specialization_resolved_type_map_.clear();
}

void ASTContext::set_dependent_name_resolved_type(
    const DependentNameType* type,
    std::shared_ptr<CType> resolved_type) {
    if (!type) {
        return;
    }
    if (!resolved_type) {
        dependent_name_resolved_type_map_.erase(type);
        return;
    }
    dependent_name_resolved_type_map_[type] = std::move(resolved_type);
}

std::shared_ptr<CType> ASTContext::get_dependent_name_resolved_type(
    const DependentNameType* type) const {
    if (!type) {
        return nullptr;
    }
    auto it = dependent_name_resolved_type_map_.find(type);
    if (it == dependent_name_resolved_type_map_.end()) {
        return nullptr;
    }
    return it->second;
}

void ASTContext::clear_dependent_name_resolved_types() {
    dependent_name_resolved_type_map_.clear();
}

ClassTemplateSpecializationEntry* ASTContext::lookup_class_template_specialization(
    std::string_view canonical_key) {
    auto it = class_template_specialization_lookup_.find(std::string(canonical_key));
    if (it == class_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= class_template_specializations_.size()) {
        return nullptr;
    }
    return class_template_specializations_[it->second].get();
}

const ClassTemplateSpecializationEntry*
ASTContext::lookup_class_template_specialization(std::string_view canonical_key) const {
    auto it = class_template_specialization_lookup_.find(std::string(canonical_key));
    if (it == class_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= class_template_specializations_.size()) {
        return nullptr;
    }
    return class_template_specializations_[it->second].get();
}

ClassTemplateSpecializationEntry&
ASTContext::get_or_create_class_template_specialization(
    std::string canonical_key,
    const ClassTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::shared_ptr<ObjectType> specialization_type,
    std::unique_ptr<ObjectDecl> specialization_decl) {
    auto existing = lookup_class_template_specialization(canonical_key);
    if (existing) {
        return *existing;
    }

    auto entry = std::make_unique<ClassTemplateSpecializationEntry>();
    entry->primary_template = primary_template;
    entry->canonical_key = canonical_key;
    entry->arguments = std::move(arguments);
    entry->specialization_type = std::move(specialization_type);
    entry->specialization_decl = std::move(specialization_decl);

    size_t index = class_template_specializations_.size();
    class_template_specialization_lookup_.emplace(entry->canonical_key, index);
    class_template_specializations_.push_back(std::move(entry));
    return *class_template_specializations_.back();
}

FunctionTemplateSpecializationEntry*
ASTContext::lookup_function_template_specialization(std::string_view canonical_key) {
    auto it = function_template_specialization_lookup_.find(std::string(canonical_key));
    if (it == function_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= function_template_specializations_.size()) {
        return nullptr;
    }
    return function_template_specializations_[it->second].get();
}

const FunctionTemplateSpecializationEntry*
ASTContext::lookup_function_template_specialization(std::string_view canonical_key) const {
    auto it = function_template_specialization_lookup_.find(std::string(canonical_key));
    if (it == function_template_specialization_lookup_.end()) {
        return nullptr;
    }
    if (it->second >= function_template_specializations_.size()) {
        return nullptr;
    }
    return function_template_specializations_[it->second].get();
}

FunctionTemplateSpecializationEntry&
ASTContext::get_or_create_function_template_specialization(
    std::string canonical_key,
    const FunctionTemplateDecl* primary_template,
    std::vector<TemplateArgument> arguments,
    std::unique_ptr<FuncDecl> specialization_decl,
    std::shared_ptr<Symbol> specialization_symbol) {
    auto existing = lookup_function_template_specialization(canonical_key);
    if (existing) {
        return *existing;
    }

    auto entry = std::make_unique<FunctionTemplateSpecializationEntry>();
    entry->primary_template = primary_template;
    entry->canonical_key = canonical_key;
    entry->arguments = std::move(arguments);
    entry->specialization_decl = std::move(specialization_decl);
    entry->specialization_symbol = std::move(specialization_symbol);

    size_t index = function_template_specializations_.size();
    function_template_specialization_lookup_.emplace(entry->canonical_key, index);
    function_template_specializations_.push_back(std::move(entry));
    return *function_template_specializations_.back();
}

bool ASTContext::push_template_instantiation_frame(size_t max_depth) {
    if (template_instantiation_depth_ >= max_depth) {
        return false;
    }
    ++template_instantiation_depth_;
    return true;
}

void ASTContext::pop_template_instantiation_frame() {
    if (template_instantiation_depth_ > 0) {
        --template_instantiation_depth_;
    }
}

void ASTContext::clear_external_semantic_side_tables() {
    clear_func_decl_cxx_qualifier_prefixes();
    clear_func_decl_owner_record_types();
    clear_func_decl_function_template_specializations();
    clear_template_decl_canonical_decls();
    clear_template_parameter_default_arguments();
    clear_template_decl_default_arguments();
    clear_symbol_cxx_qualifier_prefixes();
    clear_symbol_owner_record_types();
    clear_symbol_function_template_specializations();
    clear_param_decl_default_arguments();
    clear_symbol_cpp_default_arguments();
    clear_template_specialization_resolved_types();
    clear_dependent_name_resolved_types();
    external_qualifier_pool_.clear();
}

void ASTContext::retain_external_decl(std::unique_ptr<Decl> decl) {
    if (!decl) {
        return;
    }
    retained_external_decls_.push_back(std::move(decl));
}

// --- Attribute side table ---

void ASTContext::set_attrs(uint32_t id, AttributeList attrs) {
    attr_table_[id] = std::move(attrs);
}

void ASTContext::append_attrs(uint32_t id, std::vector<ParsedAttribute>&& attrs) {
    if (attrs.empty()) return;
    attr_table_[id].append(std::move(attrs));
}

const AttributeList& ASTContext::get_attrs(uint32_t id) const {
    auto* found = attr_table_.find(id);
    if (found) return *found;
    return empty_attr_list;
}

AttributeList& ASTContext::get_attrs_mut(uint32_t id) {
    return attr_table_[id];
}

bool ASTContext::has_attrs(uint32_t id) const {
    return attr_table_.contains(id);
}

// --- Bitfield side table ---

void ASTContext::set_bitfield_info(uint32_t id, BitfieldInfo info) {
    bitfield_table_[id] = info;
}

BitfieldInfo* ASTContext::get_bitfield_info(uint32_t id) {
    return bitfield_table_.find(id);
}

const BitfieldInfo* ASTContext::get_bitfield_info(uint32_t id) const {
    return bitfield_table_.find(id);
}

// --- C++ member-declaration side table ---

void ASTContext::set_cpp_member_decl_info(uint32_t id, CppMemberDeclInfo info) {
    cpp_member_decl_info_table_[id] = info;
}

CppMemberDeclInfo* ASTContext::get_cpp_member_decl_info(uint32_t id) {
    return cpp_member_decl_info_table_.find(id);
}

const CppMemberDeclInfo* ASTContext::get_cpp_member_decl_info(uint32_t id) const {
    return cpp_member_decl_info_table_.find(id);
}

bool ASTContext::has_cpp_member_decl_info(uint32_t id) const {
    return cpp_member_decl_info_table_.contains(id);
}

// --- C++ variable-destructor side table ---

void ASTContext::set_cpp_variable_destructor_symbol(uint32_t id,
                                                    std::shared_ptr<Symbol> sym) {
    if (!sym) {
        cpp_variable_destructor_table_.erase(id);
        return;
    }
    cpp_variable_destructor_table_[id] = std::move(sym);
}

std::shared_ptr<Symbol>* ASTContext::get_cpp_variable_destructor_symbol(uint32_t id) {
    return cpp_variable_destructor_table_.find(id);
}

const std::shared_ptr<Symbol>* ASTContext::get_cpp_variable_destructor_symbol(
    uint32_t id) const {
    return cpp_variable_destructor_table_.find(id);
}

bool ASTContext::has_cpp_variable_destructor_symbol(uint32_t id) const {
    return cpp_variable_destructor_table_.contains(id);
}

// --- C++ virtual-call side table ---

void ASTContext::set_cpp_virtual_call_info(uint32_t id, CppVirtualCallInfo info) {
    cpp_virtual_call_info_table_[id] = std::move(info);
}

CppVirtualCallInfo* ASTContext::get_cpp_virtual_call_info(uint32_t id) {
    return cpp_virtual_call_info_table_.find(id);
}

const CppVirtualCallInfo* ASTContext::get_cpp_virtual_call_info(uint32_t id) const {
    return cpp_virtual_call_info_table_.find(id);
}

bool ASTContext::has_cpp_virtual_call_info(uint32_t id) const {
    return cpp_virtual_call_info_table_.contains(id);
}

void ASTContext::set_cpp_lambda_closure_decl_info(uint32_t id,
                                                  CppLambdaClosureDeclInfo info) {
    cpp_lambda_closure_decl_info_table_[id] = std::move(info);
}

CppLambdaClosureDeclInfo* ASTContext::get_cpp_lambda_closure_decl_info(uint32_t id) {
    return cpp_lambda_closure_decl_info_table_.find(id);
}

const CppLambdaClosureDeclInfo* ASTContext::get_cpp_lambda_closure_decl_info(
    uint32_t id) const {
    return cpp_lambda_closure_decl_info_table_.find(id);
}

bool ASTContext::has_cpp_lambda_closure_decl_info(uint32_t id) const {
    return cpp_lambda_closure_decl_info_table_.contains(id);
}

void ASTContext::set_cpp_lambda_invoker_info(uint32_t id,
                                             CppLambdaInvokerInfo info) {
    cpp_lambda_invoker_info_table_[id] = std::move(info);
}

CppLambdaInvokerInfo* ASTContext::get_cpp_lambda_invoker_info(uint32_t id) {
    return cpp_lambda_invoker_info_table_.find(id);
}

const CppLambdaInvokerInfo* ASTContext::get_cpp_lambda_invoker_info(
    uint32_t id) const {
    return cpp_lambda_invoker_info_table_.find(id);
}

bool ASTContext::has_cpp_lambda_invoker_info(uint32_t id) const {
    return cpp_lambda_invoker_info_table_.contains(id);
}
