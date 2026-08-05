#ifndef ABURI_PREPROCESSOR_H
#define ABURI_PREPROCESSOR_H
#include <cstdint>
#include <filesystem>
#include <iosfwd>
#include <map>
#include <utility>
#include <unordered_set>

#include "source_mgnt.h"
#include "lexer.h"
#include "abi/target_info.h"
using ArgsType = std::vector<std::vector<Token>>;

class PerfProfiler;

struct PreprocPass {
    std::string pass_name;
    std::vector<MappingStep> steps;
    PreprocPass(std::string name): pass_name(name) {};
};
struct MacroDefinition {
    enum class BuiltinKind {
        None,
        Line,
        File,
        BaseFile,
        FileName,
        Counter,
        Date,
        Time,
        Stdc,
        StdcVersion,
        StdcHosted,
        CPlusPlus
    };
    std::string name;
    uint32_t name_ident = 0;
    SrcLoc def_loc;
    std::vector<Token> replacement_list;
    std::vector<std::string> parameters;
    bool is_function_like;
    bool is_variadic;
    BuiltinKind builtin_kind;
    MacroDefinition(): name(""), is_function_like(false), def_loc(0), builtin_kind(BuiltinKind::None) {}
    explicit MacroDefinition(std::string name, SrcLoc def_loc = SrcLoc()):
    name(std::move(name)), def_loc(def_loc), is_function_like(false), is_variadic(false),
        builtin_kind(BuiltinKind::None) {}
    int get_param_idx(const std::string &name) const {
        for (int i = 0; i < parameters.size(); ++i) {
            if (parameters[i] == name) {
                return i;
            }
        }
        return -1;
    }
    int variadic_param_index() const {
        if (!is_variadic || parameters.empty()) {
            return -1;
        }
        return static_cast<int>(parameters.size() - 1);
    }

};
enum class TokenSrcKind {
    Expansion,
    File,
};

struct TokenSrc {
    std::unique_ptr<Lexer> lex = nullptr;
    std::unique_ptr<TokenMgnt> token_mgnt = nullptr;
    bool isUsingMgnt;
    SrcLoc base_loc;
    const TokenSrcKind src_kind;
    TokenSrcKind get_src_kind() const { return src_kind; }
    virtual ~TokenSrc() = default;
protected:
    explicit TokenSrc(TokenSrcKind kind) : isUsingMgnt(false), src_kind(kind) {}
public:
    size_t get_idx();
    void set_idx(size_t idx);
    Token nextToken();
    bool isExhausted();
    Token peekToken() {
        if (isUsingMgnt) {
            return token_mgnt->peek_token(0);
        } else {
            auto state = lex->get_state();
            auto tok = nextToken();
            lex->set_state(state);
            return tok;
        }

    }

};
struct ExpansionTokenSrc: TokenSrc {
    ExpansionTokenSrc(std::vector<Token> toks, SrcLoc base_loc)
        : TokenSrc(TokenSrcKind::Expansion) {
        this->base_loc = base_loc;
        token_mgnt = std::make_unique<TokenMgnt>(std::move(toks));
        isUsingMgnt = true;
    }
    static bool classof(const TokenSrc *s) { return s->src_kind == TokenSrcKind::Expansion; }
};

void inital_preproc(std::string& text, std::vector<MappingStep>& map);
inline void ensure_initial_preprocessed(const std::shared_ptr<FileSrc>& file_src) {
    if (!file_src || file_src->initial_preprocessed) {
        return;
    }
    file_src->modified_buffer = file_src->buffer;
    file_src->change_lists.clear();
    inital_preproc(file_src->modified_buffer, file_src->change_lists);
    file_src->initial_preprocessed = true;
}
struct FileTokenSrc : TokenSrc {
    using TokenSrc::base_loc;
    std::shared_ptr<FileSrc> file_src;
    explicit FileTokenSrc(const std::shared_ptr<FileSrc>& file_src, SrcLoc base_loc,
        SourceManager* diag_sm = nullptr, const LangOptions& lang_opts = LangOptions(),
        IdentTable* idents = nullptr):
        TokenSrc(TokenSrcKind::File), file_src(file_src) {
        ensure_initial_preprocessed(file_src);
        std::string_view ref = file_src->modified_buffer;
        this->base_loc = base_loc;
        lex = std::make_unique<Lexer>(ref, base_loc, diag_sm, lang_opts);
        lex->set_phase2_source(file_src->buffer, &file_src->change_lists);
        lex->ident_table = idents;
        lex->enable_new_line_token = true;
        lex->emit_comment_whitespace = true;
        lex->pp_number_mode = true;
    }
    static bool classof(const TokenSrc *s) { return s->src_kind == TokenSrcKind::File; }
};

struct PreProcess {
    bool isProcessingConditional = false;
    int32_t current_file_id;
    std::vector<std::unique_ptr<TokenSrc>> tok_stack;
    std::shared_ptr<SourceManager> sm;
    IdentTable idents;
    std::unordered_map<uint32_t, MacroDefinition> macro_table;
    uint32_t intern_ident(std::string_view name);
    void install_macro(MacroDefinition mac);
    MacroDefinition* find_macro_by_name(std::string_view name);
    bool has_macro_name(std::string_view name) {
        return find_macro_by_name(name) != nullptr;
    }
    std::unordered_set<int32_t> pragma_once_included;
    std::unordered_set<int32_t> included_files;
    std::unordered_set<int32_t> import_once_included;
    struct MacroPushEntry {
        bool existed = false;
        MacroDefinition definition;
    };
    std::unordered_map<std::string, std::vector<MacroPushEntry>> macro_push_stack;
    std::vector<std::vector<uint32_t>> hide_sets_;
    std::map<std::vector<uint32_t>, HideSetId> hide_set_dedup_;
    std::unordered_map<uint64_t, HideSetId> hide_union_memo_;
    std::unordered_map<uint64_t, HideSetId> hide_intersect_memo_;
    std::unordered_map<uint64_t, HideSetId> hide_insert_memo_;
    HideSetId hide_set_intern(std::vector<uint32_t> sorted_names);
    HideSetId hide_set_insert(HideSetId set, uint32_t name_ident);
    HideSetId hide_set_union(HideSetId lhs, HideSetId rhs);
    HideSetId hide_set_intersect(HideSetId lhs, HideSetId rhs);
    bool hide_set_contains(HideSetId set, uint32_t name_ident) const;
    std::unordered_map<std::string, std::string> builtin_headers;
    bool builtin_headers_enabled = true;
    std::string builtin_date;
    std::string builtin_time;
    std::string base_file_name;
    std::shared_ptr<TargetInfo> target_info;
    LangOptions lang_opts;
    PerfProfiler* perf_profiler = nullptr;
    bool perf_full_detail = false;
    uint64_t perf_parser_tokens_emitted = 0;
    uint64_t perf_raw_tokens_lexed = 0;
    uint64_t counter = 0;
    enum class DefinedOperatorState : uint8_t {
        None = 0,
        SawDefined = 1,
        SawDefinedOpenParen = 2
    };
    DefinedOperatorState defined_state = DefinedOperatorState::None;
    size_t current_pack_alignment = 0;
    std::vector<size_t> pack_stack;
    uint32_t current_diag_state_id = 0;
    std::vector<uint32_t> diag_state_stack;
    struct ConditionalState {
        bool was_successful;
        bool is_active;
    };
    std::vector<ConditionalState> conditional_stack;
    bool skipping = false;

    TokenSrc * current_tok_src() const {
        return tok_stack.back().get();
    }
    void handleDefineDirective(SrcLoc def_loc);
    void handleUndefDirective(SrcLoc def_loc);
    void handleLineDirective(SrcLoc def_loc);
    void handleErrorDirective(SrcLoc def_loc);
    void handleWarningDirective(SrcLoc def_loc);
    void handlePragmaDirective(SrcLoc def_loc);
    void handlePragmaOperator(SrcLoc op_loc);
    void handlePragmaTokens(const std::vector<Token>& tokens, SrcLoc def_loc);
    void handlePackPragma(const std::vector<Token>& tokens, size_t start_idx, SrcLoc def_loc);
    void handleDiagnosticPragma(const std::vector<Token>& tokens, size_t start_idx, SrcLoc def_loc);
    void handleOptimizePragma(const std::vector<Token>& tokens, size_t start_idx, SrcLoc def_loc);

    void handleIncludeDirective(SrcLoc def_loc, bool is_next = false, bool is_import = false);
    enum class ModuleFileState : uint8_t { None, GlobalFragment, Purview, PrivateFragment };
    ModuleFileState module_file_state = ModuleFileState::None;
    std::deque<Token> module_line_pending_;
    bool try_module_directive(const Token& intro);
    void handleModuleDirective(const Token& intro, bool has_export, const Token& kw_tok);
    void handleImportDirective(const Token& intro, bool has_export, const Token& kw_tok);
    void handleIfDirective(SrcLoc loc);
    void handleIfDefDirective(SrcLoc loc, bool is_ifndef);
    void handleElseDirective(SrcLoc loc);
    void handleElifDirective(SrcLoc loc);
    void handleElifdefDirective(SrcLoc loc, bool is_elifndef);
    void handleEmbedDirective(SrcLoc loc);
    int evaluate_has_embed(const std::vector<Token>& arg_tokens, SrcLoc loc);
    void handleEndifDirective(SrcLoc loc);
    bool evaluateConstantExpression(std::vector<Token> tokens);
    void detect_include_guard(const std::shared_ptr<FileSrc>& file);
    bool parse_if_not_defined(const std::vector<Token>& tokens, std::string& macro) const;
    void define_object_macro(const std::string& name, const std::string& value, SrcLoc def_loc = SrcLoc());
    void undef_macro(const std::string& name);

    explicit PreProcess(std::string file_name, std::string content,
        std::shared_ptr<TargetInfo> target = nullptr,
        LangOptions options = LangOptions(),
        PerfProfiler* profiler = nullptr): macro_table({}), skipping(false), lang_opts(std::move(options)),
        perf_profiler(profiler) {
        if (!target) {
            target = TargetInfo::create_host();
        }
        target_info = target;
        base_file_name = file_name;
        sm = std::make_shared<SourceManager>();
        sm->perf_profiler = perf_profiler;
        current_diag_state_id = sm->defaultDiagnosticStateId();
        std::filesystem::path input_path(file_name);
        std::string main_directory = input_path.has_parent_path()
            ? input_path.parent_path().string()
            : std::string();
        auto main_sloc = sm->createFileEntry(std::move(file_name),
            std::move(content));
        main_sloc->directory = std::move(main_directory);
        current_file_id = main_sloc->file_id;
        tok_stack.push_back(std::make_unique<FileTokenSrc>(main_sloc, main_sloc->offset, sm.get(), lang_opts, &idents));
        included_files.insert(main_sloc->file_id);
        init_builtin_state();
        init_builtin_macros();
        init_target_macros(*target);
    }
    explicit PreProcess() {};
    void set_perf_profiler(PerfProfiler* profiler);
    void init_builtin_state();
    void init_builtin_macros();
    void init_target_macros(const TargetInfo& target);
    std::vector<Token> expand_builtin_macro(const MacroDefinition& mdef, const Token& trigger);
    Token nextToken_raw();
    Token nextToken(bool peeloff = false, size_t peelofflimit = 0);
    std::vector<Token> tokenize();
    bool push_pre_include(const std::string& file_name);
    void emit_preprocessed_text(std::ostream& out, bool line_markers = true);
    void emit_macro_definitions(std::ostream& out);
    void error(std::string err, SrcLoc loc = SrcLoc()) {
        SrcLoc curr_loc = loc;
        if (curr_loc.isInvalid() || sm == nullptr) {
            throw std::runtime_error("error: " + err);
        }
        throw std::runtime_error(sm->formatDiagnostic(DiagnosticLevel::Error, err, curr_loc));
    }
    void expand_object_macro(const Token& trigger, const MacroDefinition& m);

    std::vector<Token> subst(const MacroDefinition &mdef, const Token &trigger, const ArgsType &args);

    void expand_function_macro(const Token& trigger, const MacroDefinition& m);

    void peel_off_exhausted();
    bool skip_to_next_directive(Lexer* lex);
};
#endif //ABURI_PREPROCESSOR_H
