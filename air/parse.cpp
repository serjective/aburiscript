#include "parse.h"

#include "builder.h"

#include <cassert>
#include <cctype>
#include <unordered_map>

namespace aburi::air {

namespace {

enum class Tok : uint8_t {
    Ident,
    Local,
    Global,
    Int,
    HexInt,
    Str,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Equals,
    Dot,
    Arrow,
    Ellipsis,
    Plus,
    Minus,
    End,
};

struct Token {
    Tok kind = Tok::End;
    std::string_view text;
    uint32_t line = 1;
    uint32_t col = 1;
};

struct ParseException {
    ParseError error;
};

[[noreturn]] void fail(const Token& token, std::string message) {
    throw ParseException{ParseError{std::move(message), token.line, token.col}};
}

bool is_ident_char(char c) {
    return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$' ||
           c == '.';
}

bool is_canonical_value_name(std::string_view name) {
    if (name.size() < 2 || name[0] != 'v') {
        return false;
    }
    for (size_t i = 1; i < name.size(); ++i) {
        if (!std::isdigit(static_cast<unsigned char>(name[i]))) {
            return false;
        }
    }
    return true;
}

std::vector<Token> lex(std::string_view text) {
    std::vector<Token> tokens;
    uint32_t line = 1;
    uint32_t col = 1;
    size_t i = 0;
    auto advance = [&](size_t n) {
        for (size_t k = 0; k < n; ++k) {
            if (text[i + k] == '\n') {
                ++line;
                col = 1;
            } else {
                ++col;
            }
        }
        i += n;
    };
    auto push = [&](Tok kind, size_t len) {
        tokens.push_back({kind, text.substr(i, len), line, col});
        advance(len);
    };

    while (i < text.size()) {
        char c = text[i];
        if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
            advance(1);
            continue;
        }
        if (c == ';') {
            while (i < text.size() && text[i] != '\n') {
                advance(1);
            }
            continue;
        }
        if (c == '%' || c == '@') {
            size_t len = 1;
            while (i + len < text.size() && is_ident_char(text[i + len])) {
                ++len;
            }
            if (len == 1) {
                Token token{Tok::Local, text.substr(i, 1), line, col};
                fail(token, std::string("expected a name after '") + c + "'");
            }
            push(c == '%' ? Tok::Local : Tok::Global, len);
            continue;
        }
        if (std::isdigit(static_cast<unsigned char>(c))) {
            if (c == '0' && i + 1 < text.size() &&
                (text[i + 1] == 'x' || text[i + 1] == 'X')) {
                size_t len = 2;
                while (i + len < text.size() &&
                       std::isxdigit(static_cast<unsigned char>(text[i + len]))) {
                    ++len;
                }
                push(Tok::HexInt, len);
            } else {
                size_t len = 1;
                while (i + len < text.size() &&
                       std::isdigit(static_cast<unsigned char>(text[i + len]))) {
                    ++len;
                }
                push(Tok::Int, len);
            }
            continue;
        }
        if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
            size_t len = 1;
            while (i + len < text.size() && is_ident_char(text[i + len]) &&
                   text[i + len] != '.') {
                ++len;
            }
            push(Tok::Ident, len);
            continue;
        }
        if (c == '"') {
            size_t len = 1;
            bool closed = false;
            while (i + len < text.size()) {
                char s = text[i + len];
                if (s == '\\') {
                    len += 2;
                    continue;
                }
                ++len;
                if (s == '"') {
                    closed = true;
                    break;
                }
            }
            Token token{Tok::Str, text.substr(i, len), line, col};
            if (!closed) {
                fail(token, "unterminated string literal");
            }
            tokens.push_back(token);
            advance(len);
            continue;
        }
        switch (c) {
            case '(': push(Tok::LParen, 1); continue;
            case ')': push(Tok::RParen, 1); continue;
            case '{': push(Tok::LBrace, 1); continue;
            case '}': push(Tok::RBrace, 1); continue;
            case '[': push(Tok::LBracket, 1); continue;
            case ']': push(Tok::RBracket, 1); continue;
            case ',': push(Tok::Comma, 1); continue;
            case ':': push(Tok::Colon, 1); continue;
            case '=': push(Tok::Equals, 1); continue;
            case '+': push(Tok::Plus, 1); continue;
            case '.':
                if (i + 2 < text.size() && text[i + 1] == '.' && text[i + 2] == '.') {
                    push(Tok::Ellipsis, 3);
                } else {
                    push(Tok::Dot, 1);
                }
                continue;
            case '-':
                if (i + 1 < text.size() && text[i + 1] == '>') {
                    push(Tok::Arrow, 2);
                } else {
                    push(Tok::Minus, 1);
                }
                continue;
            default: {
                Token token{Tok::End, text.substr(i, 1), line, col};
                fail(token, "unexpected character '" + std::string(1, c) + "'");
            }
        }
    }
    tokens.push_back({Tok::End, {}, line, col});
    return tokens;
}

uint64_t parse_decimal(const Token& token) {
    uint64_t value = 0;
    for (char c : token.text) {
        uint64_t digit = static_cast<uint64_t>(c - '0');
        if (value > (UINT64_MAX - digit) / 10) {
            fail(token, "integer literal does not fit in 64 bits");
        }
        value = value * 10 + digit;
    }
    return value;
}

void parse_hex(const Token& token, uint64_t& low, uint64_t& high) {
    std::string_view digits = token.text.substr(2);
    if (digits.empty() || digits.size() > 32) {
        fail(token, "hex literal must have 1 to 32 digits");
    }
    low = 0;
    high = 0;
    for (char c : digits) {
        uint64_t digit;
        if (c >= '0' && c <= '9') {
            digit = static_cast<uint64_t>(c - '0');
        } else if (c >= 'a' && c <= 'f') {
            digit = static_cast<uint64_t>(c - 'a' + 10);
        } else {
            digit = static_cast<uint64_t>(c - 'A' + 10);
        }
        high = (high << 4) | (low >> 60);
        low = (low << 4) | digit;
    }
}

std::vector<uint8_t> unescape_bytes(const Token& token) {
    std::string_view body = token.text.substr(1, token.text.size() - 2);
    std::vector<uint8_t> bytes;
    for (size_t i = 0; i < body.size(); ++i) {
        if (body[i] != '\\') {
            bytes.push_back(static_cast<uint8_t>(body[i]));
            continue;
        }
        if (i + 1 >= body.size()) {
            fail(token, "dangling escape in string literal");
        }
        char next = body[i + 1];
        if (next == '\\' || next == '"') {
            bytes.push_back(static_cast<uint8_t>(next));
            ++i;
            continue;
        }
        if (i + 2 >= body.size() ||
            !std::isxdigit(static_cast<unsigned char>(body[i + 1])) ||
            !std::isxdigit(static_cast<unsigned char>(body[i + 2]))) {
            fail(token, "invalid escape in string literal");
        }
        auto hex_value = [](char c) -> uint8_t {
            if (c >= '0' && c <= '9') return static_cast<uint8_t>(c - '0');
            if (c >= 'a' && c <= 'f') return static_cast<uint8_t>(c - 'a' + 10);
            return static_cast<uint8_t>(c - 'A' + 10);
        };
        bytes.push_back(
            static_cast<uint8_t>(hex_value(body[i + 1]) << 4 | hex_value(body[i + 2])));
        i += 2;
    }
    return bytes;
}

std::string unescape_string(const Token& token) {
    std::vector<uint8_t> bytes = unescape_bytes(token);
    return std::string(bytes.begin(), bytes.end());
}

struct BlockHeader {
    size_t start = 0;
    size_t end = 0;
    BlockId block;
};

struct ValueFixup {
    std::string name;
    Token token;
    bool is_block_call = false;
    InstId inst;
    BlockCallId call;
    uint32_t operand_index = 0;
};

struct RelocFixup {
    GlobalId global;
    size_t reloc_index = 0;
    std::string symbol;
    Token token;
};

struct CtorFixup {
    uint32_t priority = 65535;
    std::string symbol;
    Token token;
};

class Parser {
public:
    Parser(std::vector<Token> tokens, std::shared_ptr<const TargetInfo> target)
        : tokens_(std::move(tokens)),
          module_(std::make_unique<Module>(std::move(target))) {}

    std::unique_ptr<Module> run() {

        if (peek().kind == Tok::Ident && peek().text == "target") {
            next();
            Token triple = expect(Tok::Str, "expected a quoted target triple");
            module_->set_triple(unescape_string(triple));
        }
        struct PendingBody {
            FuncId func;
            size_t begin = 0;
            size_t end = 0;
        };
        std::vector<PendingBody> bodies;
        while (peek().kind != Tok::End) {
            Token keyword = expect(Tok::Ident, "expected a top-level declaration");
            if (keyword.text == "global") {
                parse_global();
            } else if (keyword.text == "ctor") {
                CtorFixup ctor;
                ctor.priority = static_cast<uint32_t>(expect_int("ctor priority"));
                ctor.token = peek();
                ctor.symbol = expect_symbol_name();
                ctor_fixups_.push_back(std::move(ctor));
            } else if (keyword.text == "module_asm") {
                Token text = expect(Tok::Str, "expected a quoted asm string");
                module_->add_module_asm(unescape_string(text));
            } else if (keyword.text == "declare") {
                parse_function_header(/*is_declaration=*/true);
            } else if (keyword.text == "func") {
                FuncId func = parse_function_header(/*is_declaration=*/false);
                expect(Tok::LBrace, "expected '{' after function signature");
                size_t begin = pos_;
                while (peek().kind != Tok::RBrace) {
                    if (peek().kind == Tok::End) {
                        fail(peek(), "missing '}' at end of function body");
                    }
                    if (peek().kind == Tok::LBrace) {
                        fail(peek(), "unexpected '{' inside a function body");
                    }
                    next();
                }
                bodies.push_back({func, begin, pos_});
                next();
            } else {
                fail(keyword, "unknown top-level declaration '" +
                                  std::string(keyword.text) + "'");
            }
        }

        for (const PendingBody& body : bodies) {
            parse_body(body.func, body.begin, body.end);
        }

        for (const RelocFixup& fixup : reloc_fixups_) {
            InitReloc& reloc =
                module_->global(fixup.global).init.relocs[fixup.reloc_index];
            if (FuncId func = module_->find_function(fixup.symbol); func.is_valid()) {
                reloc.is_function = true;
                reloc.target_index = func.index;
            } else if (GlobalId global = module_->find_global(fixup.symbol);
                       global.is_valid()) {
                reloc.is_function = false;
                reloc.target_index = global.index;
            } else {
                fail(fixup.token, "unknown symbol @" + fixup.symbol);
            }
        }
        for (const CtorFixup& fixup : ctor_fixups_) {
            FuncId func = module_->find_function(fixup.symbol);
            if (!func.is_valid()) {
                fail(fixup.token, "unknown ctor function @" + fixup.symbol);
            }
            module_->add_ctor(fixup.priority, func);
        }
        return std::move(module_);
    }

private:

    const Token& peek(size_t ahead = 0) const {
        size_t index = pos_ + ahead;
        return index < tokens_.size() ? tokens_[index] : tokens_.back();
    }

    const Token& next() {
        const Token& token = peek();
        if (pos_ < tokens_.size() - 1) {
            ++pos_;
        }
        return token;
    }

    const Token& expect(Tok kind, const std::string& message) {
        if (peek().kind != kind) {
            fail(peek(), message);
        }
        return next();
    }

    bool accept(Tok kind) {
        if (peek().kind == kind) {
            next();
            return true;
        }
        return false;
    }

    bool accept_ident(std::string_view word) {
        if (peek().kind == Tok::Ident && peek().text == word) {
            next();
            return true;
        }
        return false;
    }

    void expect_ident(std::string_view word) {
        if (!accept_ident(word)) {
            fail(peek(), "expected '" + std::string(word) + "'");
        }
    }

    uint64_t expect_int(const std::string& what) {
        Token token = expect(Tok::Int, "expected " + what);
        return parse_decimal(token);
    }

    bool expect_bool_int(std::string_view what) {
        Token token = expect(Tok::Int, "expected 0 or 1 for " + std::string(what));
        uint64_t value = parse_decimal(token);
        if (value > 1) {
            fail(token, "expected 0 or 1 for " + std::string(what));
        }
        return value != 0;
    }

    TypeId parse_type() {
        Token token = next();
        if (token.kind != Tok::Ident) {
            fail(token, "expected a type");
        }
        if (token.text == "void") {
            return types::VOID;
        }
        if (token.text == "ptr") {
            uint32_t address_space = 0;
            if (accept(Tok::LParen)) {
                address_space = static_cast<uint32_t>(expect_int("address space"));
                expect(Tok::RParen, "expected ')' after address space");
            }
            return module_->types().get_ptr(address_space);
        }
        if (token.text.size() >= 2 && token.text[0] == 'i') {
            uint64_t width = 0;
            for (size_t i = 1; i < token.text.size(); ++i) {
                if (!std::isdigit(static_cast<unsigned char>(token.text[i]))) {
                    width = 0;
                    break;
                }
                width = width * 10 + static_cast<uint64_t>(token.text[i] - '0');
            }
            if (width > 0 && width <= UINT16_MAX) {
                return module_->types().get_int(static_cast<uint16_t>(width));
            }
        }
        if (token.text == "f32") return types::F32;
        if (token.text == "f64") return types::F64;
        if (token.text == "f128") return types::F128;
        if (token.text == "f80") return types::F80;
        fail(token, "expected a type, got '" + std::string(token.text) + "'");
    }

    SigId parse_signature() {
        expect(Tok::LParen, "expected '(' to start a signature");
        SigData sig;
        if (peek().kind != Tok::RParen) {
            do {
                if (accept(Tok::Ellipsis)) {
                    sig.is_variadic = true;
                    expect_ident("fixed");
                    sig.fixed_param_count =
                        static_cast<uint32_t>(expect_int("named-parameter count"));
                    break;
                }
                SigParam param;
                if (accept_ident("sret")) {
                    param.role = ParamRole::Sret;
                } else if (accept_ident("byval")) {
                    param.role = ParamRole::IndirectByval;
                } else if (accept_ident("stackbyval")) {
                    param.role = ParamRole::StackByval;
                    param.byval_size =
                        static_cast<uint32_t>(expect_int("byval size"));
                    param.byval_align =
                        static_cast<uint32_t>(expect_int("byval alignment"));
                }
                if (accept_ident("group")) {
                    param.coerce_group =
                        static_cast<uint8_t>(expect_int("group slot count"));
                }
                param.type = parse_type();
                sig.params.push_back(param);
            } while (accept(Tok::Comma));
        }
        expect(Tok::RParen, "expected ')' after signature parameters");
        expect(Tok::Arrow, "expected '->' before the return class");
        if (accept_ident("void")) {
            sig.ret_class = RetClass::Void;
        } else if (accept_ident("pair")) {
            sig.ret_class = RetClass::IntPair;
            sig.ret_type = parse_type();
            sig.ret_count = 2;
            if (accept_ident("mask")) {
                sig.ret_sse_mask =
                    static_cast<uint8_t>(expect_int("sse lane mask"));
            }
        } else if (accept_ident("hfa")) {
            sig.ret_class = RetClass::Hfa;
            sig.ret_type = parse_type();
            expect_ident("x");
            sig.ret_count = static_cast<uint8_t>(expect_int("element count"));
        } else if (accept_ident("sret")) {
            sig.ret_class = RetClass::IndirectSret;
        } else {
            sig.ret_class = RetClass::Scalar;
            sig.ret_type = parse_type();
            sig.ret_count = 1;
        }
        return module_->types().get_signature(std::move(sig));
    }

    Linkage parse_linkage() {
        if (accept_ident("internal")) return Linkage::Internal;
        if (accept_ident("linkonce_odr")) return Linkage::LinkOnceODR;
        if (accept_ident("weak")) return Linkage::Weak;
        if (accept_ident("common")) return Linkage::Common;
        return Linkage::External;
    }

    SymbolAttrs parse_symbol_attrs() {
        SymbolAttrs attrs;
        for (;;) {
            if (accept_ident("hidden")) {
                attrs.hidden = true;
                attrs.visibility = SymbolVisibility::Hidden;
                continue;
            }
            if (accept_ident("protected")) {
                attrs.visibility = SymbolVisibility::Protected;
                continue;
            }
            if (accept_ident("no_prefix")) {
                attrs.no_prefix = true;
                continue;
            }
            if (accept_ident("comdat")) {
                Token key = expect(Tok::Str, "expected COMDAT key string");
                attrs.comdat_key = unescape_string(key);
                continue;
            }
            break;
        }
        return attrs;
    }

    std::string expect_symbol_name() {
        Token token = expect(Tok::Global, "expected an @name");
        return std::string(token.text.substr(1));
    }

    void parse_global() {
        GlobalData data;
        data.linkage = parse_linkage();
        data.attrs = parse_symbol_attrs();
        Token name_token = peek();
        data.name = expect_symbol_name();
        if (module_->find_global(data.name).is_valid() ||
            module_->find_function(data.name).is_valid()) {
            fail(name_token, "duplicate symbol @" + data.name);
        }
        expect_ident("size");
        data.size_bytes = expect_int("global size");
        expect_ident("align");
        data.align_bytes = static_cast<uint32_t>(expect_int("alignment"));
        if (accept_ident("section")) {
            if (peek().kind == Tok::Str) {
                data.section = SectionKind::Custom;
                data.custom_section = unescape_string(next());
            } else {
                Token section = expect(Tok::Ident, "expected a section kind");
                if (section.text == "const") {
                    data.section = SectionKind::Const;
                } else if (section.text == "cstring") {
                    data.section = SectionKind::Cstring;
                } else if (section.text == "zerofill") {
                    data.section = SectionKind::Zerofill;
                } else if (section.text == "text") {
                    data.section = SectionKind::Text;
                } else if (section.text == "data") {
                    data.section = SectionKind::Data;
                } else {
                    fail(section, "unknown section kind '" +
                                      std::string(section.text) + "'");
                }
            }
        }
        if (accept_ident("thread_local")) {
            data.is_thread_local = true;
        }
        expect(Tok::Equals, "expected '=' before the initializer");
        std::vector<std::pair<std::string, Token>> reloc_symbols;
        if (accept_ident("external")) {
            data.init = GlobalInit::none();
        } else if (accept_ident("zeroinit")) {
            data.init = GlobalInit::zero();
        } else if (accept_ident("bytes")) {
            Token bytes_token = expect(Tok::Str, "expected a byte string");
            data.init.kind = GlobalInitKind::Bytes;
            data.init.bytes = unescape_bytes(bytes_token);
            if (accept_ident("relocs")) {
                expect(Tok::LBracket, "expected '[' after 'relocs'");
                do {
                    InitReloc reloc;
                    reloc.offset = expect_int("relocation offset");
                    expect(Tok::Colon, "expected ':' in relocation");
                    Token symbol_token = peek();
                    reloc_symbols.emplace_back(expect_symbol_name(), symbol_token);
                    if (accept(Tok::Plus)) {
                        reloc.addend = static_cast<int64_t>(expect_int("addend"));
                    } else if (accept(Tok::Minus)) {
                        reloc.addend = -static_cast<int64_t>(expect_int("addend"));
                    }
                    data.init.relocs.push_back(reloc);
                } while (accept(Tok::Comma));
                expect(Tok::RBracket, "expected ']' after relocations");
            }
        } else {
            fail(peek(), "expected 'external', 'zeroinit' or 'bytes'");
        }
        GlobalId id = module_->create_global(std::move(data));
        for (size_t i = 0; i < reloc_symbols.size(); ++i) {
            reloc_fixups_.push_back(
                {id, i, std::move(reloc_symbols[i].first), reloc_symbols[i].second});
        }
    }

    FuncId parse_function_header(bool is_declaration) {
        Linkage linkage = parse_linkage();
        SymbolAttrs attrs = parse_symbol_attrs();
        Token name_token = peek();
        std::string name = expect_symbol_name();
        if (module_->find_global(name).is_valid() ||
            module_->find_function(name).is_valid()) {
            fail(name_token, "duplicate symbol @" + name);
        }
        SigId sig = parse_signature();
        (void)is_declaration;
        FuncId id = module_->create_function(std::move(name), sig, linkage);
        module_->function(id).attrs() = attrs;
        return id;
    }

    void parse_body(FuncId func_id, size_t begin, size_t end) {
        Function& func = module_->function(func_id);
        values_.clear();
        labels_.clear();
        fixups_.clear();

        std::vector<BlockHeader> headers = scan_block_headers(func, begin, end);
        if (headers.empty()) {
            fail(tokens_[begin], "function body has no blocks");
        }
        if (headers.front().start != begin) {
            fail(tokens_[begin], "expected a block label");
        }

        size_t header_index = 0;
        BlockId current;
        pos_ = begin;
        while (pos_ < end) {
            if (header_index < headers.size() &&
                pos_ == headers[header_index].start) {
                current = headers[header_index].block;
                pos_ = headers[header_index].end;
                ++header_index;
                continue;
            }
            parse_instruction(func, current);
        }

        for (const ValueFixup& fixup : fixups_) {
            auto it = values_.find(fixup.name);
            if (it == values_.end()) {
                fail(fixup.token, "unknown value %" + fixup.name);
            }
            if (fixup.is_block_call) {
                func.set_block_call_arg(fixup.call, fixup.operand_index, it->second);
            } else {
                func.set_operand(fixup.inst, fixup.operand_index, it->second);
            }
        }
        pos_ = end + 1;
    }
    std::vector<BlockHeader> scan_block_headers(Function& func, size_t begin,
                                                size_t end) {
        std::vector<BlockHeader> headers;
        for (size_t i = begin; i < end; ++i) {
            if (tokens_[i].kind != Tok::Ident || tokens_[i + 1].kind != Tok::LParen) {
                continue;
            }
            size_t j = i + 2;
            uint32_t depth = 1;
            while (j < end && depth > 0) {
                if (tokens_[j].kind == Tok::LParen) {
                    ++depth;
                } else if (tokens_[j].kind == Tok::RParen) {
                    --depth;
                }
                ++j;
            }
            if (depth != 0 || j >= end || tokens_[j].kind != Tok::Colon) {
                continue;
            }

            BlockHeader header;
            header.start = i;
            header.end = j + 1;
            std::string label(tokens_[i].text);
            if (labels_.count(label)) {
                fail(tokens_[i], "duplicate block label " + label);
            }
            size_t saved = pos_;
            pos_ = i + 2;
            std::vector<TypeId> param_types;
            std::vector<Token> param_names;
            if (peek().kind != Tok::RParen) {
                do {
                    param_names.push_back(
                        expect(Tok::Local, "expected a %name block parameter"));
                    expect(Tok::Colon, "expected ':' before the parameter type");
                    param_types.push_back(parse_type());
                } while (accept(Tok::Comma));
            }
            expect(Tok::RParen, "expected ')' after block parameters");
            pos_ = saved;

            header.block = func.create_block(param_types);
            auto params = func.block_params(header.block);
            for (size_t p = 0; p < param_names.size(); ++p) {
                bind_value(func, param_names[p], params[p]);
            }
            labels_.emplace(std::move(label), header.block);
            headers.push_back(header);
            i = j;
        }
        return headers;
    }

    void bind_value(Function& func, const Token& name_token, ValueId value) {
        std::string name(name_token.text.substr(1));
        if (!values_.emplace(name, value).second) {
            fail(name_token, "redefinition of %" + name);
        }
        if (!is_canonical_value_name(name)) {
            func.set_value_name(value, name);
        }
    }

    ValueId parse_literal(Function& func) {
        bool negative = accept(Tok::Minus);
        Token token = next();
        if (token.kind == Tok::Ident && token.text == "null") {
            expect(Tok::Colon, "expected ':' after 'null'");
            TypeId type = parse_type();
            if (!module_->types().is_ptr(type)) {
                fail(token, "null requires a pointer type");
            }
            return func.const_null(type);
        }
        if (token.kind == Tok::Ident && token.text == "undef") {
            expect(Tok::Colon, "expected ':' after 'undef'");
            return func.undef(parse_type());
        }
        if (token.kind == Tok::Ident && token.text == "label") {
            Token label_token = expect(Tok::Ident, "expected a block label");
            auto it = labels_.find(std::string(label_token.text));
            if (it == labels_.end()) {
                fail(label_token,
                     "unknown block label " + std::string(label_token.text));
            }
            return func.label_addr(it->second, types::PTR);
        }
        uint64_t low = 0;
        uint64_t high = 0;
        bool is_hex = false;
        if (token.kind == Tok::Int) {
            low = parse_decimal(token);
        } else if (token.kind == Tok::HexInt) {
            parse_hex(token, low, high);
            is_hex = true;
        } else {
            fail(token, "expected a value");
        }
        expect(Tok::Colon, "expected ':' and a type after the literal");
        TypeId type = parse_type();
        const TypeData& data = module_->types().type(type);
        if (data.kind == TypeKind::Int) {
            if (negative) {
                if (is_hex) {
                    fail(token, "negative hex literals are not supported");
                }
                low = ~low + 1;
                high = low == 0 ? 0 : UINT64_MAX;
            }
            if (data.int_width < 64) {
                uint64_t mask = (UINT64_C(1) << data.int_width) - 1;
                if (!negative && !is_hex && low > mask) {
                    fail(token, "literal does not fit in i" +
                                    std::to_string(data.int_width));
                }
                low &= mask;
                high = 0;
            } else if (data.int_width == 64) {
                high = 0;
            }
            return func.const_int(type, low, high);
        }
        if (data.kind == TypeKind::Float) {
            if (!is_hex || negative) {
                fail(token, "float literals are written as hex bit patterns");
            }
            return func.const_float_bits(type, low, high);
        }
        fail(token, "literals must have an integer or float type");
    }
    ValueId parse_operand(Function& func, std::string* fixup_name, Token* fixup_token) {
        const Token& token = peek();
        if (token.kind == Tok::Local) {
            next();
            std::string name(token.text.substr(1));
            auto it = values_.find(name);
            if (it != values_.end()) {
                return it->second;
            }
            *fixup_name = std::move(name);
            *fixup_token = token;
            return ValueId{};
        }
        if (token.kind == Tok::Global) {
            next();
            std::string name(token.text.substr(1));
            if (FuncId callee = module_->find_function(name); callee.is_valid()) {
                return func.func_addr(callee, types::PTR);
            }
            if (GlobalId global = module_->find_global(name); global.is_valid()) {
                return func.global_addr(global, types::PTR);
            }
            fail(token, "unknown symbol @" + name);
        }
        return parse_literal(func);
    }

    struct Operand {
        ValueId value;
        std::string fixup_name;
        Token fixup_token;

        bool needs_fixup() const { return !fixup_name.empty(); }
    };

    Operand parse_operand(Function& func) {
        Operand operand;
        operand.value = parse_operand(func, &operand.fixup_name, &operand.fixup_token);
        return operand;
    }

    void record_operand_fixups(InstId inst, std::span<const Operand> operands) {
        for (uint32_t i = 0; i < operands.size(); ++i) {
            if (operands[i].needs_fixup()) {
                fixups_.push_back({operands[i].fixup_name, operands[i].fixup_token,
                                   false, inst, BlockCallId{}, i});
            }
        }
    }

    std::vector<ValueId> operand_values(std::span<const Operand> operands) {
        std::vector<ValueId> values;
        values.reserve(operands.size());
        for (const Operand& operand : operands) {
            values.push_back(operand.value);
        }
        return values;
    }

    BlockId parse_block_label() {
        Token label_token = expect(Tok::Ident, "expected a block label");
        auto it = labels_.find(std::string(label_token.text));
        if (it == labels_.end()) {
            fail(label_token, "unknown block label " + std::string(label_token.text));
        }
        return it->second;
    }

    BlockCallId parse_block_call(Function& func) {
        BlockId target = parse_block_label();
        expect(Tok::LParen, "expected '(' after the block label");
        std::vector<Operand> args;
        if (peek().kind != Tok::RParen) {
            do {
                args.push_back(parse_operand(func));
            } while (accept(Tok::Comma));
        }
        expect(Tok::RParen, "expected ')' after branch arguments");
        BlockCallId call = func.make_block_call(target, operand_values(args));
        for (uint32_t i = 0; i < args.size(); ++i) {
            if (args[i].needs_fixup()) {
                fixups_.push_back({args[i].fixup_name, args[i].fixup_token, true,
                                   InstId{}, call, i});
            }
        }
        return call;
    }

    uint64_t parse_align_suffix() {
        expect(Tok::Comma, "expected ', align N'");
        expect_ident("align");
        Token token = peek();
        uint64_t align = expect_int("alignment");
        if (align == 0 || (align & (align - 1)) != 0) {
            fail(token, "alignment must be a power of two");
        }
        uint64_t log2 = 0;
        while ((UINT64_C(1) << log2) < align) {
            ++log2;
        }
        return log2;
    }

    MemOrder parse_order(std::string_view label) {
        expect(Tok::Comma, "expected ', " + std::string(label) + " <order>'");
        expect_ident(label);
        Token token = expect(Tok::Ident, "expected a memory order");
        auto order = mem_order_from_mnemonic(token.text);
        if (!order) {
            fail(token, "unknown memory order '" + std::string(token.text) + "'");
        }
        return *order;
    }

    SrcLoc parse_loc_suffix() {
        if (peek().kind == Tok::Ident && peek().text == "loc" &&
            peek(1).kind == Tok::LParen) {
            next();
            next();
            uint64_t offset = expect_int("location offset");
            expect(Tok::RParen, "expected ')' after the location");
            return SrcLoc(static_cast<uint32_t>(offset));
        }
        return SrcLoc{};
    }

    static bool has_fixed_ptr_result(Opcode op) {
        switch (op) {
            case Opcode::StackAlloc:
            case Opcode::StackAllocDyn:
            case Opcode::StackSave:
            case Opcode::FrameAddr:
            case Opcode::ReturnAddr:
            case Opcode::EhAllocException:
            case Opcode::EhLandingPad:
            case Opcode::CatchBegin:
                return true;
            default:
                return false;
        }
    }

    void parse_instruction(Function& func, BlockId block) {
        if (!block.is_valid()) {
            fail(peek(), "instruction outside of a block");
        }
        Token result_token;
        bool has_result_name = false;
        if (peek().kind == Tok::Local && peek(1).kind == Tok::Equals) {
            result_token = next();
            next();
            has_result_name = true;
        }
        Token mnemonic = expect(Tok::Ident, "expected an instruction");
        auto opcode = opcode_from_mnemonic(mnemonic.text);
        if (!opcode) {
            fail(mnemonic,
                 "unknown instruction '" + std::string(mnemonic.text) + "'");
        }
        Opcode op = *opcode;

        TypeId result_type;
        uint64_t aux = 0;
        uint64_t aux2 = 0;
        uint16_t flags = 0;
        std::vector<Operand> operands;

        if (op == Opcode::Icmp) {
            expect(Tok::Dot, "expected a condition code suffix");
            Token cond = expect(Tok::Ident, "expected a condition code");
            auto parsed = int_cond_from_mnemonic(cond.text);
            if (!parsed) {
                fail(cond, "unknown integer condition '" + std::string(cond.text) + "'");
            }
            aux = static_cast<uint64_t>(*parsed);
            result_type = types::I8;
        } else if (op == Opcode::Fcmp) {
            expect(Tok::Dot, "expected a condition code suffix");
            Token cond = expect(Tok::Ident, "expected a condition code");
            auto parsed = float_cond_from_mnemonic(cond.text);
            if (!parsed) {
                fail(cond, "unknown float condition '" + std::string(cond.text) + "'");
            }
            aux = static_cast<uint64_t>(*parsed);
            result_type = types::I8;
        } else if (op == Opcode::AtomicRmw) {
            expect(Tok::Dot, "expected an atomic operation suffix");
            Token rmw = expect(Tok::Ident, "expected an atomic operation");
            auto parsed = rmw_op_from_mnemonic(rmw.text);
            if (!parsed) {
                fail(rmw, "unknown atomic operation '" + std::string(rmw.text) + "'");
            }
            aux = static_cast<uint64_t>(*parsed);
            expect(Tok::Dot, "expected a result type suffix");
            result_type = parse_type();
        } else if (has_fixed_ptr_result(op)) {
            result_type = types::PTR;
        } else if (opcode_result_kind(op) == ResultKind::Value) {
            expect(Tok::Dot, "expected a result type suffix");
            result_type = parse_type();
        }

        switch (op) {
            case Opcode::StackAlloc: {
                uint64_t size = expect_int("allocation size");
                uint64_t align_log2 = parse_align_suffix();
                aux = pack_stack_alloc_aux(size, static_cast<uint8_t>(align_log2));
                break;
            }
            case Opcode::StackAllocDyn:
                operands.push_back(parse_operand(func));
                aux = parse_align_suffix();
                break;
            case Opcode::Load:
                if (accept_ident("volatile")) {
                    flags |= INST_FLAG_VOLATILE;
                }
                operands.push_back(parse_operand(func));
                aux = parse_align_suffix();
                break;
            case Opcode::Store:
                if (accept_ident("volatile")) {
                    flags |= INST_FLAG_VOLATILE;
                }
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' between store operands");
                operands.push_back(parse_operand(func));
                aux = parse_align_suffix();
                break;
            case Opcode::AtomicLoad: {
                if (accept_ident("volatile")) {
                    flags |= INST_FLAG_VOLATILE;
                }
                operands.push_back(parse_operand(func));
                uint64_t align_log2 = parse_align_suffix();
                MemOrder order = parse_order("order");
                aux = pack_atomic_access_aux(order,
                                             static_cast<uint8_t>(align_log2));
                break;
            }
            case Opcode::AtomicStore: {
                if (accept_ident("volatile")) {
                    flags |= INST_FLAG_VOLATILE;
                }
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' between store operands");
                operands.push_back(parse_operand(func));
                uint64_t align_log2 = parse_align_suffix();
                MemOrder order = parse_order("order");
                aux = pack_atomic_access_aux(order,
                                             static_cast<uint8_t>(align_log2));
                break;
            }
            case Opcode::AtomicRmw: {
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' between operands");
                operands.push_back(parse_operand(func));
                MemOrder order = parse_order("order");
                aux = pack_rmw_aux(static_cast<RmwOp>(aux), order);
                break;
            }
            case Opcode::AtomicCas: {
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' between operands");
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' between operands");
                operands.push_back(parse_operand(func));
                MemOrder success = parse_order("order");
                MemOrder failure = parse_order("failure");
                aux = pack_cas_aux(success, failure);
                break;
            }
            case Opcode::Fence: {
                expect_ident("order");
                Token token = expect(Tok::Ident, "expected a memory order");
                auto order = mem_order_from_mnemonic(token.text);
                if (!order) {
                    fail(token,
                         "unknown memory order '" + std::string(token.text) + "'");
                }
                aux = static_cast<uint64_t>(*order);
                break;
            }
            case Opcode::InlineAsm: {
                aux = module_->add_asm_payload(parse_asm_payload());
                parse_call_args(func, operands);
                break;
            }
            case Opcode::AsmGoto: {
                aux = module_->add_asm_payload(parse_asm_payload());
                parse_call_args(func, operands);
                expect_ident("to");
                std::vector<BlockCallId> calls;
                calls.push_back(
                    func.make_block_call(parse_block_label(), {}));
                expect(Tok::LBracket, "expected '[' before the label list");
                if (peek().kind != Tok::RBracket) {
                    do {
                        calls.push_back(
                            func.make_block_call(parse_block_label(), {}));
                    } while (accept(Tok::Comma));
                }
                expect(Tok::RBracket, "expected ']' after the label list");
                aux2 = func.make_block_call_list(calls);
                break;
            }
            case Opcode::EhAllocException:
                aux = expect_int("exception allocation size");
                break;
            case Opcode::EhLandingPad: {
                EhLandingPadPayload payload;
                expect_ident("cleanup");
                payload.is_cleanup = expect_bool_int("cleanup");
                expect(Tok::Comma, "expected ',' after cleanup flag");
                expect_ident("catch_all");
                payload.has_catch_all = expect_bool_int("catch_all");
                expect(Tok::Comma, "expected ',' after catch_all flag");
                expect_ident("clauses");
                expect(Tok::LBracket, "expected '[' before landing-pad clauses");
                if (peek().kind != Tok::RBracket) {
                    do {
                        Token clause_token = peek();
                        std::string name = expect_symbol_name();
                        GlobalId global = module_->find_global(name);
                        if (!global.is_valid()) {
                            fail(clause_token,
                                 "unknown landing-pad clause global @" + name);
                        }
                        payload.clause_typeinfos.push_back(global);
                    } while (accept(Tok::Comma));
                }
                expect(Tok::RBracket, "expected ']' after landing-pad clauses");
                aux = module_->add_eh_landing_pad_payload(std::move(payload));
                break;
            }
            case Opcode::Jump:
                aux = pack_pair_aux(parse_block_call(func).index, 0);
                break;
            case Opcode::BrIf: {
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' after the branch condition");
                BlockCallId then_call = parse_block_call(func);
                expect(Tok::Comma, "expected ',' between branch targets");
                BlockCallId else_call = parse_block_call(func);
                aux = pack_pair_aux(then_call.index, else_call.index);
                break;
            }
            case Opcode::Switch: {
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' after the switch operand");
                BlockCallId default_call = parse_block_call(func);
                expect(Tok::LBracket, "expected '[' before switch cases");
                std::vector<SwitchCase> cases;
                if (peek().kind != Tok::RBracket) {
                    do {
                        SwitchCase entry;
                        entry.value = expect_int("case value");
                        expect(Tok::Colon, "expected ':' after the case value");
                        entry.target = parse_block_call(func);
                        cases.push_back(entry);
                    } while (accept(Tok::Comma));
                }
                expect(Tok::RBracket, "expected ']' after switch cases");
                aux = pack_pair_aux(default_call.index, func.make_jump_table(cases));
                break;
            }
            case Opcode::BrIndirect: {
                operands.push_back(parse_operand(func));
                expect(Tok::LBracket, "expected '[' before the target list");
                std::vector<BlockCallId> calls;
                if (peek().kind != Tok::RBracket) {
                    do {
                        BlockId target = parse_block_label();
                        calls.push_back(func.make_block_call(target, {}));
                    } while (accept(Tok::Comma));
                }
                expect(Tok::RBracket, "expected ']' after the target list");
                aux = pack_pair_aux(func.make_block_call_list(calls), 0);
                break;
            }
            case Opcode::Ret:

                if (peek().line == mnemonic.line && peek().kind != Tok::RBrace) {
                    operands.push_back(parse_operand(func));
                }
                break;
            case Opcode::Unreachable:
                break;
            case Opcode::Throw:
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' after the exception pointer");
                operands.push_back(parse_operand(func));
                if (accept(Tok::Comma)) {
                    operands.push_back(parse_operand(func));
                }
                break;
            case Opcode::Rethrow:
                break;
            case Opcode::Resume:
                operands.push_back(parse_operand(func));
                expect(Tok::Comma, "expected ',' after the exception pointer");
                operands.push_back(parse_operand(func));
                break;
            case Opcode::Call: {
                Token callee_token = peek();
                std::string callee_name = expect_symbol_name();
                FuncId callee = module_->find_function(callee_name);
                if (!callee.is_valid()) {
                    fail(callee_token, "unknown function @" + callee_name);
                }
                aux = callee.index;
                parse_call_args(func, operands);
                const SigData& sig =
                    module_->types().signature(module_->function(callee).sig());
                result_type = sig.ret_class == RetClass::Scalar ? sig.ret_type
                                                                : TypeId{};
                break;
            }
            case Opcode::Invoke: {
                Token callee_token = peek();
                std::string callee_name = expect_symbol_name();
                FuncId callee = module_->find_function(callee_name);
                if (!callee.is_valid()) {
                    fail(callee_token, "unknown function @" + callee_name);
                }
                aux = callee.index;
                parse_call_args(func, operands);
                expect(Tok::Comma, "expected ',' after invoke arguments");
                expect_ident("normal");
                BlockCallId normal = parse_block_call(func);
                expect(Tok::Comma, "expected ',' after invoke normal target");
                expect_ident("unwind");
                BlockCallId unwind = parse_block_call(func);
                aux2 = pack_pair_aux(normal.index, unwind.index);
                const SigData& sig =
                    module_->types().signature(module_->function(callee).sig());
                result_type = sig.ret_class == RetClass::Scalar ? sig.ret_type
                                                                : TypeId{};
                break;
            }
            case Opcode::CallIndirect: {
                operands.push_back(parse_operand(func));
                parse_call_args(func, operands);
                expect(Tok::Colon, "expected ': (signature)' after the call");
                SigId sig_id = parse_signature();
                aux = sig_id.index;
                const SigData& sig = module_->types().signature(sig_id);
                result_type = sig.ret_class == RetClass::Scalar ? sig.ret_type
                                                                : TypeId{};
                break;
            }
            case Opcode::TailCallIndirect: {
                operands.push_back(parse_operand(func));
                parse_call_args(func, operands);
                expect(Tok::Colon, "expected ': (signature)' after the call");
                aux = parse_signature().index;
                break;
            }
            case Opcode::InvokeIndirect: {
                operands.push_back(parse_operand(func));
                parse_call_args(func, operands);
                expect(Tok::Colon, "expected ': (signature)' after the invoke");
                SigId sig_id = parse_signature();
                aux = sig_id.index;
                expect(Tok::Comma, "expected ',' after invoke signature");
                expect_ident("normal");
                BlockCallId normal = parse_block_call(func);
                expect(Tok::Comma, "expected ',' after invoke normal target");
                expect_ident("unwind");
                BlockCallId unwind = parse_block_call(func);
                aux2 = pack_pair_aux(normal.index, unwind.index);
                const SigData& sig = module_->types().signature(sig_id);
                result_type = sig.ret_class == RetClass::Scalar ? sig.ret_type
                                                                : TypeId{};
                break;
            }
            default: {

                int count = opcode_operand_count(op);
                assert(count >= 0);
                for (int i = 0; i < count; ++i) {
                    if (i > 0) {
                        expect(Tok::Comma, "expected ',' between operands");
                    }
                    operands.push_back(parse_operand(func));
                }
                break;
            }
        }

        SrcLoc loc = parse_loc_suffix();
        InstId inst =
            func.make_inst(op, result_type, operand_values(operands), aux, loc,
                           flags, aux2);
        func.append_inst(block, inst);
        record_operand_fixups(inst, operands);

        ValueId result = func.inst(inst).result;
        if (has_result_name) {
            if (!result.is_valid()) {
                fail(result_token, "instruction does not produce a result");
            }
            bind_value(func, result_token, result);
        } else if (result.is_valid()) {
            fail(mnemonic, "result of this instruction must be named");
        }
    }

    void parse_call_args(Function& func, std::vector<Operand>& operands) {
        expect(Tok::LParen, "expected '(' before call arguments");
        if (peek().kind != Tok::RParen) {
            do {
                operands.push_back(parse_operand(func));
            } while (accept(Tok::Comma));
        }
        expect(Tok::RParen, "expected ')' after call arguments");
    }
    AsmPayload parse_asm_payload() {
        AsmPayload payload;
        Token text = expect(Tok::Str, "expected the asm text string");
        payload.text = unescape_string(text);
        expect_ident("constraints");
        parse_string_list(payload.constraints);
        expect_ident("operand_types");
        expect(Tok::LBracket, "expected '[' before asm operand types");
        if (peek().kind != Tok::RBracket) {
            do {
                payload.operand_types.push_back(parse_type());
            } while (accept(Tok::Comma));
        }
        expect(Tok::RBracket, "expected ']' after asm operand types");
        expect_ident("clobbers");
        parse_string_list(payload.clobbers);
        if (peek().kind == Tok::Ident && peek().text == "bindings") {
            expect_ident("bindings");
            parse_string_list(payload.register_bindings);
        }
        return payload;
    }

    void parse_string_list(std::vector<std::string>& out) {
        expect(Tok::LBracket, "expected '['");
        if (peek().kind != Tok::RBracket) {
            do {
                Token item = expect(Tok::Str, "expected a quoted string");
                out.push_back(unescape_string(item));
            } while (accept(Tok::Comma));
        }
        expect(Tok::RBracket, "expected ']'");
    }

    std::vector<Token> tokens_;
    std::unique_ptr<Module> module_;
    size_t pos_ = 0;
    std::unordered_map<std::string, ValueId> values_;
    std::unordered_map<std::string, BlockId> labels_;
    std::vector<ValueFixup> fixups_;
    std::vector<RelocFixup> reloc_fixups_;
    std::vector<CtorFixup> ctor_fixups_;
};

} // namespace

ParseResult parse_module(std::string_view text,
                         std::shared_ptr<const TargetInfo> target) {
    ParseResult result;
    try {
        Parser parser(lex(text), std::move(target));
        result.module = parser.run();
    } catch (const ParseException& e) {
        result.errors.push_back(e.error);
    }
    return result;
}

} // namespace aburi::air
