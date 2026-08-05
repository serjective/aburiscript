#include <__adinkra/regex_runtime>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <new>
#include <utility>
#include <vector>

namespace std {
inline namespace __adinkra_v1 {
namespace __regex_runtime {

namespace {

constexpr unsigned flag_icase = 1U << 0;
constexpr unsigned flag_nosubs = 1U << 1;
constexpr unsigned flag_collate = 1U << 3;
constexpr unsigned flag_ecmascript = 1U << 4;
constexpr unsigned flag_basic = 1U << 5;
constexpr unsigned flag_extended = 1U << 6;
constexpr unsigned flag_awk = 1U << 7;
constexpr unsigned flag_grep = 1U << 8;
constexpr unsigned flag_egrep = 1U << 9;
constexpr unsigned flag_multiline = 1U << 10;

constexpr unsigned match_not_bol = 1U << 0;
constexpr unsigned match_not_eol = 1U << 1;
constexpr unsigned match_not_bow = 1U << 2;
constexpr unsigned match_not_eow = 1U << 3;
constexpr unsigned match_not_null = 1U << 5;
constexpr unsigned match_continuous = 1U << 6;
constexpr unsigned match_prev_avail = 1U << 7;
constexpr unsigned match_iterator_progress = 1U << 31;

constexpr int error_collate = 0;
constexpr int error_ctype = 1;
constexpr int error_escape = 2;
constexpr int error_backref = 3;
constexpr int error_brack = 4;
constexpr int error_paren = 5;
constexpr int error_brace = 6;
constexpr int error_badbrace = 7;
constexpr int error_range = 8;
constexpr int error_space = 9;
constexpr int error_badrepeat = 10;
constexpr int error_stack = 12;

constexpr size_t unlimited = numeric_limits<size_t>::max();
constexpr size_t maximum_program_size = 1U << 20;
constexpr size_t maximum_parse_depth = 1024;

enum class node_kind {
    empty,
    literal,
    dot,
    character_class,
    sequence,
    alternative,
    repeat,
    capture,
    backreference,
    begin,
    end,
    word_boundary,
    lookahead
};

struct range {
    uint32_t first;
    uint32_t last;
};

struct named_class {
    vector<uint32_t> name;
    bool inverted;
};

struct character_class {
    bool inverted = false;
    vector<uint32_t> singles;
    vector<range> ranges;
    vector<named_class> names;
    vector<vector<uint32_t>> equivalents;
};

struct node {
    node_kind kind = node_kind::empty;
    size_t left = 0;
    size_t right = 0;
    size_t minimum = 0;
    size_t maximum = 0;
    size_t value = 0;
    bool greedy = true;
    bool inverted = false;
};

enum class operation {
    character,
    any,
    character_class,
    split,
    jump,
    save,
    backreference,
    begin,
    end,
    word_boundary,
    lookahead,
    accept
};

struct instruction {
    operation op = operation::accept;
    size_t first = 0;
    size_t second = 0;
    uint32_t value = 0;
    bool inverted = false;
};

struct code {
    vector<instruction> instructions;
};

enum class grammar {
    ecmascript,
    basic,
    extended,
    awk,
    grep,
    egrep
};

class parse_failure {
public:
    parse_failure(int error_code, size_t error_position)
        : code(error_code), position(error_position) {}

    int code;
    size_t position;
};

bool is_ascii_digit(uint32_t value) {
    return value >= static_cast<uint32_t>('0') &&
           value <= static_cast<uint32_t>('9');
}

bool is_ascii_hex(uint32_t value) {
    return is_ascii_digit(value) ||
           (value >= static_cast<uint32_t>('a') &&
            value <= static_cast<uint32_t>('f')) ||
           (value >= static_cast<uint32_t>('A') &&
            value <= static_cast<uint32_t>('F'));
}

unsigned hex_value(uint32_t value) {
    if (is_ascii_digit(value)) {
        return static_cast<unsigned>(value - '0');
    }
    if (value >= static_cast<uint32_t>('a') &&
        value <= static_cast<uint32_t>('f')) {
        return static_cast<unsigned>(value - 'a' + 10);
    }
    return static_cast<unsigned>(value - 'A' + 10);
}

class parser {
public:
    parser(
        const uint32_t* expression,
        size_t size,
        unsigned flags,
        grammar selected_grammar,
        const traits& character_traits)
        : expression_(expression),
          size_(size),
          flags_(flags),
          grammar_(selected_grammar),
          character_traits_(character_traits) {}

    size_t parse() {
        const size_t result = parse_alternative(false, 0);
        if (position_ != size_) {
            throw parse_failure(error_paren, position_);
        }
        validate_backreferences();
        return result;
    }

    const vector<node>& nodes() const {
        return nodes_;
    }

    vector<character_class>& classes() {
        return classes_;
    }

    size_t captures() const {
        return captures_;
    }

    bool requires_backtracking() const {
        return requires_backtracking_;
    }

private:
    const uint32_t* expression_;
    size_t size_;
    unsigned flags_;
    grammar grammar_;
    const traits& character_traits_;
    size_t position_ = 0;
    size_t captures_ = 0;
    size_t depth_ = 0;
    bool requires_backtracking_ = false;
    vector<node> nodes_;
    vector<character_class> classes_;
    vector<size_t> backreferences_;

    bool ecmascript() const {
        return grammar_ == grammar::ecmascript;
    }

    bool basic_syntax() const {
        return grammar_ == grammar::basic ||
               grammar_ == grammar::grep;
    }

    bool newline_alternative() const {
        return grammar_ == grammar::grep ||
               grammar_ == grammar::egrep;
    }

    bool at_end() const {
        return position_ == size_;
    }

    uint32_t peek(size_t offset = 0) const {
        return position_ + offset < size_
            ? expression_[position_ + offset]
            : 0;
    }

    uint32_t take() {
        return expression_[position_++];
    }

    size_t add(node value) {
        if (nodes_.size() >= maximum_program_size) {
            throw parse_failure(error_space, position_);
        }
        nodes_.push_back(value);
        return nodes_.size() - 1;
    }

    size_t empty() {
        return add(node{});
    }

    size_t sequence(size_t left, size_t right) {
        if (nodes_[left].kind == node_kind::empty) {
            return right;
        }
        if (nodes_[right].kind == node_kind::empty) {
            return left;
        }
        node result;
        result.kind = node_kind::sequence;
        result.left = left;
        result.right = right;
        return add(result);
    }

    size_t alternative(size_t left, size_t right) {
        node result;
        result.kind = node_kind::alternative;
        result.left = left;
        result.right = right;
        return add(result);
    }

    bool begins_group_end() const {
        if (ecmascript() || !basic_syntax()) {
            return peek() == static_cast<uint32_t>(')');
        }
        return peek() == static_cast<uint32_t>('\\') &&
               peek(1) == static_cast<uint32_t>(')');
    }

    bool begins_alternative() const {
        if (newline_alternative() &&
            peek() == static_cast<uint32_t>('\n')) {
            return true;
        }
        return !basic_syntax() &&
               peek() == static_cast<uint32_t>('|');
    }

    void consume_alternative() {
        ++position_;
    }

    size_t parse_alternative(bool in_group, size_t capture_number) {
        if (++depth_ > maximum_parse_depth) {
            throw parse_failure(error_stack, position_);
        }

        size_t result = parse_sequence(in_group);
        while (!at_end() && begins_alternative()) {
            consume_alternative();
            result = alternative(result, parse_sequence(in_group));
        }

        if (in_group) {
            if (at_end() || !begins_group_end()) {
                throw parse_failure(error_paren, position_);
            }
            position_ += basic_syntax() ? 2 : 1;
            if (capture_number != 0) {
                node capture;
                capture.kind = node_kind::capture;
                capture.left = result;
                capture.value = capture_number;
                result = add(capture);
            }
        }
        --depth_;
        return result;
    }

    size_t parse_sequence(bool in_group) {
        size_t result = empty();
        while (!at_end()) {
            if (begins_alternative() ||
                (in_group && begins_group_end())) {
                break;
            }
            if (!in_group && begins_group_end()) {
                throw parse_failure(error_paren, position_);
            }
            result = sequence(result, parse_term());
        }
        return result;
    }

    bool begins_group() const {
        if (ecmascript() || !basic_syntax()) {
            return peek() == static_cast<uint32_t>('(');
        }
        return peek() == static_cast<uint32_t>('\\') &&
               peek(1) == static_cast<uint32_t>('(');
    }

    size_t parse_group() {
        position_ += basic_syntax() ? 2 : 1;
        if (ecmascript() && peek() == static_cast<uint32_t>('?')) {
            ++position_;
            if (peek() == static_cast<uint32_t>(':')) {
                ++position_;
                return parse_alternative(true, 0);
            }
            if (peek() == static_cast<uint32_t>('=') ||
                peek() == static_cast<uint32_t>('!')) {
                const bool inverted =
                    take() == static_cast<uint32_t>('!');
                requires_backtracking_ = true;
                node result;
                result.kind = node_kind::lookahead;
                result.inverted = inverted;
                result.left = parse_alternative(true, 0);
                return add(result);
            }
            throw parse_failure(error_paren, position_);
        }

        const size_t number = ++captures_;
        return parse_alternative(true, number);
    }

    size_t parse_term() {
        const size_t start = position_;
        size_t result;
        bool assertion = false;

        if (begins_group()) {
            result = parse_group();
        } else {
            const uint32_t current = take();
            switch (current) {
            case '^': {
                node value;
                value.kind = node_kind::begin;
                result = add(value);
                assertion = true;
                break;
            }
            case '$': {
                node value;
                value.kind = node_kind::end;
                result = add(value);
                assertion = true;
                break;
            }
            case '.': {
                node value;
                value.kind = node_kind::dot;
                result = add(value);
                break;
            }
            case '[':
                result = parse_character_class();
                break;
            case '\\':
                result = parse_escape(false, assertion);
                break;
            case '*':
            case '+':
            case '?':
                if (ecmascript() || !basic_syntax() || current == '*') {
                    throw parse_failure(error_badrepeat, start);
                }
                [[fallthrough]];
            case '{':
                if (!basic_syntax()) {
                    throw parse_failure(error_badrepeat, start);
                }
                [[fallthrough]];
            default: {
                node value;
                value.kind = node_kind::literal;
                value.value = current;
                result = add(value);
                break;
            }
            }
        }

        if (!assertion) {
            result = parse_quantifier(result);
        }
        return result;
    }

    bool begins_quantifier() const {
        const uint32_t current = peek();
        if (current == static_cast<uint32_t>('*')) {
            return true;
        }
        if (!basic_syntax() &&
            (current == static_cast<uint32_t>('+') ||
             current == static_cast<uint32_t>('?') ||
             current == static_cast<uint32_t>('{'))) {
            return true;
        }
        return basic_syntax() &&
               current == static_cast<uint32_t>('\\') &&
               peek(1) == static_cast<uint32_t>('{');
    }

    size_t parse_decimal(int error_code) {
        if (!is_ascii_digit(peek())) {
            throw parse_failure(error_code, position_);
        }
        size_t result = 0;
        while (is_ascii_digit(peek())) {
            const unsigned digit =
                static_cast<unsigned>(take() - '0');
            if (result >
                (numeric_limits<size_t>::max() - digit) / 10) {
                throw parse_failure(error_badbrace, position_);
            }
            result = result * 10 + digit;
        }
        return result;
    }

    size_t parse_quantifier(size_t child) {
        if (!begins_quantifier()) {
            return child;
        }

        const size_t quantifier_position = position_;
        size_t minimum = 0;
        size_t maximum = unlimited;
        if (peek() == static_cast<uint32_t>('*')) {
            ++position_;
        } else if (peek() == static_cast<uint32_t>('+')) {
            ++position_;
            minimum = 1;
        } else if (peek() == static_cast<uint32_t>('?')) {
            ++position_;
            maximum = 1;
        } else {
            if (basic_syntax()) {
                position_ += 2;
            } else {
                ++position_;
            }
            minimum = parse_decimal(error_badbrace);
            maximum = minimum;
            if (peek() == static_cast<uint32_t>(',')) {
                ++position_;
                maximum = is_ascii_digit(peek())
                    ? parse_decimal(error_badbrace)
                    : unlimited;
            }
            if (basic_syntax()) {
                if (peek() != static_cast<uint32_t>('\\') ||
                    peek(1) != static_cast<uint32_t>('}')) {
                    throw parse_failure(error_brace, position_);
                }
                position_ += 2;
            } else {
                if (peek() != static_cast<uint32_t>('}')) {
                    throw parse_failure(error_brace, position_);
                }
                ++position_;
            }
            if (maximum != unlimited && maximum < minimum) {
                throw parse_failure(error_badbrace, quantifier_position);
            }
            if (minimum > numeric_limits<unsigned>::max() ||
                (maximum != unlimited &&
                 maximum > numeric_limits<unsigned>::max())) {
                throw parse_failure(error_badbrace, quantifier_position);
            }
        }

        bool greedy = true;
        if (ecmascript() &&
            peek() == static_cast<uint32_t>('?')) {
            ++position_;
            greedy = false;
        }
        if (begins_quantifier()) {
            throw parse_failure(error_badrepeat, position_);
        }

        node result;
        result.kind = node_kind::repeat;
        result.left = child;
        result.minimum = minimum;
        result.maximum = maximum;
        result.greedy = greedy;
        return add(result);
    }

    uint32_t parse_hex_escape(size_t count) {
        uint32_t result = 0;
        for (size_t index = 0; index < count; ++index) {
            if (!is_ascii_hex(peek())) {
                throw parse_failure(error_escape, position_);
            }
            result = result * 16 + hex_value(take());
        }
        return result;
    }

    size_t add_named_class(const char* name, bool inverted) {
        character_class result;
        named_class named;
        while (*name != '\0') {
            named.name.push_back(
                static_cast<uint32_t>(
                    static_cast<unsigned char>(*name++)));
        }
        named.inverted = inverted;
        result.names.push_back(std::move(named));
        classes_.push_back(std::move(result));

        node value;
        value.kind = node_kind::character_class;
        value.value = classes_.size() - 1;
        return add(value);
    }

    size_t parse_escape(bool in_class, bool& assertion) {
        if (at_end()) {
            throw parse_failure(error_escape, position_);
        }
        const uint32_t escaped = take();
        switch (escaped) {
        case 'b':
            if (!in_class && ecmascript()) {
                node value;
                value.kind = node_kind::word_boundary;
                value.inverted = false;
                assertion = true;
                return add(value);
            }
            return literal_node(static_cast<uint32_t>('\b'));
        case 'B': {
            if (!in_class && ecmascript()) {
                node value;
                value.kind = node_kind::word_boundary;
                value.inverted = true;
                assertion = true;
                return add(value);
            }
            return literal_node(escaped);
        }
        case 'd':
            return add_named_class("digit", false);
        case 'D':
            return add_named_class("digit", true);
        case 's':
            return add_named_class("space", false);
        case 'S':
            return add_named_class("space", true);
        case 'w':
            return add_named_class("word", false);
        case 'W':
            return add_named_class("word", true);
        case 'f':
            return literal_node(static_cast<uint32_t>('\f'));
        case 'n':
            return literal_node(static_cast<uint32_t>('\n'));
        case 'r':
            return literal_node(static_cast<uint32_t>('\r'));
        case 't':
            return literal_node(static_cast<uint32_t>('\t'));
        case 'v':
            return literal_node(static_cast<uint32_t>('\v'));
        case 'x':
            if (ecmascript() || grammar_ == grammar::awk) {
                return literal_node(parse_hex_escape(2));
            }
            return literal_node(escaped);
        case 'u':
            if (ecmascript()) {
                return literal_node(parse_hex_escape(4));
            }
            return literal_node(escaped);
        case 'c':
            if (ecmascript()) {
                if (at_end()) {
                    throw parse_failure(error_escape, position_);
                }
                const uint32_t value = take();
                if (!((value >= 'a' && value <= 'z') ||
                      (value >= 'A' && value <= 'Z'))) {
                    throw parse_failure(error_escape, position_ - 1);
                }
                return literal_node(value % 32);
            }
            return literal_node(escaped);
        default:
            if (grammar_ == grammar::awk &&
                escaped >= static_cast<uint32_t>('0') &&
                escaped <= static_cast<uint32_t>('7')) {
                uint32_t value = escaped - static_cast<uint32_t>('0');
                size_t count = 1;
                while (count < 3 &&
                       peek() >= static_cast<uint32_t>('0') &&
                       peek() <= static_cast<uint32_t>('7')) {
                    value = value * 8 +
                        (take() - static_cast<uint32_t>('0'));
                    ++count;
                }
                return literal_node(value);
            }
            if (!in_class && is_ascii_digit(escaped) &&
                escaped != static_cast<uint32_t>('0')) {
                size_t number = static_cast<size_t>(escaped - '0');
                if (ecmascript()) {
                    while (is_ascii_digit(peek())) {
                        const size_t digit =
                            static_cast<size_t>(take() - '0');
                        if (number >
                            (numeric_limits<size_t>::max() - digit) /
                                10) {
                            throw parse_failure(
                                error_backref, position_);
                        }
                        number = number * 10 + digit;
                    }
                }
                node value;
                value.kind = node_kind::backreference;
                value.value = number;
                if (number > captures_) {
                    throw parse_failure(
                        error_backref, position_);
                }
                backreferences_.push_back(number);
                requires_backtracking_ = true;
                return add(value);
            }
            if (escaped == static_cast<uint32_t>('0') &&
                ecmascript()) {
                if (is_ascii_digit(peek())) {
                    throw parse_failure(error_escape, position_);
                }
                return literal_node(0);
            }
            if (ecmascript() &&
                ((escaped >= static_cast<uint32_t>('a') &&
                  escaped <= static_cast<uint32_t>('z')) ||
                 (escaped >= static_cast<uint32_t>('A') &&
                  escaped <= static_cast<uint32_t>('Z')))) {
                throw parse_failure(error_escape, position_ - 1);
            }
            return literal_node(escaped);
        }
    }

    size_t literal_node(uint32_t character) {
        node result;
        result.kind = node_kind::literal;
        result.value = character;
        return add(result);
    }

    vector<uint32_t> parse_class_name(uint32_t delimiter) {
        vector<uint32_t> result;
        while (!at_end()) {
            if (peek() == delimiter &&
                peek(1) == static_cast<uint32_t>(']')) {
                position_ += 2;
                return result;
            }
            result.push_back(take());
        }
        throw parse_failure(
            delimiter == static_cast<uint32_t>(':')
                ? error_ctype
                : error_collate,
            position_);
    }

    size_t parse_character_class() {
        character_class result;
        if (peek() == static_cast<uint32_t>('^')) {
            ++position_;
            result.inverted = true;
        }

        bool first = true;
        bool have_pending = false;
        uint32_t pending = 0;
        while (!at_end()) {
            if (peek() == static_cast<uint32_t>(']') &&
                (!first || ecmascript())) {
                ++position_;
                if (have_pending) {
                    result.singles.push_back(pending);
                }
                classes_.push_back(std::move(result));
                node value;
                value.kind = node_kind::character_class;
                value.value = classes_.size() - 1;
                return add(value);
            }
            first = false;

            if (peek() == static_cast<uint32_t>('[') &&
                (peek(1) == static_cast<uint32_t>(':') ||
                 peek(1) == static_cast<uint32_t>('=') ||
                 peek(1) == static_cast<uint32_t>('.'))) {
                const uint32_t delimiter = peek(1);
                position_ += 2;
                vector<uint32_t> name = parse_class_name(delimiter);
                if (delimiter == static_cast<uint32_t>(':')) {
                    if (!character_traits_.valid_class(
                            character_traits_.context,
                            name.data(), name.size(), false)) {
                        throw parse_failure(error_ctype, position_);
                    }
                    if (have_pending) {
                        result.singles.push_back(pending);
                        have_pending = false;
                    }
                    result.names.push_back(
                        named_class{std::move(name), false});
                    continue;
                }
                if (name.empty()) {
                    throw parse_failure(error_collate, position_);
                }
                const size_t collating_size =
                    character_traits_.lookup_collate(
                        character_traits_.context,
                        name.data(), name.size(), nullptr, 0);
                vector<uint32_t> collating(collating_size);
                if (collating_size != 0) {
                    character_traits_.lookup_collate(
                        character_traits_.context,
                        name.data(), name.size(),
                        collating.data(), collating.size());
                }
                if (delimiter == static_cast<uint32_t>('=')) {
                    if (collating.empty()) {
                        throw parse_failure(
                            error_collate, position_);
                    }
                    if (have_pending) {
                        result.singles.push_back(pending);
                        have_pending = false;
                    }
                    result.equivalents.push_back(
                        std::move(collating));
                    continue;
                }
                if (collating.size() != 1) {
                    throw parse_failure(error_collate, position_);
                }
                if (have_pending) {
                    result.singles.push_back(pending);
                }
                pending = collating[0];
                have_pending = true;
                continue;
            }

            uint32_t current;
            if (peek() == static_cast<uint32_t>('\\')) {
                ++position_;
                if (ecmascript() &&
                    (peek() == static_cast<uint32_t>('d') ||
                     peek() == static_cast<uint32_t>('D') ||
                     peek() == static_cast<uint32_t>('s') ||
                     peek() == static_cast<uint32_t>('S') ||
                     peek() == static_cast<uint32_t>('w') ||
                     peek() == static_cast<uint32_t>('W'))) {
                    const uint32_t kind = take();
                    if (have_pending) {
                        result.singles.push_back(pending);
                        have_pending = false;
                    }
                    const char* name =
                        kind == 'd' || kind == 'D'
                            ? "digit"
                            : kind == 's' || kind == 'S'
                                ? "space"
                                : "word";
                    named_class named;
                    while (*name != '\0') {
                        named.name.push_back(
                            static_cast<uint32_t>(*name++));
                    }
                    named.inverted =
                        kind == 'D' || kind == 'S' || kind == 'W';
                    result.names.push_back(std::move(named));
                    if (peek() == static_cast<uint32_t>('-') &&
                        peek(1) != static_cast<uint32_t>(']')) {
                        throw parse_failure(error_range, position_);
                    }
                    continue;
                }
                bool ignored = false;
                const size_t escaped = parse_escape(true, ignored);
                if (nodes_[escaped].kind != node_kind::literal) {
                    throw parse_failure(error_escape, position_);
                }
                current = static_cast<uint32_t>(nodes_[escaped].value);
            } else {
                current = take();
            }

            if (current == static_cast<uint32_t>('-') &&
                have_pending &&
                peek() != static_cast<uint32_t>(']')) {
                uint32_t range_end;
                if (peek() == static_cast<uint32_t>('\\')) {
                    ++position_;
                    bool ignored = false;
                    const size_t escaped = parse_escape(true, ignored);
                    if (nodes_[escaped].kind != node_kind::literal) {
                        throw parse_failure(error_range, position_);
                    }
                    range_end =
                        static_cast<uint32_t>(nodes_[escaped].value);
                } else {
                    range_end = take();
                }
                if (pending > range_end &&
                    (flags_ & flag_collate) == 0) {
                    throw parse_failure(error_range, position_);
                }
                result.ranges.push_back(range{pending, range_end});
                have_pending = false;
                continue;
            }

            if (have_pending) {
                result.singles.push_back(pending);
            }
            pending = current;
            have_pending = true;
        }
        throw parse_failure(error_brack, position_);
    }

    void validate_backreferences() const {
        for (size_t reference : backreferences_) {
            if (reference == 0 || reference > captures_) {
                throw parse_failure(error_backref, position_);
            }
        }
    }
};

grammar select_grammar(unsigned flags) {
    const unsigned grammar_flags =
        flags & (flag_ecmascript | flag_basic | flag_extended |
                 flag_awk | flag_grep | flag_egrep);
    if (grammar_flags == 0 || grammar_flags == flag_ecmascript) {
        return grammar::ecmascript;
    }
    if ((grammar_flags & (grammar_flags - 1)) != 0) {
        throw parse_failure(error_ctype, 0);
    }
    if ((grammar_flags & flag_basic) != 0) {
        return grammar::basic;
    }
    if ((grammar_flags & flag_extended) != 0) {
        return grammar::extended;
    }
    if ((grammar_flags & flag_awk) != 0) {
        return grammar::awk;
    }
    if ((grammar_flags & flag_grep) != 0) {
        return grammar::grep;
    }
    return grammar::egrep;
}

class bytecode_compiler {
public:
    bytecode_compiler(
        const vector<node>& nodes,
        size_t root)
        : nodes_(nodes), root_(root) {}

    vector<code> compile() {
        codes_.push_back(code{});
        compile_node(root_, 0);
        emit(0, instruction{operation::accept});
        return std::move(codes_);
    }

private:
    const vector<node>& nodes_;
    size_t root_;
    vector<code> codes_;

    size_t emit(size_t code_index, instruction value) {
        vector<instruction>& target =
            codes_[code_index].instructions;
        if (target.size() >= maximum_program_size) {
            throw parse_failure(error_space, 0);
        }
        target.push_back(value);
        return target.size() - 1;
    }

    void compile_node(size_t index, size_t code_index) {
        const node value = nodes_[index];
        switch (value.kind) {
        case node_kind::empty:
            return;
        case node_kind::literal:
            emit(code_index, instruction{
                operation::character, 0, 0,
                static_cast<uint32_t>(value.value)});
            return;
        case node_kind::dot:
            emit(code_index, instruction{operation::any});
            return;
        case node_kind::character_class:
            emit(code_index, instruction{
                operation::character_class,
                value.value});
            return;
        case node_kind::sequence:
            compile_node(value.left, code_index);
            compile_node(value.right, code_index);
            return;
        case node_kind::alternative: {
            const size_t split = emit(
                code_index, instruction{operation::split});
            const size_t first =
                codes_[code_index].instructions.size();
            compile_node(value.left, code_index);
            const size_t jump = emit(
                code_index, instruction{operation::jump});
            const size_t second =
                codes_[code_index].instructions.size();
            compile_node(value.right, code_index);
            const size_t end =
                codes_[code_index].instructions.size();
            codes_[code_index].instructions[split].first = first;
            codes_[code_index].instructions[split].second = second;
            codes_[code_index].instructions[jump].first = end;
            return;
        }
        case node_kind::repeat:
            compile_repeat(value, code_index);
            return;
        case node_kind::capture:
            emit(code_index, instruction{
                operation::save, value.value * 2});
            compile_node(value.left, code_index);
            emit(code_index, instruction{
                operation::save, value.value * 2 + 1});
            return;
        case node_kind::backreference:
            emit(code_index, instruction{
                operation::backreference, value.value});
            return;
        case node_kind::begin:
            emit(code_index, instruction{operation::begin});
            return;
        case node_kind::end:
            emit(code_index, instruction{operation::end});
            return;
        case node_kind::word_boundary:
            emit(code_index, instruction{
                operation::word_boundary, 0, 0, 0,
                value.inverted});
            return;
        case node_kind::lookahead: {
            const size_t assertion = codes_.size();
            codes_.push_back(code{});
            compile_node(value.left, assertion);
            emit(assertion, instruction{operation::accept});
            emit(code_index, instruction{
                operation::lookahead, assertion, 0, 0,
                value.inverted});
            return;
        }
        }
    }

    void compile_repeat(const node& value, size_t code_index) {
        for (size_t count = 0; count < value.minimum; ++count) {
            compile_node(value.left, code_index);
        }
        if (value.maximum == value.minimum) {
            return;
        }

        if (value.maximum == unlimited) {
            const size_t split = emit(
                code_index, instruction{operation::split});
            const size_t body =
                codes_[code_index].instructions.size();
            compile_node(value.left, code_index);
            emit(code_index, instruction{
                operation::jump, split});
            const size_t end =
                codes_[code_index].instructions.size();
            instruction& branch =
                codes_[code_index].instructions[split];
            branch.first = value.greedy ? body : end;
            branch.second = value.greedy ? end : body;
            branch.value = 1;
            branch.inverted = value.greedy;
            return;
        }

        for (size_t count = value.minimum;
             count < value.maximum; ++count) {
            const size_t split = emit(
                code_index, instruction{operation::split});
            const size_t body =
                codes_[code_index].instructions.size();
            compile_node(value.left, code_index);
            const size_t end =
                codes_[code_index].instructions.size();
            instruction& branch =
                codes_[code_index].instructions[split];
            branch.first = value.greedy ? body : end;
            branch.second = value.greedy ? end : body;
        }
    }
};

} // namespace

struct program {
    size_t references = 1;
    unsigned syntax_flags = 0;
    size_t captures = 0;
    size_t reported_captures = 0;
    grammar selected_grammar = grammar::ecmascript;
    traits character_traits{};
    vector<character_class> classes;
    vector<code> codes;
    bool nfa_eligible = false;
};

namespace {

struct match_context {
    const program* expression;
    const uint32_t* input;
    size_t size;
    uint32_t previous;
    bool has_previous;
    unsigned match_flags;
    size_t budget;
    size_t steps = 0;
};

struct state {
    size_t pc;
    size_t position;
    vector<ptrdiff_t> captures;
    vector<size_t> loop_positions;
};

bool translated_equal(
    const program* expression, uint32_t left, uint32_t right) {
    const bool icase =
        (expression->syntax_flags & flag_icase) != 0;
    return expression->character_traits.translate(
               expression->character_traits.context, left, icase) ==
           expression->character_traits.translate(
               expression->character_traits.context, right, icase);
}

bool class_matches(
    const program* expression,
    const character_class& character_set,
    uint32_t character) {
    const bool icase =
        (expression->syntax_flags & flag_icase) != 0;
    bool matched = false;
    for (uint32_t single : character_set.singles) {
        if (translated_equal(expression, single, character)) {
            matched = true;
            break;
        }
    }
    if (!matched) {
        for (const range& current : character_set.ranges) {
            if (expression->character_traits.in_range(
                    expression->character_traits.context,
                    character, current.first, current.last,
                    (expression->syntax_flags & flag_collate) != 0,
                    icase)) {
                matched = true;
                break;
            }
        }
    }
    if (!matched) {
        for (const named_class& current : character_set.names) {
            bool current_match =
                expression->character_traits.is_class(
                    expression->character_traits.context,
                    character, current.name.data(),
                    current.name.size(), icase);
            if (current.inverted) {
                current_match = !current_match;
            }
            if (current_match) {
                matched = true;
                break;
            }
        }
    }
    if (!matched) {
        for (const vector<uint32_t>& current :
             character_set.equivalents) {
            if (expression->character_traits.is_equivalent(
                    expression->character_traits.context,
                    character, current.data(), current.size())) {
                matched = true;
                break;
            }
        }
    }
    return character_set.inverted ? !matched : matched;
}

bool is_line_terminator(uint32_t character) {
    return character == static_cast<uint32_t>('\n') ||
           character == static_cast<uint32_t>('\r') ||
           character == 0x2028 || character == 0x2029;
}

bool is_word(const match_context& context, uint32_t character) {
    static const uint32_t word[] = {'w', 'o', 'r', 'd'};
    return context.expression->character_traits.is_class(
        context.expression->character_traits.context,
        character, word, 4,
        (context.expression->syntax_flags & flag_icase) != 0);
}

bool at_begin(const match_context& context, size_t position) {
    if (position != 0) {
        return context.expression->selected_grammar ==
                   grammar::ecmascript &&
               (context.expression->syntax_flags & flag_multiline) != 0 &&
               is_line_terminator(context.input[position - 1]);
    }
    if ((context.match_flags & match_iterator_progress) != 0) {
        return context.expression->selected_grammar ==
                   grammar::ecmascript &&
               (context.expression->syntax_flags & flag_multiline) != 0 &&
               context.has_previous &&
               is_line_terminator(context.previous);
    }
    if ((context.match_flags & match_prev_avail) != 0 &&
        context.has_previous) {
        return true;
    }
    if ((context.match_flags & match_not_bol) != 0) {
        return false;
    }
    return true;
}

bool at_end(const match_context& context, size_t position) {
    if (position != context.size) {
        return context.expression->selected_grammar ==
                   grammar::ecmascript &&
               (context.expression->syntax_flags & flag_multiline) != 0 &&
               is_line_terminator(context.input[position]);
    }
    return (context.match_flags & match_not_eol) == 0;
}

bool at_word_boundary(
    const match_context& context, size_t position) {
    const bool before =
        position == 0
            ? (context.has_previous &&
               (context.match_flags & match_prev_avail) != 0 &&
               is_word(context, context.previous))
            : is_word(context, context.input[position - 1]);
    const bool after =
        position != context.size &&
        is_word(context, context.input[position]);
    if (before == after) {
        return false;
    }
    if (!before && after &&
        (context.match_flags & match_not_bow) != 0 &&
        (context.match_flags & match_prev_avail) == 0) {
        return false;
    }
    if (before && !after &&
        (context.match_flags & match_not_eow) != 0) {
        return false;
    }
    return true;
}

bool any_matches(
    const match_context& context, uint32_t character) {
    if (context.expression->selected_grammar == grammar::ecmascript) {
        return !is_line_terminator(character);
    }
    return character != 0 &&
           character != static_cast<uint32_t>('\n');
}

bool better_posix(
    const vector<ptrdiff_t>& candidate,
    const vector<ptrdiff_t>& current) {
    if (current.empty()) {
        return true;
    }
    if (candidate[1] != current[1]) {
        return candidate[1] > current[1];
    }
    const size_t count =
        candidate.size() < current.size()
            ? candidate.size()
            : current.size();
    for (size_t index = 2; index + 1 < count; index += 2) {
        const ptrdiff_t candidate_start = candidate[index];
        const ptrdiff_t current_start = current[index];
        if (candidate_start != current_start) {
            if (candidate_start < 0) {
                return false;
            }
            if (current_start < 0) {
                return true;
            }
            return candidate_start < current_start;
        }
        const ptrdiff_t candidate_length =
            candidate[index + 1] - candidate_start;
        const ptrdiff_t current_length =
            current[index + 1] - current_start;
        if (candidate_length != current_length) {
            return candidate_length > current_length;
        }
    }
    return false;
}

match_status run_vm(
    match_context& context,
    size_t code_index,
    size_t start,
    bool require_full_match,
    bool posix,
    vector<ptrdiff_t>& captures,
    size_t assertion_depth);

bool instruction_consumes(
    match_context& context,
    const instruction& current,
    state& active) {
    if (active.position >= context.size) {
        return false;
    }
    const uint32_t character = context.input[active.position];
    switch (current.op) {
    case operation::character:
        if (!translated_equal(
                context.expression, current.value, character)) {
            return false;
        }
        break;
    case operation::any:
        if (!any_matches(context, character)) {
            return false;
        }
        break;
    case operation::character_class:
        if (!class_matches(
                context.expression,
                context.expression->classes[current.first],
                character)) {
            return false;
        }
        break;
    default:
        return false;
    }
    ++active.position;
    ++active.pc;
    return true;
}

match_status run_vm(
    match_context& context,
    size_t code_index,
    size_t start,
    bool require_full_match,
    bool posix,
    vector<ptrdiff_t>& captures,
    size_t assertion_depth) {
    if (assertion_depth > maximum_parse_depth) {
        return match_status::error_stack;
    }

    const code& current_code =
        context.expression->codes[code_index];
    vector<state> pending;
    state initial;
    initial.pc = 0;
    initial.position = start;
    initial.captures = captures;
    initial.loop_positions.assign(
        current_code.instructions.size(), unlimited);
    pending.push_back(std::move(initial));

    vector<ptrdiff_t> best;
    while (!pending.empty()) {
        state active = std::move(pending.back());
        pending.pop_back();

        for (;;) {
            if (++context.steps > context.budget) {
                return match_status::error_complexity;
            }
            if (active.pc >= current_code.instructions.size()) {
                break;
            }
            const instruction& current =
                current_code.instructions[active.pc];
            if (instruction_consumes(context, current, active)) {
                continue;
            }

            switch (current.op) {
            case operation::character:
            case operation::any:
            case operation::character_class:
                active.pc = current_code.instructions.size();
                break;
            case operation::split: {
                if (current.value == 1 &&
                    active.loop_positions[active.pc] ==
                        active.position) {
                    active.pc = current.inverted
                        ? current.second
                        : current.first;
                    continue;
                }
                if (current.value == 1) {
                    active.loop_positions[active.pc] =
                        active.position;
                }
                state deferred = active;
                deferred.pc = current.second;
                pending.push_back(std::move(deferred));
                active.pc = current.first;
                continue;
            }
            case operation::jump:
                active.pc = current.first;
                continue;
            case operation::save:
                if (current.first < active.captures.size()) {
                    active.captures[current.first] =
                        static_cast<ptrdiff_t>(active.position);
                }
                ++active.pc;
                continue;
            case operation::backreference: {
                const size_t slot = current.first * 2;
                if (slot + 1 >= active.captures.size() ||
                    active.captures[slot] < 0 ||
                    active.captures[slot + 1] < 0) {
                    ++active.pc;
                    continue;
                }
                const size_t first =
                    static_cast<size_t>(active.captures[slot]);
                const size_t last =
                    static_cast<size_t>(active.captures[slot + 1]);
                const size_t length = last - first;
                if (active.position + length > context.size) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                bool equal = true;
                for (size_t index = 0; index < length; ++index) {
                    if (!translated_equal(
                            context.expression,
                            context.input[first + index],
                            context.input[active.position + index])) {
                        equal = false;
                        break;
                    }
                }
                if (!equal) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                active.position += length;
                ++active.pc;
                continue;
            }
            case operation::begin:
                if (!at_begin(context, active.position)) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                ++active.pc;
                continue;
            case operation::end:
                if (!at_end(context, active.position)) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                ++active.pc;
                continue;
            case operation::word_boundary: {
                const bool boundary =
                    at_word_boundary(context, active.position);
                if (boundary == current.inverted) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                ++active.pc;
                continue;
            }
            case operation::lookahead: {
                vector<ptrdiff_t> assertion_captures =
                    active.captures;
                const match_status assertion = run_vm(
                    context, current.first, active.position,
                    false, false, assertion_captures,
                    assertion_depth + 1);
                if (assertion == match_status::error_complexity ||
                    assertion == match_status::error_stack) {
                    return assertion;
                }
                const bool success =
                    assertion == match_status::matched;
                if (success == current.inverted) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                if (!current.inverted) {
                    active.captures =
                        std::move(assertion_captures);
                }
                ++active.pc;
                continue;
            }
            case operation::accept:
                if (require_full_match &&
                    active.position != context.size) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                if (assertion_depth == 0 &&
                    (context.match_flags & match_not_null) != 0 &&
                    active.position == start) {
                    active.pc = current_code.instructions.size();
                    break;
                }
                active.captures[0] =
                    static_cast<ptrdiff_t>(start);
                active.captures[1] =
                    static_cast<ptrdiff_t>(active.position);
                if (!posix) {
                    captures = std::move(active.captures);
                    return match_status::matched;
                }
                if (better_posix(active.captures, best)) {
                    best = std::move(active.captures);
                }
                active.pc = current_code.instructions.size();
                break;
            }
            break;
        }
    }

    if (!best.empty()) {
        captures = std::move(best);
        return match_status::matched;
    }
    return match_status::no_match;
}

struct nfa_thread {
    size_t pc;
    vector<ptrdiff_t> captures;
};

match_status add_nfa_thread(
    match_context& context,
    vector<nfa_thread>& target,
    vector<unsigned char>& visited,
    nfa_thread active,
    size_t position) {
    const code& current_code = context.expression->codes[0];
    for (;;) {
        if (++context.steps > context.budget) {
            return match_status::error_complexity;
        }
        if (active.pc >= current_code.instructions.size()) {
            return match_status::no_match;
        }
        if (visited[active.pc] != 0) {
            const instruction& repeated =
                current_code.instructions[active.pc];
            if (repeated.op == operation::split &&
                repeated.value == 1) {
                active.pc = repeated.inverted
                    ? repeated.second
                    : repeated.first;
                continue;
            }
            return match_status::no_match;
        }
        visited[active.pc] = 1;
        const instruction& current =
            current_code.instructions[active.pc];
        switch (current.op) {
        case operation::split: {
            nfa_thread first = active;
            first.pc = current.first;
            nfa_thread second = active;
            second.pc = current.second;
            const match_status status = add_nfa_thread(
                context, target, visited,
                std::move(first), position);
            if (status != match_status::no_match) {
                return status;
            }
            active = std::move(second);
            continue;
        }
        case operation::jump:
            active.pc = current.first;
            continue;
        case operation::save:
            if (current.first < active.captures.size()) {
                active.captures[current.first] =
                    static_cast<ptrdiff_t>(position);
            }
            ++active.pc;
            continue;
        case operation::begin:
            if (!at_begin(context, position)) {
                return match_status::no_match;
            }
            ++active.pc;
            continue;
        case operation::end:
            if (!at_end(context, position)) {
                return match_status::no_match;
            }
            ++active.pc;
            continue;
        case operation::word_boundary:
            if (at_word_boundary(context, position) ==
                current.inverted) {
                return match_status::no_match;
            }
            ++active.pc;
            continue;
        default:
            target.push_back(std::move(active));
            return match_status::no_match;
        }
    }
}

match_status run_nfa(
    match_context& context,
    size_t start,
    bool require_full_match,
    vector<ptrdiff_t>& captures) {
    const code& current_code = context.expression->codes[0];
    vector<nfa_thread> active;
    vector<unsigned char> visited(
        current_code.instructions.size(), 0);
    nfa_thread initial{0, captures};
    match_status status = add_nfa_thread(
        context, active, visited, std::move(initial), start);
    if (status != match_status::no_match) {
        return status;
    }

    vector<ptrdiff_t> candidate;
    for (size_t position = start;; ++position) {
        size_t accept_index = active.size();
        for (size_t index = 0; index < active.size(); ++index) {
            const instruction& current =
                current_code.instructions[active[index].pc];
            if (current.op == operation::accept) {
                vector<ptrdiff_t> accepted =
                    active[index].captures;
                accepted[0] = static_cast<ptrdiff_t>(start);
                accepted[1] = static_cast<ptrdiff_t>(position);
                const bool valid =
                    (!require_full_match ||
                     position == context.size) &&
                    ((context.match_flags & match_not_null) == 0 ||
                     position != start);
                if (valid) {
                    accept_index = index;
                    candidate = std::move(accepted);
                    if (index == 0) {
                        captures = std::move(candidate);
                        return match_status::matched;
                    }
                }
                if (valid) {
                    break;
                }
            }
        }

        if (position == context.size) {
            break;
        }

        vector<nfa_thread> next;
        vector<unsigned char> next_visited(
            current_code.instructions.size(), 0);
        for (size_t index = 0;
             index < active.size() && index < accept_index;
             ++index) {
            nfa_thread thread = std::move(active[index]);
            state consumable{
                thread.pc, position, thread.captures, {}};
            const instruction& current =
                current_code.instructions[thread.pc];
            if (!instruction_consumes(
                    context, current, consumable)) {
                continue;
            }
            thread.pc = consumable.pc;
            thread.captures = std::move(consumable.captures);
            status = add_nfa_thread(
                context, next, next_visited,
                std::move(thread), position + 1);
            if (status != match_status::no_match) {
                return status;
            }
        }
        if (next.empty()) {
            break;
        }
        active = std::move(next);
    }

    if (!candidate.empty()) {
        captures = std::move(candidate);
        return match_status::matched;
    }
    return match_status::no_match;
}

} // namespace

program* compile(
    const uint32_t* expression,
    size_t size,
    unsigned syntax_flags,
    const traits& character_traits,
    error& result) {
    result = error{error_space, 0};
    program* compiled = nullptr;
    try {
        const grammar selected = select_grammar(syntax_flags);
        parser expression_parser(
            expression, size, syntax_flags, selected,
            character_traits);
        const size_t root = expression_parser.parse();
        bytecode_compiler compiler(
            expression_parser.nodes(), root);

        compiled = new program();
        compiled->syntax_flags = syntax_flags;
        if ((compiled->syntax_flags &
             (flag_ecmascript | flag_basic | flag_extended |
              flag_awk | flag_grep | flag_egrep)) == 0) {
            compiled->syntax_flags |= flag_ecmascript;
        }
        compiled->captures = expression_parser.captures();
        compiled->reported_captures =
            (syntax_flags & flag_nosubs) != 0
                ? 0
                : compiled->captures;
        compiled->selected_grammar = selected;
        compiled->character_traits = character_traits;
        compiled->character_traits.context =
            character_traits.clone(character_traits.context);
        compiled->classes = std::move(expression_parser.classes());
        compiled->codes = compiler.compile();
        compiled->nfa_eligible =
            selected == grammar::ecmascript &&
            !expression_parser.requires_backtracking();
        return compiled;
    } catch (const parse_failure& failure) {
        if (compiled != nullptr) {
            if (compiled->character_traits.context != nullptr &&
                compiled->character_traits.destroy != nullptr) {
                compiled->character_traits.destroy(
                    compiled->character_traits.context);
            }
            delete compiled;
        }
        result = error{failure.code, failure.position};
        return nullptr;
    } catch (const bad_alloc&) {
        if (compiled != nullptr) {
            if (compiled->character_traits.context != nullptr &&
                compiled->character_traits.destroy != nullptr) {
                compiled->character_traits.destroy(
                    compiled->character_traits.context);
            }
            delete compiled;
        }
        result = error{error_space, 0};
        return nullptr;
    }
}

void retain(program* value) noexcept {
    if (value != nullptr) {
        __atomic_add_fetch(
            &value->references, static_cast<size_t>(1),
            __ATOMIC_RELAXED);
    }
}

void release(program* value) noexcept {
    if (value == nullptr ||
        __atomic_sub_fetch(
            &value->references, static_cast<size_t>(1),
            __ATOMIC_ACQ_REL) != 0) {
        return;
    }
    value->character_traits.destroy(
        value->character_traits.context);
    delete value;
}

size_t mark_count(const program* value) noexcept {
    return value == nullptr ? 0 : value->reported_captures;
}

unsigned flags(const program* value) noexcept {
    return value == nullptr ? flag_ecmascript : value->syntax_flags;
}

match_status search(
    const program* expression,
    const uint32_t* input,
    size_t size,
    uint32_t previous,
    bool has_previous,
    unsigned flags_value,
    bool require_full_match,
    span* results,
    size_t result_count) {
    if (expression == nullptr) {
        return match_status::no_match;
    }

    match_context context{
        expression,
        input,
        size,
        previous,
        has_previous,
        flags_value,
        4096 * (size == 0 ? 1 : size),
        0};
    if (context.budget < size) {
        context.budget = numeric_limits<size_t>::max();
    }

    const bool posix =
        expression->selected_grammar != grammar::ecmascript;
    const size_t capture_count =
        (expression->captures + 1) * 2;
    const size_t last_start =
        (flags_value & match_continuous) != 0 ||
        require_full_match
            ? 0
            : size;
    for (size_t start = 0; start <= last_start; ++start) {
        vector<ptrdiff_t> captures(capture_count, -1);
        const match_status status =
            expression->nfa_eligible
                ? run_nfa(
                      context, start, require_full_match,
                      captures)
                : run_vm(
                      context, 0, start,
                      require_full_match, posix,
                      captures, 0);
        if (status == match_status::error_complexity ||
            status == match_status::error_stack) {
            return status;
        }
        if (status != match_status::matched) {
            continue;
        }
        if ((flags_value & match_not_null) != 0 &&
            captures[0] == captures[1]) {
            continue;
        }

        const size_t count =
            result_count < expression->reported_captures + 1
                ? result_count
                : expression->reported_captures + 1;
        for (size_t index = 0; index < count; ++index) {
            const ptrdiff_t first = captures[index * 2];
            const ptrdiff_t second = captures[index * 2 + 1];
            results[index] = span{
                first, second, first >= 0 && second >= first};
        }
        return match_status::matched;
    }
    return match_status::no_match;
}

} // namespace __regex_runtime
} // namespace __adinkra_v1
} // namespace std
