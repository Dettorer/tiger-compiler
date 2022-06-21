//! A regex-based lexer strongly inspired by [krsnik02](https://crates.io/users/krsnik02)'s
//! [regex-lexer](https://crates.io/crates/regex-lexer) crate. It essentially works the same way,
//! with the addition of a [`Location`](Location) attached to each token

use super::{Location, TextPoint};
use regex::{Regex, RegexSet};
use std::io::BufRead;

#[derive(Debug, PartialEq)]
pub enum TokenVariant {
    // reserved keywords
    Array,
    Break,
    Do,
    Else,
    End,
    For,
    Function,
    If,
    In,
    Let,
    Nil,
    Of,
    Then,
    To,
    Type,
    Var,
    While,

    // punctuation symbols
    Comma,
    Colon,
    Semicolon,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftCurlyBracket,
    RightCurlyBracket,
    Dot,
    PlusSign,
    Dash,
    Star,
    Slash,
    EqualSign,
    DiffSign,
    LeftChevron,
    RightChevron,
    InferiorOrEqualSign,
    SuperiorOrEqualSign,
    Ampersand,
    Pipe,
    AssignmentSign,

    // complex tokens
    Id(String),
    IntLiteral(u32),
    StringLiteral(String),

    // ignored syntax elements
    Comment,
    NewLine,
    WhiteSpace,
}

impl TokenVariant {
    pub fn is_ignored(&self) -> bool {
        matches!(
            self,
            TokenVariant::Comment | TokenVariant::NewLine | TokenVariant::WhiteSpace
        )
    }
}

fn parse_ascii_code(digits: &[u8], location: Location) -> char {
    let code_str = std::str::from_utf8(digits).unwrap_or_else(|err| {
        panic!(
            "internal error parsing ascii code escape sequence in a string at {} ({})",
            location, err
        )
    });
    let code = u8::from_str_radix(code_str, 10).unwrap_or_else(|err| {
        panic!(
            "invalid ascii code \"{}\" at {} ({})",
            code_str, location, err
        )
    });

    code as char
}

fn parse_string_literal(literal: &str, location: Location) -> String {
    let mut parsed = String::new();

    let content: Vec<u8> = literal.bytes().collect();
    let mut remaining_content = &content[1..&content.len() - 1];

    // `push_and_advance!(char, length)` pushes `char` to the parsed string and consume `length`
    // characters in the remaining content (move the start of the slide `length` elements to the
    // right)
    macro_rules! push_and_consume {
        ($char:expr, $length:expr) => {{
            parsed.push($char);
            remaining_content = &remaining_content[$length..];
        }};
    }

    // scan the input string copying regular character and replacing escape sequences by the
    // character they describe
    loop {
        match remaining_content {
            // simple escapes
            [b'\\', b'"', ..] => push_and_consume!('"', 2),
            [b'\\', b'n', ..] => push_and_consume!('\n', 2),
            [b'\\', b't', ..] => push_and_consume!('\t', 2),
            [b'\\', b'\\', ..] => push_and_consume!('\\', 2),
            // control characters
            [b'\\', b'^', b'a', ..] => push_and_consume!('\x07', 3),
            [b'\\', b'^', b'b', ..] => push_and_consume!('\x08', 3),
            [b'\\', b'^', b'f', ..] => push_and_consume!('\x0C', 3),
            [b'\\', b'^', b'r', ..] => push_and_consume!('\r', 3),
            [b'\\', b'^', b'v', ..] => push_and_consume!('\x0B', 3),
            [b'\\', b'^', b'0', ..] => push_and_consume!('\0', 3),
            // arbitrary ascii code
            [b'\\', _, _, _, ..] => {
                push_and_consume!(parse_ascii_code(&remaining_content[1..4], location), 4)
            }
            // TODO: ignored formatting sequence (arbitrary length)
            // regular character
            [c, ..] => push_and_consume!(*c as char, 1),
            // end of the string
            [] => break,
        }
    }

    parsed
}

#[derive(Debug)]
pub struct Token {
    pub token_type: TokenVariant,
    pub location: Location,
}

impl Token {
    fn new(token_type: TokenVariant, location: Location) -> Self {
        Token {
            token_type,
            location,
        }
    }
}

type TokenBuilder = fn(Location, &str) -> Token;
macro_rules! simple_builder {
    ($token:expr) => {
        |loc, _| Token::new($token, loc)
    };
}

const PRODUCTION_RULES: &[(&str, TokenBuilder)] = {
    use TokenVariant::*;
    &[
        // identifiers
        //
        // The identifier regex must appear first as identifier tokens have a lower priority than
        // the reserved keywords, who also matches the identifier regex. Later on we use
        // `Iterator::max_by_key` to find the regex in this set that matched the longest string,
        // and if multiple regexes matched a string of the same maximum length, then this function
        // returns the last one on the list.
        (r"^[[:alpha:]][[:alnum:]_]*", |loc, matched_text| {
            Token::new(Id(matched_text.to_string()), loc)
        }),
        // reserved keywords
        (r"^array", simple_builder!(Array)),
        (r"^break", simple_builder!(Break)),
        (r"^do", simple_builder!(Do)),
        (r"^else", simple_builder!(Else)),
        (r"^end", simple_builder!(End)),
        (r"^for", simple_builder!(For)),
        (r"^function", simple_builder!(Function)),
        (r"^if", simple_builder!(If)),
        (r"^in", simple_builder!(In)),
        (r"^let", simple_builder!(Let)),
        (r"^nil", simple_builder!(Nil)),
        (r"^of", simple_builder!(Of)),
        (r"^then", simple_builder!(Then)),
        (r"^to", simple_builder!(To)),
        (r"^type", simple_builder!(Type)),
        (r"^var", simple_builder!(Var)),
        (r"^while", simple_builder!(While)),
        // punctuation symbols
        (r"^,", simple_builder!(Comma)),
        (r"^:", simple_builder!(Colon)),
        (r"^;", simple_builder!(Semicolon)),
        (r"^\(", simple_builder!(LeftParen)),
        (r"^\)", simple_builder!(RightParen)),
        (r"^\[", simple_builder!(LeftBracket)),
        (r"^\]", simple_builder!(RightBracket)),
        (r"^\{", simple_builder!(LeftCurlyBracket)),
        (r"^\}", simple_builder!(RightCurlyBracket)),
        (r"^\.", simple_builder!(Dot)),
        (r"^\+", simple_builder!(PlusSign)),
        (r"^-", simple_builder!(Dash)),
        (r"^\*", simple_builder!(Star)),
        (r"^/", simple_builder!(Slash)),
        (r"^=", simple_builder!(EqualSign)),
        (r"^<>", simple_builder!(DiffSign)),
        (r"^<", simple_builder!(LeftChevron)),
        (r"^>", simple_builder!(RightChevron)),
        (r"^<=", simple_builder!(InferiorOrEqualSign)),
        (r"^>=", simple_builder!(SuperiorOrEqualSign)),
        (r"^&", simple_builder!(Ampersand)),
        (r"^\|", simple_builder!(Pipe)),
        (r"^:=", simple_builder!(AssignmentSign)),
        // string literals
        (r#"^".*?[^\\]?""#, |loc, matched_text| {
            Token::new(StringLiteral(parse_string_literal(matched_text, loc)), loc)
        }),
        // integer literals
        (r"^\d+", |loc, matched_text| {
            Token::new(
                IntLiteral(
                    matched_text
                        .parse()
                        .unwrap_or_else(|_| panic!("out of bound int literal at {}", loc)),
                ),
                loc,
            )
        }),
        // whitespace
        (r"^\s+", simple_builder!(WhiteSpace)),
        // comments
        // FIXME: this doesn't parse comments spanning on multiple lines (because I work line by
        // line), nor does it handle nested comments
        (r"^/\*.*?\*/", simple_builder!(Comment)),
    ]
};

pub struct Lexer<R: BufRead> {
    input: R,
    regex_set: RegexSet,
    regex_list: Vec<Regex>,

    current_line: String,
    current_pos: TextPoint,
}

impl<R: BufRead> Lexer<R> {
    pub fn new(input: R) -> Self {
        let regex_set = RegexSet::new(PRODUCTION_RULES.iter().map(|(regex, _)| *regex))
            .expect("Internal error initializing the lexer");

        let regex_list = PRODUCTION_RULES
            .iter()
            .map(|(regex, _)| Regex::new(regex).expect("Internal error initializing the lexer"))
            .collect();

        Self {
            input,
            regex_set,
            regex_list,
            current_line: String::new(),
            current_pos: TextPoint { line: 0, column: 1 },
        }
    }
}

impl<R: BufRead> Iterator for Lexer<R> {
    type Item = Token;
    fn next(&mut self) -> Option<Token> {
        // check if we need to consume more input
        while self.current_pos.column >= self.current_line.len() {
            self.current_line.clear();
            let res_line = self.input.read_line(&mut self.current_line);
            match res_line {
                Ok(0) => return None, // EOF
                Err(err) => panic!("Error while consuming the input: {}", err),
                Ok(_) => (),
            }

            self.current_pos.line += 1;
            self.current_pos.column = 0;
        }

        // find the best match
        let next_input = &self.current_line[self.current_pos.column..];
        let (rule_index, match_length) = self
            .regex_set
            .matches(next_input)
            .into_iter()
            .map(|rule_index| {
                // find the regex corresponding to this index in `regex_list`
                let matching_regex = self
                    .regex_list
                    .get(rule_index)
                    .expect("Internal error scanning the input");

                // run the regex *a second time* to compute the start and the end of the matched
                // region. this is only needed because RegexSet only tells which regex matched and
                // no other information about what it matched
                let region = matching_regex
                    .find(next_input)
                    .expect("Internal error scanning the input");
                let match_length = region.end() - region.start();

                (rule_index, match_length)
            })
            .max_by_key(|&(_idx, match_length)| match_length)
            .unwrap_or_else(|| panic!("Unknown token at {}", self.current_pos));

        // Build the token
        let matched_col_start = self.current_pos.column;
        let matched_col_end = matched_col_start + match_length;
        let loc = Location {
            start: self.current_pos,
            end: TextPoint {
                line: matched_col_start,
                column: matched_col_end,
            },
        };
        let matched_text = &self.current_line[matched_col_start..matched_col_end];
        let (_, token_builder) = PRODUCTION_RULES
            .get(rule_index)
            .expect("Internal error scanning the input");
        let token = token_builder(loc, matched_text);

        // update our position in the input
        self.current_pos.column += match_length;

        if token.token_type.is_ignored() {
            self.next()
        } else {
            Some(token)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::{self, BufReader, Cursor};

    #[test]
    fn empty() {
        let lexer = Lexer::new(Cursor::new(""));
        assert_eq!(lexer.count(), 0);
    }

    fn check_single_string(input: &str, expected: &str) {
        eprintln!("Parsing ```{}```", input);
        let lexer = Lexer::new(Cursor::new(input));
        let token_list = lexer.collect::<Vec<Token>>();
        assert_eq!(token_list.len(), 1);
        assert_eq!(
            token_list.get(0).unwrap().token_type,
            TokenVariant::StringLiteral(expected.to_string())
        )
    }

    #[test]
    fn test_string_parsing() {
        check_single_string(r#""""#, "");
        check_single_string(r#""\"""#, "\"");
        check_single_string(r#""\086o\116a\105\032T\101st\046""#, "Votai Test.");
    }

    fn token_count_in_example(file_name: &str) -> io::Result<usize> {
        let path = format!("tests/tiger_examples/{}", file_name);
        let reader = BufReader::new(File::open(path)?);
        let lexer = Lexer::new(reader);
        Ok(lexer.count())
    }

    fn check_token_count(file_name: &str, expected: usize) {
        assert_eq!(
            token_count_in_example(file_name).unwrap(),
            expected,
            "expected {} tokens in the example file {}",
            expected,
            file_name
        );
    }

    #[test]
    fn test_token_count() {
        check_token_count("test1.tig", 21);
        check_token_count("test2.tig", 25);
        check_token_count("test3.tig", 37);
        check_token_count("test4.tig", 32);
        check_token_count("test5.tig", 55);
        check_token_count("test6.tig", 41);
    }
}
