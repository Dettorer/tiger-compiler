//! A regex-based lexer strongly inspired by [krsnik02](https://crates.io/users/krsnik02)'s
//! [regex-lexer](https://crates.io/crates/regex-lexer) crate. It essentially works the same way,
//! with the addition of a [`Location`](Location) attached to each token

use super::{Location, TextPoint, Token, TokenVariant};
use regex::{Regex, RegexSet};

#[derive(Debug)]
pub struct ScanError {
    reason: String,
}

impl ScanError {
    pub fn new(reason: String) -> Self {
        ScanError { reason }
    }
}

impl std::fmt::Display for ScanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.reason)
    }
}

impl std::error::Error for ScanError {}

/// Functions usually associated to a regex that build the [`Token`](Token) corresponding to that
/// regex given the string it matched and its [location](Location) in the input.
type TokenBuilder = fn(Location, &str) -> Token;

/// This array works as an association table similar to flex's production rule. Each element is a
/// tuple, the first element of that tuple is a regex description, the second one is a
/// [`TokenBuilder`](TokenBuilder) function that builds a `[Token]` given the matched string and
/// its location in the input
const PRODUCTION_RULES: &[(&str, TokenBuilder)] = {
    use TokenVariant::*;

    macro_rules! simple_builder {
        ($token:expr) => {
            |loc, _| Token::new($token, loc)
        };
    }

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
        (r#"^"(?s:.)*?[^\\]?""#, |loc, matched_text| {
            Token::new(
                TokenVariant::from_string_literal(matched_text).unwrap_or_else(|err| {
                    panic!("Error parsing a string literal at {}: {}", loc, err)
                }),
                loc,
            )
        }),
        // integer literals
        (r"^\d+", |loc, matched_text| {
            Token::new(
                TokenVariant::from_int_literal(matched_text)
                    .unwrap_or_else(|err| panic!("error parsing int literal at {}: {}", loc, err)),
                loc,
            )
        }),
        // whitespace
        (r"^\s+", simple_builder!(WhiteSpace)),
        // comments
        // TODO: handle nested comments (as per Andrew Appel's grammar)
        (r"^/\*(?s:.)*?\*/", simple_builder!(Comment)),
    ]
};

/// An iterator that yields [`Token`](Token)s.
///
/// # Example
///
/// ```
/// use tc::parser::{Lexer, Token, TokenVariant};
///
/// let lexer = Lexer::new("if a=nil then b else c");
/// let tokens: Vec<Token> = lexer.collect();
///
/// assert_eq!(tokens.len(), 8);
/// assert_eq!(tokens.get(2).unwrap().variant, TokenVariant::EqualSign);
/// ```
pub struct Lexer<'a> {
    input: &'a str,
    regex_set: RegexSet,
    regex_list: Vec<Regex>,

    current_pos: TextPoint,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
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
            current_pos: TextPoint {
                line: 1,
                column: 1,
                index: 0,
            },
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let next_input = &self.input[self.current_pos.index..];
        if next_input.is_empty() {
            return None;
        }

        // find the best match
        let (rule_index, matched_length) = self
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
            // keep only the largest match
            .max_by_key(|&(_idx, match_length)| match_length)
            .unwrap_or_else(|| panic!("Unknown token at {}", self.current_pos));

        // Build the token
        let matched_col_start = self.current_pos.column;
        let matched_col_end = matched_col_start + matched_length;
        let matched_index_start = self.current_pos.index;
        let matched_index_end = matched_index_start + matched_length;
        let loc = Location {
            start: self.current_pos,
            end: TextPoint {
                line: matched_col_start,
                column: matched_col_end,
                index: matched_index_end,
            },
        };
        let matched_text = &self.input[matched_index_start..matched_index_end];
        let (_, token_builder) = PRODUCTION_RULES
            .get(rule_index)
            .expect("Internal error scanning the input");
        let token = token_builder(loc, matched_text);

        // update our position in the input
        self.current_pos.index += matched_length;
        self.current_pos.column += matched_length;
        // check for newlines in the matched text
        if let Some(last_newline_pos) = matched_text.rfind('\n') {
            self.current_pos.line += matched_text.matches('\n').count();
            // FIXME: last_newline_pos is a *byte* index, I need a way to translate it to a
            // character index (or an rfind version that returns a char index)
            self.current_pos.column = matched_text.chars().count() - last_newline_pos;
        }

        if token.variant.is_ignored() {
            self.next()
        } else {
            Some(token)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io;

    #[test]
    fn empty() {
        let lexer = Lexer::new("");
        assert_eq!(lexer.count(), 0);
    }

    fn check_single_string(input: &str, expected: &str) {
        eprintln!("Parsing ```{}```", input);
        let lexer = Lexer::new(input);
        let token_list = lexer.collect::<Vec<Token>>();
        assert_eq!(token_list.len(), 1);
        assert_eq!(
            token_list.get(0).unwrap().variant,
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
        let input = fs::read_to_string(path)?;
        let lexer = Lexer::new(&input);
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

    #[test]
    fn test1_complete_with_positions() {
        let expected_tokens = {
            use TokenVariant::*;
            vec![
                Token {
                    variant: Let,
                    location: Location {
                        start: TextPoint {
                            line: 2,
                            column: 1,
                            index: 42,
                        },
                        end: TextPoint {
                            line: 1,
                            column: 4,
                            index: 45,
                        },
                    },
                },
                Token {
                    variant: Type,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 2,
                            index: 47,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 6,
                            index: 51,
                        },
                    },
                },
                Token {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 8,
                            index: 53,
                        },
                        end: TextPoint {
                            line: 8,
                            column: 15,
                            index: 60,
                        },
                    },
                },
                Token {
                    variant: EqualSign,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 16,
                            index: 61,
                        },
                        end: TextPoint {
                            line: 16,
                            column: 17,
                            index: 62,
                        },
                    },
                },
                Token {
                    variant: Array,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 18,
                            index: 63,
                        },
                        end: TextPoint {
                            line: 18,
                            column: 23,
                            index: 68,
                        },
                    },
                },
                Token {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 24,
                            index: 69,
                        },
                        end: TextPoint {
                            line: 24,
                            column: 26,
                            index: 71,
                        },
                    },
                },
                Token {
                    variant: Id("int".into()),
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 27,
                            index: 72,
                        },
                        end: TextPoint {
                            line: 27,
                            column: 30,
                            index: 75,
                        },
                    },
                },
                Token {
                    variant: Var,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 2,
                            index: 77,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 5,
                            index: 80,
                        },
                    },
                },
                Token {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 6,
                            index: 81,
                        },
                        end: TextPoint {
                            line: 6,
                            column: 10,
                            index: 85,
                        },
                    },
                },
                Token {
                    variant: Colon,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 10,
                            index: 85,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 11,
                            index: 86,
                        },
                    },
                },
                Token {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 11,
                            index: 86,
                        },
                        end: TextPoint {
                            line: 11,
                            column: 18,
                            index: 93,
                        },
                    },
                },
                Token {
                    variant: AssignmentSign,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 19,
                            index: 94,
                        },
                        end: TextPoint {
                            line: 19,
                            column: 21,
                            index: 96,
                        },
                    },
                },
                Token {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 22,
                            index: 97,
                        },
                        end: TextPoint {
                            line: 22,
                            column: 29,
                            index: 104,
                        },
                    },
                },
                Token {
                    variant: LeftBracket,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 30,
                            index: 105,
                        },
                        end: TextPoint {
                            line: 30,
                            column: 31,
                            index: 106,
                        },
                    },
                },
                Token {
                    variant: IntLiteral(10),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 31,
                            index: 106,
                        },
                        end: TextPoint {
                            line: 31,
                            column: 33,
                            index: 108,
                        },
                    },
                },
                Token {
                    variant: RightBracket,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 33,
                            index: 108,
                        },
                        end: TextPoint {
                            line: 33,
                            column: 34,
                            index: 109,
                        },
                    },
                },
                Token {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 35,
                            index: 110,
                        },
                        end: TextPoint {
                            line: 35,
                            column: 37,
                            index: 112,
                        },
                    },
                },
                Token {
                    variant: IntLiteral(0),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 38,
                            index: 113,
                        },
                        end: TextPoint {
                            line: 38,
                            column: 39,
                            index: 114,
                        },
                    },
                },
                Token {
                    variant: In,
                    location: Location {
                        start: TextPoint {
                            line: 5,
                            column: 1,
                            index: 115,
                        },
                        end: TextPoint {
                            line: 1,
                            column: 3,
                            index: 117,
                        },
                    },
                },
                Token {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 2,
                            index: 119,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 6,
                            index: 123,
                        },
                    },
                },
                Token {
                    variant: End,
                    location: Location {
                        start: TextPoint {
                            line: 7,
                            column: 1,
                            index: 124,
                        },
                        end: TextPoint {
                            line: 1,
                            column: 4,
                            index: 127,
                        },
                    },
                },
            ]
        };

        let input = fs::read_to_string("tests/tiger_examples/test1.tig").unwrap();
        let lexer = Lexer::new(&input);
        for (index, (scanned, expected)) in lexer.zip(expected_tokens.iter()).enumerate() {
            assert_eq!(scanned, *expected, "token number {} is different", index);
        }
    }

    #[test]
    fn test_multiline_tokens() {
        let expected_tokens = {
            use TokenVariant::*;
            vec![
                Token {
                    variant: Let,
                    location: Location {
                        start: TextPoint {
                            line: 5,
                            column: 1,
                            index: 49,
                        },
                        end: TextPoint {
                            line: 1,
                            column: 4,
                            index: 52,
                        },
                    },
                },
                Token {
                    variant: Type,
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 2,
                            index: 54,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 6,
                            index: 58,
                        },
                    },
                },
                Token {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 8,
                            index: 60,
                        },
                        end: TextPoint {
                            line: 8,
                            column: 15,
                            index: 67,
                        },
                    },
                },
                Token {
                    variant: EqualSign,
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 16,
                            index: 68,
                        },
                        end: TextPoint {
                            line: 16,
                            column: 17,
                            index: 69,
                        },
                    },
                },
                Token {
                    variant: Array,
                    location: Location {
                        start: TextPoint {
                            line: 8,
                            column: 12,
                            index: 124,
                        },
                        end: TextPoint {
                            line: 12,
                            column: 17,
                            index: 129,
                        },
                    },
                },
                Token {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 8,
                            column: 18,
                            index: 130,
                        },
                        end: TextPoint {
                            line: 18,
                            column: 20,
                            index: 132,
                        },
                    },
                },
                Token {
                    variant: Id("int".into()),
                    location: Location {
                        start: TextPoint {
                            line: 8,
                            column: 21,
                            index: 133,
                        },
                        end: TextPoint {
                            line: 21,
                            column: 24,
                            index: 136,
                        },
                    },
                },
                Token {
                    variant: Var,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 2,
                            index: 138,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 5,
                            index: 141,
                        },
                    },
                },
                Token {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 6,
                            index: 142,
                        },
                        end: TextPoint {
                            line: 6,
                            column: 10,
                            index: 146,
                        },
                    },
                },
                Token {
                    variant: Colon,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 10,
                            index: 146,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 11,
                            index: 147,
                        },
                    },
                },
                Token {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 11,
                            index: 147,
                        },
                        end: TextPoint {
                            line: 11,
                            column: 18,
                            index: 154,
                        },
                    },
                },
                Token {
                    variant: AssignmentSign,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 19,
                            index: 155,
                        },
                        end: TextPoint {
                            line: 19,
                            column: 21,
                            index: 157,
                        },
                    },
                },
                Token {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 22,
                            index: 158,
                        },
                        end: TextPoint {
                            line: 22,
                            column: 29,
                            index: 165,
                        },
                    },
                },
                Token {
                    variant: LeftBracket,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 30,
                            index: 166,
                        },
                        end: TextPoint {
                            line: 30,
                            column: 31,
                            index: 167,
                        },
                    },
                },
                Token {
                    variant: IntLiteral(10),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 31,
                            index: 167,
                        },
                        end: TextPoint {
                            line: 31,
                            column: 33,
                            index: 169,
                        },
                    },
                },
                Token {
                    variant: RightBracket,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 33,
                            index: 169,
                        },
                        end: TextPoint {
                            line: 33,
                            column: 34,
                            index: 170,
                        },
                    },
                },
                Token {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 35,
                            index: 171,
                        },
                        end: TextPoint {
                            line: 35,
                            column: 37,
                            index: 173,
                        },
                    },
                },
                Token {
                    variant: IntLiteral(0),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 38,
                            index: 174,
                        },
                        end: TextPoint {
                            line: 38,
                            column: 39,
                            index: 175,
                        },
                    },
                },
                Token {
                    variant: Var,
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 9,
                            index: 184,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 12,
                            index: 187,
                        },
                    },
                },
                Token {
                    variant: Id("str".into()),
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 13,
                            index: 188,
                        },
                        end: TextPoint {
                            line: 13,
                            column: 16,
                            index: 191,
                        },
                    },
                },
                Token {
                    variant: Colon,
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 16,
                            index: 191,
                        },
                        end: TextPoint {
                            line: 16,
                            column: 17,
                            index: 192,
                        },
                    },
                },
                Token {
                    variant: Id("string".into()),
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 17,
                            index: 192,
                        },
                        end: TextPoint {
                            line: 17,
                            column: 23,
                            index: 198,
                        },
                    },
                },
                Token {
                    variant: AssignmentSign,
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 24,
                            index: 199,
                        },
                        end: TextPoint {
                            line: 24,
                            column: 26,
                            index: 201,
                        },
                    },
                },
                Token {
                    variant: StringLiteral("simple string".into()),
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 27,
                            index: 202,
                        },
                        end: TextPoint {
                            line: 27,
                            column: 42,
                            index: 217,
                        },
                    },
                },
                Token {
                    variant: In,
                    location: Location {
                        start: TextPoint {
                            line: 11,
                            column: 1,
                            index: 218,
                        },
                        end: TextPoint {
                            line: 1,
                            column: 3,
                            index: 220,
                        },
                    },
                },
                Token {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 12,
                            column: 2,
                            index: 222,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 6,
                            index: 226,
                        },
                    },
                },
                Token {
                    variant: DiffSign,
                    location: Location {
                        start: TextPoint {
                            line: 12,
                            column: 7,
                            index: 227,
                        },
                        end: TextPoint {
                            line: 7,
                            column: 9,
                            index: 229,
                        },
                    },
                },
                Token {
                    variant: StringLiteral("this is\n        a multiline\n        string".into()),
                    location: Location {
                        start: TextPoint {
                            line: 12,
                            column: 10,
                            index: 230,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 54,
                            index: 274,
                        },
                    },
                },
                Token {
                    variant: End,
                    location: Location {
                        start: TextPoint {
                            line: 15,
                            column: 1,
                            index: 275,
                        },
                        end: TextPoint {
                            line: 1,
                            column: 4,
                            index: 278,
                        },
                    },
                },
            ]
        };

        let input =
            fs::read_to_string("tests/tiger_examples/test1_multiline_comments_and_strings.tig")
                .unwrap();
        let lexer = Lexer::new(&input);
        for (index, (scanned, expected)) in lexer.zip(expected_tokens.iter()).enumerate() {
            assert_eq!(scanned, *expected, "token number {} is different", index);
        }
    }
}
