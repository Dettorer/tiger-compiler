use std::{error::Error, num::ParseIntError};

use strum::{EnumIter, IntoEnumIterator};

use super::{Lexer, LexerRule, Location, ScanError, Token, Symbol};

/// Every valid token type in the Tiger language grammar. `Comment`, `NewLine` and `WhiteSpace`
/// aren't technically tokens in the grammar but are used by the lexer to recognize and ignore part
/// of the input.
#[derive(Debug, PartialEq, EnumIter, Clone)]
pub enum TigerTokenVariant {
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
    IntLiteral(i32),
    StringLiteral(String),

    // ignored syntax elements
    Comment,
    NewLine,
    WhiteSpace,
}

impl Symbol for TigerTokenVariant {
    type ValueIterator = TigerTokenVariantIter;

    fn possible_symbols() -> Self::ValueIterator {
        Self::iter()
    }

    fn is_ignored(&self) -> bool {
        matches!(
            self,
            TigerTokenVariant::Comment | TigerTokenVariant::NewLine | TigerTokenVariant::WhiteSpace
        )
    }

    fn is_terminal(&self) -> bool {
        true
    }

    fn to_default(&self) -> Self {
        match self {
            Self::Id(_) => Self::Id(Default::default()),
            Self::IntLiteral(_) => Self::IntLiteral(Default::default()),
            Self::StringLiteral(_) => Self::StringLiteral(Default::default()),
            _ => self.clone(),
        }
    }
}

impl TigerTokenVariant {

    /// Parse an array of `u8` as an array of characters representing an integer in decimal and
    /// return the `char` whose ascii code is that integer
    fn parse_ascii_code(digits: &[u8]) -> Result<char, Box<dyn Error>> {
        let code_str = std::str::from_utf8(digits)?;
        let code = code_str.parse::<u8>()?;

        Ok(code as char)
    }

    /// Parse the given string as a Tiger language string literal that potentially contains escape
    /// sequences. The returned string has every escape sequence replaced by what the described
    ///
    /// # Example
    ///
    /// ```
    /// use tc::parsing::TigerTokenVariant;
    ///
    /// match TigerTokenVariant::from_string_literal(r#""\tShort text ending with a dot\046""#).unwrap() {
    ///     TigerTokenVariant::StringLiteral(parsed) => assert_eq!(parsed, "\tShort text ending with a dot."),
    ///     _ => panic!("TigerTokenVariant::from_string_literal did not return a TigerTokenVariant::StringLiteral, this should never happen™"),
    /// }
    ///
    /// // Invalid escape sequence
    /// assert!(TigerTokenVariant::from_string_literal(r#""This does not exist \x""#).is_err());
    /// ```
    pub fn from_string_literal(literal: &str) -> Result<TigerTokenVariant, Box<dyn Error>> {
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
                [b'\\', a, b, c, ..]
                    if a.is_ascii_digit() && b.is_ascii_digit() && c.is_ascii_digit() =>
                {
                    push_and_consume!(
                        TigerTokenVariant::parse_ascii_code(&remaining_content[1..4])?,
                        4
                    )
                }
                // invalid escape sequence
                [b'\\', ..] => {
                    return Err(Box::new(ScanError::new(
                        "invalid escape sequence".to_string(),
                    )))
                }
                // TODO: ignored formatting sequence (arbitrary length)
                // regular character
                [c, ..] => push_and_consume!(*c as char, 1),
                // end of the string
                [] => break,
            }
        }

        Ok(TigerTokenVariant::StringLiteral(parsed))
    }

    /// Parse the given string as a Tiger language integer literal
    ///
    /// # Example
    ///
    /// ```
    /// use tc::parsing::TigerTokenVariant;
    ///
    /// match TigerTokenVariant::from_int_literal("42").unwrap() {
    ///     TigerTokenVariant::IntLiteral(integer) => assert_eq!(integer, 42),
    ///     _ => panic!("TigerTokenVariant::from_int_literal did not return a TigerTokenVariant::IntLiteral, this should never happen™"),
    /// }
    ///
    /// // Out of bound for 32 bits signed integers
    /// assert!(TigerTokenVariant::from_int_literal("3000000000").is_err());
    /// ```
    pub fn from_int_literal(literal: &str) -> Result<Self, ParseIntError> {
        Ok(TigerTokenVariant::IntLiteral(literal.parse()?))
    }
}

#[derive(Debug, PartialEq)]
pub struct TigerToken {
    pub variant: TigerTokenVariant,
    pub location: Location,
}

impl TigerToken {
    pub fn new(token_type: TigerTokenVariant, location: Location) -> Self {
        TigerToken {
            variant: token_type,
            location,
        }
    }
}

impl Token for TigerToken {
    type SymbolType = TigerTokenVariant;

    fn is_ignored(&self) -> bool {
        self.variant.is_ignored()
    }

    fn symbol(&self) -> &TigerTokenVariant {
        &self.variant
    }
}

const TIGER_LEXING_RULES: &[LexerRule<TigerToken>] = {
    use TigerTokenVariant::*;

    macro_rules! simple_builder {
        ($token:expr) => {
            |loc, _| TigerToken::new($token, loc)
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
            TigerToken::new(Id(matched_text.to_string()), loc)
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
            TigerToken::new(
                TigerTokenVariant::from_string_literal(matched_text).unwrap_or_else(|err| {
                    panic!("Error parsing a string literal at {}: {}", loc, err)
                }),
                loc,
            )
        }),
        // integer literals
        (r"^\d+", |loc, matched_text| {
            TigerToken::new(
                TigerTokenVariant::from_int_literal(matched_text)
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

/// Build and return a [`Lexer`](Lexer) for the Tiger language.
///
/// # Example
///
/// ```
/// use tc::parsing::build_tiger_lexer;
///
/// let lexer = build_tiger_lexer();
/// let token_iterator = lexer.scan("var arr1:arrtype := arrtype [10] of 0");
/// assert_eq!(token_iterator.count(), 11);
/// ```
pub fn build_tiger_lexer() -> Lexer<TigerToken> {
    Lexer::new(TIGER_LEXING_RULES.to_owned())
}

#[cfg(test)]
mod tests {
    use super::super::{Location, TextPoint};
    use super::*;
    use std::fs;
    use std::io;

    #[test]
    fn empty() {
        let lexer = build_tiger_lexer();
        assert_eq!(lexer.scan("").count(), 0);
    }

    fn check_single_string(input: &str, expected: &str) {
        eprintln!("Parsing ```{}```", input);
        let lexer = build_tiger_lexer();
        let token_list = lexer.scan(input).collect::<Vec<TigerToken>>();
        assert_eq!(token_list.len(), 1);
        assert_eq!(
            token_list.get(0).unwrap().variant,
            TigerTokenVariant::StringLiteral(expected.to_string())
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
        let lexer = build_tiger_lexer();
        Ok(lexer.scan(&input).count())
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
            use TigerTokenVariant::*;
            vec![
                TigerToken {
                    variant: Let,
                    location: Location {
                        start: TextPoint {
                            line: 2,
                            column: 1,
                            index: 42,
                        },
                        end: TextPoint {
                            line: 2,
                            column: 3,
                            index: 44,
                        },
                    },
                },
                TigerToken {
                    variant: Type,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 2,
                            index: 47,
                        },
                        end: TextPoint {
                            line: 3,
                            column: 5,
                            index: 50,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 8,
                            index: 53,
                        },
                        end: TextPoint {
                            line: 3,
                            column: 14,
                            index: 59,
                        },
                    },
                },
                TigerToken {
                    variant: EqualSign,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 16,
                            index: 61,
                        },
                        end: TextPoint {
                            line: 3,
                            column: 16,
                            index: 61,
                        },
                    },
                },
                TigerToken {
                    variant: Array,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 18,
                            index: 63,
                        },
                        end: TextPoint {
                            line: 3,
                            column: 22,
                            index: 67,
                        },
                    },
                },
                TigerToken {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 24,
                            index: 69,
                        },
                        end: TextPoint {
                            line: 3,
                            column: 25,
                            index: 70,
                        },
                    },
                },
                TigerToken {
                    variant: Id("int".into()),
                    location: Location {
                        start: TextPoint {
                            line: 3,
                            column: 27,
                            index: 72,
                        },
                        end: TextPoint {
                            line: 3,
                            column: 29,
                            index: 74,
                        },
                    },
                },
                TigerToken {
                    variant: Var,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 2,
                            index: 77,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 4,
                            index: 79,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 6,
                            index: 81,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 9,
                            index: 84,
                        },
                    },
                },
                TigerToken {
                    variant: Colon,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 10,
                            index: 85,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 10,
                            index: 85,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 11,
                            index: 86,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 17,
                            index: 92,
                        },
                    },
                },
                TigerToken {
                    variant: AssignmentSign,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 19,
                            index: 94,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 20,
                            index: 95,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 22,
                            index: 97,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 28,
                            index: 103,
                        },
                    },
                },
                TigerToken {
                    variant: LeftBracket,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 30,
                            index: 105,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 30,
                            index: 105,
                        },
                    },
                },
                TigerToken {
                    variant: IntLiteral(10),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 31,
                            index: 106,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 32,
                            index: 107,
                        },
                    },
                },
                TigerToken {
                    variant: RightBracket,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 33,
                            index: 108,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 33,
                            index: 108,
                        },
                    },
                },
                TigerToken {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 35,
                            index: 110,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 36,
                            index: 111,
                        },
                    },
                },
                TigerToken {
                    variant: IntLiteral(0),
                    location: Location {
                        start: TextPoint {
                            line: 4,
                            column: 38,
                            index: 113,
                        },
                        end: TextPoint {
                            line: 4,
                            column: 38,
                            index: 113,
                        },
                    },
                },
                TigerToken {
                    variant: In,
                    location: Location {
                        start: TextPoint {
                            line: 5,
                            column: 1,
                            index: 115,
                        },
                        end: TextPoint {
                            line: 5,
                            column: 2,
                            index: 116,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 2,
                            index: 119,
                        },
                        end: TextPoint {
                            line: 6,
                            column: 5,
                            index: 122,
                        },
                    },
                },
                TigerToken {
                    variant: End,
                    location: Location {
                        start: TextPoint {
                            line: 7,
                            column: 1,
                            index: 124,
                        },
                        end: TextPoint {
                            line: 7,
                            column: 3,
                            index: 126,
                        },
                    },
                },
            ]
        };

        let input = fs::read_to_string("tests/tiger_examples/test1.tig").unwrap();
        let lexer = build_tiger_lexer();

        lexer
            .scan(&input)
            .zip(expected_tokens.iter())
            .enumerate()
            .for_each(|(index, (scanned, expected))| {
                assert_eq!(scanned, *expected, "token number {} is different", index)
            });
    }

    #[test]
    fn test_multiline_tokens() {
        let expected_tokens = {
            use TigerTokenVariant::*;
            vec![
                TigerToken {
                    variant: Let,
                    location: Location {
                        start: TextPoint {
                            line: 5,
                            column: 1,
                            index: 49,
                        },
                        end: TextPoint {
                            line: 5,
                            column: 3,
                            index: 51,
                        },
                    },
                },
                TigerToken {
                    variant: Type,
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 2,
                            index: 54,
                        },
                        end: TextPoint {
                            line: 6,
                            column: 5,
                            index: 57,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 8,
                            index: 60,
                        },
                        end: TextPoint {
                            line: 6,
                            column: 14,
                            index: 66,
                        },
                    },
                },
                TigerToken {
                    variant: EqualSign,
                    location: Location {
                        start: TextPoint {
                            line: 6,
                            column: 16,
                            index: 68,
                        },
                        end: TextPoint {
                            line: 6,
                            column: 16,
                            index: 68,
                        },
                    },
                },
                TigerToken {
                    variant: Array,
                    location: Location {
                        start: TextPoint {
                            line: 8,
                            column: 12,
                            index: 124,
                        },
                        end: TextPoint {
                            line: 8,
                            column: 16,
                            index: 128,
                        },
                    },
                },
                TigerToken {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 8,
                            column: 18,
                            index: 130,
                        },
                        end: TextPoint {
                            line: 8,
                            column: 19,
                            index: 131,
                        },
                    },
                },
                TigerToken {
                    variant: Id("int".into()),
                    location: Location {
                        start: TextPoint {
                            line: 8,
                            column: 21,
                            index: 133,
                        },
                        end: TextPoint {
                            line: 8,
                            column: 23,
                            index: 135,
                        },
                    },
                },
                TigerToken {
                    variant: Var,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 2,
                            index: 138,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 4,
                            index: 140,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 6,
                            index: 142,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 9,
                            index: 145,
                        },
                    },
                },
                TigerToken {
                    variant: Colon,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 10,
                            index: 146,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 10,
                            index: 146,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 11,
                            index: 147,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 17,
                            index: 153,
                        },
                    },
                },
                TigerToken {
                    variant: AssignmentSign,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 19,
                            index: 155,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 20,
                            index: 156,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arrtype".into()),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 22,
                            index: 158,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 28,
                            index: 164,
                        },
                    },
                },
                TigerToken {
                    variant: LeftBracket,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 30,
                            index: 166,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 30,
                            index: 166,
                        },
                    },
                },
                TigerToken {
                    variant: IntLiteral(10),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 31,
                            index: 167,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 32,
                            index: 168,
                        },
                    },
                },
                TigerToken {
                    variant: RightBracket,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 33,
                            index: 169,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 33,
                            index: 169,
                        },
                    },
                },
                TigerToken {
                    variant: Of,
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 35,
                            index: 171,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 36,
                            index: 172,
                        },
                    },
                },
                TigerToken {
                    variant: IntLiteral(0),
                    location: Location {
                        start: TextPoint {
                            line: 9,
                            column: 38,
                            index: 174,
                        },
                        end: TextPoint {
                            line: 9,
                            column: 38,
                            index: 174,
                        },
                    },
                },
                TigerToken {
                    variant: Var,
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 9,
                            index: 184,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 11,
                            index: 186,
                        },
                    },
                },
                TigerToken {
                    variant: Id("str".into()),
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 13,
                            index: 188,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 15,
                            index: 190,
                        },
                    },
                },
                TigerToken {
                    variant: Colon,
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 16,
                            index: 191,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 16,
                            index: 191,
                        },
                    },
                },
                TigerToken {
                    variant: Id("string".into()),
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 17,
                            index: 192,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 22,
                            index: 197,
                        },
                    },
                },
                TigerToken {
                    variant: AssignmentSign,
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 24,
                            index: 199,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 25,
                            index: 200,
                        },
                    },
                },
                TigerToken {
                    variant: StringLiteral("simple string".into()),
                    location: Location {
                        start: TextPoint {
                            line: 10,
                            column: 27,
                            index: 202,
                        },
                        end: TextPoint {
                            line: 10,
                            column: 41,
                            index: 216,
                        },
                    },
                },
                TigerToken {
                    variant: In,
                    location: Location {
                        start: TextPoint {
                            line: 11,
                            column: 1,
                            index: 218,
                        },
                        end: TextPoint {
                            line: 11,
                            column: 2,
                            index: 219,
                        },
                    },
                },
                TigerToken {
                    variant: Id("arr1".into()),
                    location: Location {
                        start: TextPoint {
                            line: 12,
                            column: 2,
                            index: 222,
                        },
                        end: TextPoint {
                            line: 12,
                            column: 5,
                            index: 225,
                        },
                    },
                },
                TigerToken {
                    variant: DiffSign,
                    location: Location {
                        start: TextPoint {
                            line: 12,
                            column: 7,
                            index: 227,
                        },
                        end: TextPoint {
                            line: 12,
                            column: 8,
                            index: 228,
                        },
                    },
                },
                TigerToken {
                    variant: StringLiteral("this is\n        a multiline\n        string".into()),
                    location: Location {
                        start: TextPoint {
                            line: 12,
                            column: 10,
                            index: 230,
                        },
                        end: TextPoint {
                            line: 14,
                            column: 15,
                            index: 273,
                        },
                    },
                },
                TigerToken {
                    variant: End,
                    location: Location {
                        start: TextPoint {
                            line: 15,
                            column: 1,
                            index: 275,
                        },
                        end: TextPoint {
                            line: 15,
                            column: 3,
                            index: 277,
                        },
                    },
                },
            ]
        };

        let input =
            fs::read_to_string("tests/tiger_examples/test1_multiline_comments_and_strings.tig")
                .unwrap();
        let lexer = build_tiger_lexer();

        lexer
            .scan(&input)
            .zip(expected_tokens.iter())
            .enumerate()
            .for_each(|(index, (scanned, expected))| {
                assert_eq!(scanned, *expected, "token number {} is different", index)
            });
    }
}
