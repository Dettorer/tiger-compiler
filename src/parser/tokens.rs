use super::{lexer::ScanError, Location};
use std::{error::Error, num::ParseIntError};

/// Every valid token type in the Tiger language grammar. `Comment`, `NewLine` and `WhiteSpace`
/// aren't technically tokens in the grammar but are used by the lexer to recognize and ignore part
/// of the input
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
    IntLiteral(i32),
    StringLiteral(String),

    // ignored syntax elements
    Comment,
    NewLine,
    WhiteSpace,
}

impl TokenVariant {
    /// Return `true` for tokens that aren't really in the Tiger language grammar and are ignored
    /// by the lexer
    ///
    /// # Example
    ///
    /// ```
    /// use tc::parser::TokenVariant;
    ///
    /// assert!(!TokenVariant::Comma.is_ignored());
    /// assert!(TokenVariant::WhiteSpace.is_ignored());
    /// ```
    pub fn is_ignored(&self) -> bool {
        matches!(
            self,
            TokenVariant::Comment | TokenVariant::NewLine | TokenVariant::WhiteSpace
        )
    }

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
    /// use tc::parser::TokenVariant;
    ///
    /// match TokenVariant::from_string_literal(r#""\tShort text ending with a dot\046""#).unwrap() {
    ///     TokenVariant::StringLiteral(parsed) => assert_eq!(parsed, "\tShort text ending with a dot."),
    ///     _ => panic!("TokenVariant::from_string_literal did not return a TokenVariant::StringLiteral, this should never happen™"),
    /// }
    ///
    /// // Invalid escape sequence
    /// assert!(TokenVariant::from_string_literal(r#""This does not exist \x""#).is_err());
    /// ```
    pub fn from_string_literal(literal: &str) -> Result<TokenVariant, Box<dyn Error>> {
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
                    push_and_consume!(TokenVariant::parse_ascii_code(&remaining_content[1..4])?, 4)
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

        Ok(TokenVariant::StringLiteral(parsed))
    }

    /// Parse the given string as a Tiger language integer literal
    ///
    /// # Example
    ///
    /// ```
    /// use tc::parser::TokenVariant;
    ///
    /// match TokenVariant::from_int_literal("42").unwrap() {
    ///     TokenVariant::IntLiteral(integer) => assert_eq!(integer, 42),
    ///     _ => panic!("TokenVariant::from_int_literal did not return a TokenVariant::IntLiteral, this should never happen™"),
    /// }
    ///
    /// // Out of bound for 32 bits signed integers
    /// assert!(TokenVariant::from_int_literal("3000000000").is_err());
    /// ```
    pub fn from_int_literal(literal: &str) -> Result<Self, ParseIntError> {
        Ok(TokenVariant::IntLiteral(literal.parse()?))
    }
}

#[derive(Debug)]
pub struct Token {
    pub variant: TokenVariant,
    pub location: Location,
}

impl Token {
    pub fn new(token_type: TokenVariant, location: Location) -> Self {
        Token {
            variant: token_type,
            location,
        }
    }
}
