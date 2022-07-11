//! A regex-based lexer strongly inspired by [krsnik02](https://crates.io/users/krsnik02)'s
//! [regex-lexer](https://crates.io/crates/regex-lexer) crate. It essentially works the same way,
//! with the addition of a [`Location`](Location) attached to each token

use super::{Location, TextPoint};
use regex::{Regex, RegexSet};

pub trait Token {
    fn is_ignored(&self) -> bool;
}

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

/// Functions usually associated to a regex that build a [`Token`](Token) corresponding to that
/// regex. The functions are given the string it matched and its [location](Location) in the input.
pub type TokenBuilder<TokenType> = fn(Location, &str) -> TokenType;

/// An association similar to flex's production rule. The first element of the tuple is a regex
/// description, the second one is a [`TokenBuilder`](TokenBuilder) function that builds a token of
/// type `TokenType` given the matched string and its location in the input.
pub type LexerRule<TokenType> = (&'static str, TokenBuilder<TokenType>);

/// A Lexer capable of scanning [`Token`](Token)s described by a set of [`LexerRule`](LexerRule)s.
///
/// # Example
///
/// ```
/// use tc::parsing::{Lexer, Location, LexerRule, Token};
///
/// #[derive(Debug, PartialEq)]
/// enum ExampleToken {
///     WhiteSpace,
///     Else,
///     EqualSign,
///     Id(String),
///     If,
///     Then,
/// }
///
/// impl Token for ExampleToken {
///     fn is_ignored(&self) -> bool {
///         *self == ExampleToken::WhiteSpace
///     }
/// }
///
/// let lexing_rules: Vec<LexerRule<ExampleToken>> = vec![
///     // Ids first so they have lower priority than keywords
///     (r"^[[:alpha:]][[:alnum:]_]*", |loc, matched_text| {
///         ExampleToken::Id(matched_text.to_string())
///     }),
///     // keywords
///     (r"^else", |_location, _matched_text| ExampleToken::Else),
///     (r"^=", |_location, _matched_text| ExampleToken::EqualSign),
///     (r"^if", |_location, _matched_text| ExampleToken::If),
///     (r"^then", |_location, _matched_text| ExampleToken::Then),
///     (r"^\s+", |_location, _matched_text| ExampleToken::WhiteSpace),
/// ];
///
/// let lexer = Lexer::new(lexing_rules);
/// let tokens: Vec<ExampleToken> = lexer.scan("if a=nil then b else c").collect();
///
/// assert_eq!(
///     tokens,
///     vec![
///         ExampleToken::If,
///         ExampleToken::Id("a".to_owned()),
///         ExampleToken::EqualSign,
///         ExampleToken::Id("nil".to_owned()),
///         ExampleToken::Then,
///         ExampleToken::Id("b".to_owned()),
///         ExampleToken::Else,
///         ExampleToken::Id("c".to_owned()),
///     ]
/// );
/// ```
pub struct Lexer<TokenType: Token> {
    regex_set: RegexSet,
    regex_list: Vec<Regex>,
    production_rules: Vec<LexerRule<TokenType>>,
}

impl<TokenType: Token> Lexer<TokenType> {
    pub fn new(production_rules: Vec<LexerRule<TokenType>>) -> Self {
        let regex_set = RegexSet::new(production_rules.iter().map(|(regex, _)| *regex))
            .expect("Internal error initializing the lexer");

        let regex_list = production_rules
            .iter()
            .map(|(regex, _)| Regex::new(regex).expect("Internal error initializing the lexer"))
            .collect();

        Self {
            regex_set,
            regex_list,
            production_rules,
        }
    }

    /// Return an [`Iterator`](TokenIterator) over the scanned tokens of `input`.
    ///
    /// See the example of [`Lexer`](Lexer).
    pub fn scan<'a, 'b>(&'a self, input: &'b str) -> TokenIterator<'a, 'b, TokenType> {
        TokenIterator {
            lexer: self,
            input,
            current_pos: TextPoint {
                line: 1,
                column: 1,
                index: 0,
            },
        }
    }
}

/// An iterator that yields [`Token`](Token)s.
pub struct TokenIterator<'a, 'b, TokenType: Token> {
    lexer: &'a Lexer<TokenType>,
    input: &'b str,
    current_pos: TextPoint,
}

impl<'a, 'b, TokenType: Token> Iterator for TokenIterator<'a, 'b, TokenType> {
    type Item = TokenType;

    fn next(&mut self) -> Option<TokenType> {
        let next_input = &self.input[self.current_pos.index..];
        if next_input.is_empty() {
            return None;
        }

        // find the best match
        let (rule_index, matched_length) = self
            .lexer
            .regex_set
            .matches(next_input)
            .into_iter()
            .map(|rule_index| {
                // find the regex corresponding to this index in `regex_list`
                let matching_regex = self
                    .lexer
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

        // Compute the ending point of the token
        let matched_index_end = self.current_pos.index + matched_length - 1;
        let matched_text = &self.input[self.current_pos.index..=matched_index_end];
        let newline_count = matched_text.matches('\n').count();
        let last_newline_pos = if newline_count != 0 {
            // FIXME: last_newline_pos is a *byte* index, I need a way to translate it to a
            // character index (or an rfind version that returns a char index)
            matched_text.rfind('\n').unwrap_or_else(|| panic!("Internal lexer error on token at {}: counted a non-zero number of newlines in the matched text, but rfind() cannot find any.", self.current_pos))
        } else {
            0
        };
        let matched_end_point = TextPoint {
            line: self.current_pos.line + newline_count,
            column: if newline_count == 0 {
                self.current_pos.column + matched_length - 1
            } else {
                matched_length - last_newline_pos - 1
            },
            index: matched_index_end,
        };

        // Build the token
        let loc = Location {
            start: self.current_pos,
            end: matched_end_point,
        };
        let (_, token_builder) = self
            .lexer
            .production_rules
            .get(rule_index)
            .unwrap_or_else(|| panic!("Internal lexer error on token at {}: could not find the corresponding production", loc));
        let token = token_builder(loc, matched_text);

        // update our position in the input
        self.current_pos = TextPoint {
            line: matched_end_point.line,
            column: matched_end_point.column + 1,
            index: matched_end_point.index + 1,
        };

        if token.is_ignored() {
            self.next()
        } else {
            Some(token)
        }
    }
}
