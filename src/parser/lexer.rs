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

/// Functions usually associated to a regex that build the [`Token`](Token) corresponding to that
/// regex given the string it matched and its [location](Location) in the input.
pub type TokenBuilder<TokenType> = fn(Location, &str) -> TokenType;

/// An association similar to flex's production rule. The first element of the tuple is a regex
/// description, the second one is a [`TokenBuilder`](TokenBuilder) function that builds a token of
/// type `[TokenType]` given the matched string and its location in the input
pub type LexerRule<TokenType> = (&'static str, TokenBuilder<TokenType>);

/// An iterator that yields [`Token`](Token)s.
///
/// # Example
///
/// ```
/// use tc::parser::{Lexer, Location, LexerRule, Token};
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
/// let lexer = Lexer::new("if a=nil then b else c", lexing_rules);
/// let tokens: Vec<ExampleToken> = lexer.collect();
///
/// assert_eq!(tokens.len(), 8);
/// assert_eq!(tokens.get(2), Some(&ExampleToken::EqualSign));
/// ```
pub struct Lexer<'a, TokenType: Token> {
    input: &'a str,
    regex_set: RegexSet,
    regex_list: Vec<Regex>,
    production_rules: Vec<LexerRule<TokenType>>,

    current_pos: TextPoint,
}

impl<'a, TokenType: Token> Lexer<'a, TokenType> {
    pub fn new(input: &'a str, production_rules: Vec<LexerRule<TokenType>>) -> Self {
        let regex_set = RegexSet::new(production_rules.iter().map(|(regex, _)| *regex))
            .expect("Internal error initializing the lexer");

        let regex_list = production_rules
            .iter()
            .map(|(regex, _)| Regex::new(regex).expect("Internal error initializing the lexer"))
            .collect();

        Self {
            input,
            regex_set,
            regex_list,
            production_rules,
            current_pos: TextPoint {
                line: 1,
                column: 1,
                index: 0,
            },
        }
    }
}

impl<'a, TokenType: Token> Iterator for Lexer<'a, TokenType> {
    type Item = TokenType;

    fn next(&mut self) -> Option<TokenType> {
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
        let (_, token_builder) = self
            .production_rules
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

        if token.is_ignored() {
            self.next()
        } else {
            Some(token)
        }
    }
}
