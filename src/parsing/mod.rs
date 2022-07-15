mod lexer;
mod location;
mod parser;
mod tiger_lexer;

pub trait Symbol {
    type ValueIterator: Iterator<Item = Self>;

    fn is_terminal(&self) -> bool;
    fn possible_symbols() -> Self::ValueIterator;

    fn is_non_terminal(&self) -> bool {
        !self.is_terminal()
    }
}

pub use lexer::{Lexer, LexerRule, ScanError, Token, TokenBuilder, TokenIterator};
pub use location::{Location, TextPoint};
pub use parser::{GrammarRules, Grammar};
pub use tiger_lexer::{build_tiger_lexer, TigerToken, TigerTokenVariant};
