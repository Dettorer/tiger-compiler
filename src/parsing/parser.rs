//! Parser generation utilies, WIP
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use super::{Lexer, LexerRule, Symbol, Token};

pub type GrammarRules<SymbolType> = std::collections::HashMap<Vec<SymbolType>, SymbolType>;

/// Generate a grammar usable by the parser generation utilities from [`parsing`](super).
///
/// `.into()` will be called on every right-hand-side symbol. This allows, for example, to
/// concisely reuse the type you use as lexer [`Token`](super::Token)s if you implement the
/// correct `From` trait (see the example below).
///
/// # Example
///
/// This example builds a representation of Grammar 3.11 from Andrew Appel's book (page 45)
///
/// ```
/// use strum::{EnumIter, IntoEnumIterator};
/// use tc::{gen_grammar_rules, parsing};
///
/// #[derive(Debug, PartialEq, Hash, Eq, EnumIter)]
/// enum G311Symbol {
///     // Terminal symbols
///     Begin,
///     Else,
///     End,
///     EqualSign,
///     If,
///     Num(i32),
///     Print,
///     Semicolon,
///     Then,
///     WhiteSpace,
///
///     // Non-terminal symbols
///     Stm,
///     StmList,
///     Expr,
/// }
///
/// impl parsing::Symbol for G311Symbol {
///     type ValueIterator = G311SymbolIter;
///
///     fn is_terminal(&self) -> bool {
///         use G311Symbol::*;
///         !matches!(*self, Stm | StmList | Expr)
///     }
///
///     fn possible_symbols() -> G311SymbolIter {
///         Self::iter()
///     }
/// }
///
/// let grammar: parsing::GrammarRules<G311Symbol> = {
///     use G311Symbol::*;
///     gen_grammar_rules!(
///         Stm -> If Expr Then Stm Else Stm,
///         Stm -> Begin Stm StmList,
///         Stm -> Print Expr,
///         StmList -> End,
///         StmList -> Semicolon Stm StmList,
///         Expr -> Num(0) EqualSign Num(0),
///     )
/// };
/// ```
#[macro_export]
macro_rules! gen_grammar_rules {
    (
        // One rule
        $(
            // Symbol produced by the rule (reduce result)
            $lhs:ident
            ->
            // Sequence of symbols that produce (reduce to) the left hand side symbol
            $($rhs:expr)+
        )
        ,+ // Repeat, separated by commas

        // Allow a trailing comma at the end of the rule list
        $(,)?
    ) => {
        std::collections::HashMap::from([ $((vec![$($rhs, )+], $lhs)),+ ])
    }
}

/// The internal representation of a grammar
#[derive(Debug)]
pub struct Grammar<SymbolType> {
    rules: GrammarRules<SymbolType>,
    start_symbol: SymbolType,
}

impl<SymbolType> Grammar<SymbolType> {
    /// Build a new grammar using the specified set of reduction rules and start symbol.
    ///
    /// # Example
    ///
    /// See [`gen_grammar_rules`](gen_grammar_rules).
    pub fn new(start_symbol: SymbolType, rules: GrammarRules<SymbolType>) -> Self {
        Grammar {
            rules,
            start_symbol,
        }
    }
}

pub struct Parser<TokenType, SymbolType>
where
    SymbolType: Symbol,
    TokenType: Token,
{
    lexer: Lexer<TokenType>,
    grammar_rules: GrammarRules<SymbolType>,
    start_symbol: SymbolType,

    nullable_symbols: HashSet<SymbolType>,
    first_sets: HashMap<SymbolType, HashSet<SymbolType>>,
    follow_sets: HashMap<SymbolType, HashSet<SymbolType>>,
}

impl<TokenType, SymbolType> Parser<TokenType, SymbolType>
where
    TokenType: Token,
    SymbolType: Symbol + Eq + PartialEq + Hash + Copy,
{
    pub fn new(
        lexing_rules: Vec<LexerRule<TokenType>>,
        grammar_rules: GrammarRules<SymbolType>,
        start_symbol: SymbolType,
    ) -> Self {
        let mut new_parser = Parser {
            lexer: Lexer::new(lexing_rules),
            grammar_rules,
            start_symbol,
            nullable_symbols: HashSet::new(),
            first_sets: HashMap::new(),
            follow_sets: HashMap::new(),
        };

        new_parser.populate_grammar_sets();

        new_parser
    }

    /// Fill the nullable, FIRST and FOLLOW sets for the current grammar
    fn populate_grammar_sets(&mut self) {
        todo!();
    }

    /// Parse the input string and return a boolean indicating if it is syntactically correct.
    ///
    /// The current algorithm is predictive parsing of LL(1) grammar.
    pub fn parse(_input: &str) -> bool {
        todo!();
    }
}
