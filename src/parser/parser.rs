//! Parser generation utilies, WIP

pub type Grammar<SymbolType, NonTerminalSymbolType> =
    std::collections::HashMap<Vec<SymbolType>, NonTerminalSymbolType>;

/// Generate a grammar usable by the parser generation utilities from [`parser`](super).
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
/// use tc::{gen_grammar, parser::Grammar};
///
/// /// Terminal grammar symbols
/// #[derive(Debug, PartialEq, Hash, Eq)]
/// enum G311TokenVariant {
///     Begin,
///     Else,
///     End,
///     EqualSign,
///     If,
///     Num,
///     Print,
///     Semicolon,
///     Then,
///     WhiteSpace,
/// }
///
/// /// Non-terminal grammar symbols
/// #[derive(Debug, Hash, PartialEq, Eq)]
/// enum G311NonTerminal {
///     Stm,
///     StmList,
///     Expr,
/// }
///
/// #[derive(Debug, Hash, PartialEq, Eq)]
/// enum G311Symbol {
///     /// Terminal symbol
///     T(G311TokenVariant),
///     /// Non-terminal symbol
///     NT(G311NonTerminal),
/// }
///
/// impl From<G311NonTerminal> for G311Symbol {
///     fn from(sym: G311NonTerminal) -> Self {
///         G311Symbol::NT(sym)
///     }
/// }
///
/// impl From<G311TokenVariant> for G311Symbol {
///     fn from(sym: G311TokenVariant) -> Self {
///         G311Symbol::T(sym)
///     }
/// }
///
/// use G311NonTerminal::*;
/// use G311TokenVariant::*;
/// let grammar: Grammar<G311Symbol, G311NonTerminal> = gen_grammar!(
///     Stm -> If Expr Then Stm Else Stm,
///     Stm -> Begin Stm StmList,
///     Stm -> Print Expr,
///     StmList -> End,
///     StmList -> Semicolon Stm StmList,
///     Expr -> Num EqualSign Num,
/// );
/// ```
#[macro_export]
macro_rules! gen_grammar {
    (
        /// One rule
        $(
            /// Symbol produced by the rule (reduce result)
            $lhs:ident
            ->
            /// Sequence of symbols that produce (reduce to) the left hand side symbol
            $($rhs:ident)+
        )
        ,+ /// Repeat, separated by commas

        /// Allow a trailing comma at the end of the rule list
        $(,)?
    ) => {
        std::collections::HashMap::from([ $((vec![$($rhs.into(), )+], $lhs)),+ ])
    }
}
