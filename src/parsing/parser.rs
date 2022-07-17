//! Parser generation utilies, WIP
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
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
            $($rhs:expr)*
        )
        ,+ // Repeat, separated by commas

        // Allow a trailing comma at the end of the rule list
        $(,)?
    ) => {
        std::collections::HashMap::from([ $((vec![$($rhs, )*], $lhs)),+ ])
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

    nullable_symbols: HashSet<Vec<SymbolType>>,
    first_sets: HashMap<Vec<SymbolType>, HashSet<SymbolType>>,
    follow_sets: HashMap<SymbolType, HashSet<SymbolType>>,

    parsing_table: HashMap<SymbolType, HashMap<SymbolType, Vec<SymbolType>>>,
}

impl<TokenType, SymbolType> Parser<TokenType, SymbolType>
where
    TokenType: Token,
    SymbolType: Symbol + Eq + PartialEq + Hash + Copy + Debug,
{
    pub fn new(
        lexing_rules: Vec<LexerRule<TokenType>>,
        grammar_rules: GrammarRules<SymbolType>,
        start_symbol: SymbolType,
    ) -> Result<Self, String> {
        let mut new_parser = Parser {
            lexer: Lexer::new(lexing_rules),
            grammar_rules,
            start_symbol,
            nullable_symbols: HashSet::new(),
            first_sets: HashMap::new(),
            follow_sets: HashMap::new(),
            parsing_table: HashMap::new(),
        };

        new_parser.populate_grammar_sets();
        new_parser.build_parsing_table()?;

        Ok(new_parser)
    }

    /// Fill the nullable, FIRST and FOLLOW sets for the current grammar
    fn populate_grammar_sets(&mut self) {
        // Algorithm 3.13 from Andrew Appel's book, page 49.
        // comments starting with //* are pseudo code from the book

        //* for each terminal symbol Z { FIRST[Z] <- {Z} }
        for variant in
            SymbolType::possible_symbols().filter(|sym| sym.is_terminal() && !sym.is_ignored())
        {
            self.first_sets
                .entry(vec![variant])
                .or_default()
                .insert(variant);
        }

        //* repeat { ... } until FIRST, FOLLOW, and nullable did not change in this iteration
        let mut something_changed = true;
        while something_changed {
            something_changed = false;

            //* for each production X -> Y1Y2...Yk
            for (symbols, product) in self.grammar_rules.iter() {
                //* if Y1...Yk are all nullable (or if k = 0)
                if symbols
                    .iter()
                    .all(|sym| self.nullable_symbols.contains(&vec![*sym]))
                {
                    //* then nullable[X] <- true
                    something_changed =
                        something_changed || self.nullable_symbols.insert(vec![*product]);
                }

                //* for each i from 1 to k, each j from i + 1 to k
                // skip empty rules
                if symbols.is_empty() {
                    continue;
                }
                let k = symbols.len() - 1;
                for i in 0..=k {
                    // A helper macro that essentially does
                    // `extendee_set[extendee].extend(extension_set[extension])` but does so by
                    // removing the extendee from `set`, calling `.extend` on the removed
                    // value, then inserting the result again. This avoids a mutable/unmutable
                    // borrow conflict. This isn't useful when the two sets are different, but
                    // the option is given for code deduplication purposes.
                    macro_rules! extend_parser_set {
                        ($extendee_set:expr, $extendee_id:expr, $extension_set:expr, $extension_id:expr) => {{
                            // extract the two sets
                            let mut extendee =
                                $extendee_set.remove(&$extendee_id).unwrap_or_default();
                            let extension = $extension_set.entry($extension_id).or_default();

                            // do the actual extension
                            let old_len = extendee.len();
                            extendee.extend(extension.iter());
                            let modified = old_len != extendee.len();

                            // insert the extended set back
                            $extendee_set.insert($extendee_id, extendee);

                            // return a boolean indicating that the extended set is indeed
                            // different than before
                            modified
                        }};

                        ($set:expr, $extendee_id:expr, $extension_id:expr) => {{
                            extend_parser_set!($set, $extendee_id, $set, $extension_id)
                        }};
                    }

                    //* if Y1...Yi-1 are all nullable (or if i = 1)
                    if (i == 0
                        || symbols[0..i]
                            .iter()
                            .all(|sym| self.nullable_symbols.contains(&vec![*sym])))
                        && product != &symbols[i]
                    {
                        //* then FIRST[X] <- FIRST[X] U FIRST[Yi]
                        something_changed = something_changed
                            || extend_parser_set!(
                                self.first_sets,
                                vec![*product],
                                vec![symbols[i]]
                            );
                    }

                    //* if Yi+1...Yk are all nullable (or if i = k)
                    if (i == k
                        || symbols[i + 1..=k]
                            .iter()
                            .all(|sym| self.nullable_symbols.contains(&vec![*sym])))
                        && product != &symbols[i]
                    {
                        //* then FOLLOW[Yi] <- FOLLOW[Yi] U FOLLOW[X]
                        something_changed = something_changed
                            || extend_parser_set!(self.follow_sets, symbols[i], *product);
                    }

                    for j in (i + 1)..=k {
                        //* if Yi+1...Yj-1 are nullable (or if i + 1 = j)
                        if i + 1 == j
                            || symbols[i + 1..j]
                                .iter()
                                .all(|sym| self.nullable_symbols.contains(&vec![*sym]))
                        {
                            //* then FOLLOW[Yi] <- FOLLOW[Yi] U FIRST[Yj]
                            // XXX: The macro isn't really useful here since the sets are different
                            // (there is no two references on the same set), but not using it would
                            // still duplicate a non-negligeable amount of code. Using `.extend` on
                            // the set directly without calling the macro would be a (probably very
                            // small) optimization.
                            something_changed = something_changed
                                || extend_parser_set!(
                                    self.follow_sets,
                                    symbols[i],
                                    self.first_sets,
                                    vec![symbols[j]]
                                );
                        }
                    }

                    //* a string γ is nullable if each symbol in γ is nullable
                    if symbols[i..=k]
                        .iter()
                        .all(|sym| self.nullable_symbols.contains(&vec![*sym]))
                    {
                        something_changed = something_changed
                            || self.nullable_symbols.insert(symbols[i..=k].to_owned());
                    }

                    //* FIRST(Xγ) = FIRST[X]                if not nullable[X]
                    //* FIRST(Xγ) = FIRST[X] U FIRST(γ)     if nullable[X]
                    something_changed = something_changed
                        || extend_parser_set!(
                            self.first_sets,
                            symbols[i..=k].to_owned(),
                            vec![symbols[i]]
                        );
                    if self.nullable_symbols.contains(&vec![symbols[i]]) {
                        something_changed = something_changed
                            || extend_parser_set!(
                                self.first_sets,
                                symbols[i..=k].to_owned(),
                                symbols[i + 1..=k].to_owned()
                            )
                    }
                }
            }
        }
    }

    fn build_parsing_table(&mut self) -> Result<(), String> {
        for (symbols, product) in self.grammar_rules.iter() {
            for first_sym in &self.first_sets[symbols] {
                let insert_result = self
                    .parsing_table
                    .entry(*product)
                    .or_default()
                    .insert(*first_sym, symbols.clone())
                    // `.insert` returns `Some(symbols)` if a value already existed, which means
                    // that the grammar is not LL(1), but only if what we're trying to insert isn't
                    // identical to what's already in the table.
                    .and_then(|existing_symbols| {
                        if &existing_symbols != symbols {
                            Some(existing_symbols)
                        } else {
                            None
                        }
                    });
                if let Some(existing_symbols) = insert_result {
                    return Err(
                        format!(
                            "Ambiguous grammar: duplicate parsing table entry for symbols {:?} and {:?}, trying to insert {:?} while there already is {:?}",
                            product,
                            first_sym,
                            symbols,
                            existing_symbols,
                        )
                    );
                }
            }
        }

        Ok(())
    }

    /// Parse the input string and return a boolean indicating if it is syntactically correct.
    ///
    /// The current algorithm is LL(1) (predictive parsing)
    pub fn parse(&self, _input: &str) -> bool {
        todo!();
    }
}

#[cfg(test)]
mod tests {
    use crate::parsing::Location;
    use strum::{EnumIter, IntoEnumIterator};

    use super::*;

    impl<TokenType, SymbolType> Parser<TokenType, SymbolType>
    where
        TokenType: Token,
        SymbolType: Symbol + Eq + PartialEq + Hash + Copy + Debug,
    {
        pub fn assert_grammar_sets(
            &self,
            nullable_symbols: &HashSet<Vec<SymbolType>>,
            first_sets: &HashMap<Vec<SymbolType>, HashSet<SymbolType>>,
            follow_sets: &HashMap<SymbolType, HashSet<SymbolType>>,
        ) {
            assert_eq!(*nullable_symbols, self.nullable_symbols);
            assert_eq!(*first_sets, self.first_sets);
            assert_eq!(*follow_sets, self.follow_sets);
        }
    }

    // Parsing the grammar 3.11 in Andrew Appel's book (page 45)
    // WIP

    #[derive(Debug, PartialEq, Hash, Eq, EnumIter, Clone, Copy)]
    enum G311Symbol {
        // Terminal symbols
        Begin,
        Else,
        End,
        EqualSign,
        If,
        Num(i32),
        Print,
        Semicolon,
        Then,
        WhiteSpace,

        // Non-terminal symbols
        Stm,
        StmList,
        Expr,
    }

    impl Symbol for G311Symbol {
        type ValueIterator = G311SymbolIter;
        fn is_terminal(&self) -> bool {
            use G311Symbol::*;
            !matches!(*self, Stm | StmList | Expr)
        }

        fn is_ignored(&self) -> bool {
            self == &G311Symbol::WhiteSpace
        }

        fn possible_symbols() -> G311SymbolIter {
            Self::iter()
        }
    }

    #[derive(Debug)]
    struct G311Token {
        symbol: G311Symbol,
        location: Location,
    }

    impl G311Token {
        pub fn new(symbol: G311Symbol, location: Location) -> Self {
            assert!(
                symbol.is_terminal(),
                "cannot create a token with non-terminal symbol {:?}",
                symbol
            );
            G311Token { symbol, location }
        }
    }

    impl Token for G311Token {
        fn is_ignored(&self) -> bool {
            self.symbol.is_ignored()
        }
    }

    const G311_LEXING_RULES: &[LexerRule<G311Token>] = {
        use G311Symbol::*;
        &[
            (r"^begin", |loc, _| G311Token::new(Begin, loc)),
            (r"^else", |loc, _| G311Token::new(Else, loc)),
            (r"^end", |loc, _| G311Token::new(End, loc)),
            (r"^=", |loc, _| G311Token::new(EqualSign, loc)),
            (r"^if", |loc, _| G311Token::new(If, loc)),
            (r"^\d+", |loc, matched_text| {
                G311Token::new(
                    Num(matched_text.parse().unwrap_or_else(|err| {
                        panic!("invalid integer literal at {}: {}", loc, err)
                    })),
                    loc,
                )
            }),
            (r"^print", |loc, _| G311Token::new(Print, loc)),
            (r"^;", |loc, _| G311Token::new(Semicolon, loc)),
            (r"^then", |loc, _| G311Token::new(Then, loc)),
            (r"^\s+", |loc, _| G311Token::new(WhiteSpace, loc)),
        ]
    };

    #[test]
    fn parse_g311_grammar() {
        let num_def = Default::default();
        let grammar_rules: GrammarRules<G311Symbol> = {
            use G311Symbol::*;
            gen_grammar_rules!(
                Stm -> If Expr Then Stm Else Stm,
                Stm -> Begin Stm StmList,
                Stm -> Print Expr,
                StmList -> End,
                StmList -> Semicolon Stm StmList,
                Expr -> Num(num_def) EqualSign Num(num_def),
            )
        };

        let parser =
            Parser::new(G311_LEXING_RULES.to_owned(), grammar_rules, G311Symbol::Stm).unwrap();

        {
            use G311Symbol::*;
            let expected_nullable: HashSet<Vec<G311Symbol>> = HashSet::new();
            let mut expected_first = G311Symbol::possible_symbols()
                .filter(|sym| sym.is_terminal() && !sym.is_ignored())
                .map(|sym| (vec![sym], HashSet::from([sym])))
                .collect::<HashMap<_, _>>();
            expected_first.extend([
                (vec![Stm], HashSet::from([If, Begin, Print])),
                (vec![StmList], HashSet::from([Semicolon, End])),
                (vec![Expr], HashSet::from([Num(num_def)])),
                (vec![Begin, Stm, StmList], HashSet::from([Begin])),
                (vec![Else, Stm], HashSet::from([Else])),
                (vec![EqualSign, Num(num_def)], HashSet::from([EqualSign])),
                (vec![Expr, Then, Stm, Else, Stm], HashSet::from([Num(num_def)])),
                (vec![If, Expr, Then, Stm, Else, Stm], HashSet::from([If])),
                (vec![Num(num_def), EqualSign, Num(num_def)], HashSet::from([Num(num_def)])),
                (vec![Print, Expr], HashSet::from([Print])),
                (vec![Semicolon, Stm, StmList], HashSet::from([Semicolon])),
                (vec![Stm, Else, Stm], HashSet::from([Print, If, Begin])),
                (vec![Stm, StmList], HashSet::from([Print, If, Begin])),
                (vec![Then, Stm, Else, Stm], HashSet::from([Then])),
            ]);
            let expected_follow = HashMap::from([
                (Begin, HashSet::from([If, Begin, Print])),
                (Else, HashSet::from([If, Begin, Print])),
                (End, HashSet::from([Else, End, Semicolon])),
                (EqualSign, HashSet::from([Num(num_def)])),
                (If, HashSet::from([Num(num_def)])),
                (
                    Num(num_def),
                    HashSet::from([EqualSign, Then, Else, Semicolon, End]),
                ),
                (Print, HashSet::from([Num(num_def)])),
                (Semicolon, HashSet::from([If, Begin, Print])),
                (Then, HashSet::from([If, Begin, Print])),
                (Stm, HashSet::from([Else, End, Semicolon])),
                (Expr, HashSet::from([Then, End, Semicolon, Else])),
                (StmList, HashSet::from([Else, End, Semicolon])),
            ]);
            parser.assert_grammar_sets(&expected_nullable, &expected_first, &expected_follow);
        }

        assert!(parser.parse("begin if 2 = 2 then print 1 else print 0; print 42 end"));
    }

    // Parsing the grammar 3.12 in Andrew Appel's book (page 45)
    // WIP
    #[derive(Debug, PartialEq, Hash, Eq, EnumIter, Clone, Copy)]
    enum G312Symbol {
        // Terminal symbols
        D,
        C,
        A,

        // Non-terminal symbols
        Z,
        Y,
        X,
    }

    impl Symbol for G312Symbol {
        type ValueIterator = G312SymbolIter;
        fn is_terminal(&self) -> bool {
            use G312Symbol::*;
            matches!(*self, D | C | A)
        }

        fn is_ignored(&self) -> bool {
            false
        }

        fn possible_symbols() -> G312SymbolIter {
            Self::iter()
        }
    }

    #[derive(Debug)]
    struct G312Token {
        symbol: G312Symbol,
        location: Location,
    }

    impl G312Token {
        pub fn new(symbol: G312Symbol, location: Location) -> Self {
            assert!(
                symbol.is_terminal(),
                "cannot create a token with non-terminal symbol {:?}",
                symbol
            );
            G312Token { symbol, location }
        }
    }

    impl Token for G312Token {
        fn is_ignored(&self) -> bool {
            false
        }
    }

    const G312_LEXING_RULES: &[LexerRule<G312Token>] = {
        use G312Symbol::*;
        &[
            (r"^d", |loc, _| G312Token::new(D, loc)),
            (r"^c", |loc, _| G312Token::new(C, loc)),
            (r"^a", |loc, _| G312Token::new(A, loc)),
        ]
    };

    #[test]
    fn parse_g312_grammar() {
        let grammar_rules: GrammarRules<G312Symbol> = {
            use G312Symbol::*;
            gen_grammar_rules!(
                Z -> D,
                Z -> X Y Z,
                Y -> , // empty
                Y -> C,
                X -> Y,
                X -> A,
            )
        };

        assert!(
            Parser::new(
                G312_LEXING_RULES.to_owned(),
                grammar_rules.clone(),
                G312Symbol::Z
            )
            .is_err(),
            "Grammar G312 is ambiguous for LL(1) parsers, but the parser built successfully"
        );

        // manually build the parser in order to test the grammar sets
        let mut parser = Parser {
            lexer: Lexer::new(G312_LEXING_RULES.to_owned()),
            grammar_rules,
            start_symbol: G312Symbol::Z,
            nullable_symbols: HashSet::new(),
            first_sets: HashMap::new(),
            follow_sets: HashMap::new(),
            parsing_table: HashMap::new(),
        };
        parser.populate_grammar_sets();

        {
            use G312Symbol::*;
            let expected_nullable = HashSet::from([vec![X], vec![Y]]);
            let mut expected_first = G312Symbol::possible_symbols()
                .filter(|sym| sym.is_terminal())
                .map(|sym| (vec![sym], HashSet::from([sym])))
                .collect::<HashMap<_, _>>();
            expected_first.extend([
                (vec![X], HashSet::from([A, C])),
                (vec![Y], HashSet::from([C])),
                (vec![Z], HashSet::from([A, C, D])),
                (vec![X, Y, Z], HashSet::from([A, C, D])),
                (vec![Y, Z], HashSet::from([A, C, D])),
                (vec![], HashSet::new()),
            ]);
            let expected_follow = HashMap::from([
                (X, HashSet::from([A, C, D])),
                (Y, HashSet::from([A, C, D])),
                (Z, HashSet::from([])),
                (A, HashSet::from([A, C, D])),
                (C, HashSet::from([A, C, D])),
                (D, HashSet::from([])),
            ]);
            parser.assert_grammar_sets(&expected_nullable, &expected_first, &expected_follow);
        }

        assert!(parser.parse("d"));
        assert!(parser.parse("ca"));
    }
}
