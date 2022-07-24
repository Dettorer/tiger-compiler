//! Parser generation utilies, WIP
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
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
/// #[derive(Debug, PartialEq, Hash, Eq, EnumIter, Clone, Copy)]
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
///     fn possible_symbols() -> G311SymbolIter {
///         Self::iter()
///     }
///
///     fn is_terminal(&self) -> bool {
///         use G311Symbol::*;
///         !matches!(*self, Stm | StmList | Expr)
///     }
///
///     fn is_ignored(&self) -> bool {
///         *self == Self::WhiteSpace
///     }
///
///     fn to_default(&self) -> Self {
///         match self {
///             Self::Num(_) => Self::Num(Default::default()),
///             _ => *self,
///         }
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LRItem<SymbolType: Symbol> {
    lhs: SymbolType,
    rhs: Vec<SymbolType>,
    dot_pos: usize,
    lookahead: SymbolType,
}

impl<SymbolType> Display for LRItem<SymbolType>
where
    SymbolType: Symbol + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ->", self.lhs)?;
        for (i, symbol) in self.rhs.iter().enumerate() {
            write!(f, " ")?;
            if i == self.dot_pos {
                write!(f, ".")?;
            }
            write!(f, "{}", symbol)?;
        }
        if self.dot_pos == self.rhs.len() {
            write!(f, ".")?;
        }
        write!(f, "    {}", self.lookahead)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LRState<SymbolType>
where
    SymbolType: Symbol + PartialEq + Eq + Hash,
{
    items: HashSet<LRItem<SymbolType>>,
    is_accept: bool,
}

impl<SymbolType> Display for LRState<SymbolType>
where
    SymbolType: Symbol + Display + Hash + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for item in self.items.iter() {
            write!(f, "{}\n", item)?;
        }
        write!(f, "")
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct LREdge<SymbolType> {
    src: usize,
    dst: usize,
    symbol: SymbolType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct GrammarRule<SymbolType> {
    lhs: SymbolType,
    rhs: Vec<SymbolType>,
}

impl<SymbolType> Display for GrammarRule<SymbolType>
where
    SymbolType: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ->", self.lhs)?;
        for symbol in &self.rhs {
            write!(f, " {}", symbol)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
enum ParseAction<SymbolType> {
    Shift(usize), // shift a symbol and go to the indicated state
    Goto(usize),  // go to the indicated state
    Reduce(GrammarRule<SymbolType>),
    Accept,
    #[default]
    None,
}

impl<SymbolType> Display for ParseAction<SymbolType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseAction::Shift(state) => write!(f, "s{}", state),
            ParseAction::Goto(state) => write!(f, "g{}", state),
            ParseAction::Reduce(_rule) => write!(f, "r"),
            ParseAction::Accept => write!(f, "a"),
            ParseAction::None => write!(f, ""),
        }
    }
}

pub struct Parser<TokenType, SymbolType>
where
    SymbolType: Symbol + Eq + Hash,
    TokenType: Token,
{
    lexer: Lexer<TokenType>,
    grammar_rules: GrammarRules<SymbolType>,
    start_symbol: SymbolType,
    main_symbol: SymbolType,
    end_symbol: SymbolType,

    // Data for LL parsing
    nullable_symbols: HashSet<Vec<SymbolType>>,
    first_sets: HashMap<Vec<SymbolType>, HashSet<SymbolType>>,
    follow_sets: HashMap<SymbolType, HashSet<SymbolType>>,

    // DFA for LR parsing
    lr_states: Vec<LRState<SymbolType>>,
    lr_edges: Vec<LREdge<SymbolType>>,

    parsing_table: Vec<HashMap<SymbolType, ParseAction<SymbolType>>>,
}

impl<TokenType, SymbolType> Parser<TokenType, SymbolType>
where
    TokenType: Token<SymbolType = SymbolType>,
    SymbolType: Symbol + Eq + PartialEq + Hash + Copy + Debug + Display,
{
    /// Builds a complete LR(1) parser for the given grammar.
    ///
    /// - `lexing_rules` is used to build an internal [`Lexer`](super::Lexer).
    /// - `grammar_rules` describes the grammar, the easiest way to write these rules is by using
    /// the [`gen_grammar_rules`](gen_grammar_rules) macro. The special starting rule `S' -> S$`
    /// MUST NOT be included in the given rules (it will be added by the parser building
    /// algorithm).
    /// - `start_symbol` is the `S'` in the special rule `S' -> S$`, it MUST NOT appear in any
    /// given rule.
    /// - `main_symbol` is the `S` in the special rule `S' -> S$`, it CAN appear in any given rule
    /// (left-hand-side or right-hand-side).
    /// - `end_symbol` is the `$` in the special rule `S' -> S$`, it MUST NOT appear in any given
    /// rule.
    pub fn new(
        lexing_rules: Vec<LexerRule<TokenType>>,
        grammar_rules: GrammarRules<SymbolType>,
        start_symbol: SymbolType,
        main_symbol: SymbolType,
        end_symbol: SymbolType,
    ) -> Result<Self, String> {
        let mut new_parser = Parser {
            lexer: Lexer::new(lexing_rules),
            grammar_rules,
            start_symbol,
            main_symbol,
            end_symbol,

            nullable_symbols: HashSet::new(),
            first_sets: HashMap::new(),
            follow_sets: HashMap::new(),

            lr_states: Vec::new(),
            lr_edges: Vec::new(),

            parsing_table: Vec::new(),
        };

        if end_symbol.is_non_terminal() {
            return Err("The end symbol must be terminal".into());
        }

        new_parser.populate_grammar_sets();
        new_parser.build_dfa();
        new_parser.build_parsing_table()?;

        Ok(new_parser)
    }

    /// Get the FIRST set of the given symbol list from the pre-computed map (self.first_sets) or
    /// compute it on the fly if it wasn't pre-computed.
    fn get_or_build_first_set(&self, symbols: &Vec<SymbolType>) -> HashSet<SymbolType> {
        if let Some(pre_computed) = self.first_sets.get(symbols) {
            return pre_computed.clone();
        }

        let mut first = HashSet::new();
        for symbol in symbols {
            let dummy_sequence = vec![symbol.clone()];
            first.extend(self.first_sets.get(&dummy_sequence).expect("ICE"));
            if !self.nullable_symbols.contains(&dummy_sequence) {
                break;
            }
        }

        first
    }

    /// Compute the "closure" of an LR(1) DFA state in the sense of Appel's book, page 59-60
    fn lr_closure(&self, mut old_state: LRState<SymbolType>) -> LRState<SymbolType> {
        // comments starting with //* are pseudo code from the book.
        // I is old_state

        //* repeat […] until I does not change
        let mut something_changed = true;
        while something_changed {
            something_changed = false;
            let mut new_state = old_state.clone();

            //* for any item (A -> α.Xβ, z) in I
            for item in old_state.items {
                // Check if the item is of the form S' -> S.$, which makes this state an acept
                // state.
                if item.lhs == self.start_symbol && item.rhs[item.dot_pos] == self.end_symbol {
                    new_state.is_accept = true;
                }

                //* for any production X -> γ
                for (rhs, lhs) in &self.grammar_rules {
                    if Some(lhs) == item.rhs.get(item.dot_pos) {
                        // compute βz
                        let beta_z: Vec<SymbolType> =
                            // β
                            item.rhs[item.dot_pos + 1..]
                            .iter()
                            // z
                            .chain(&[item.lookahead])
                            .map(|s| *s)
                            .collect();

                        // compute FIRST(βz)
                        let possible_lookaheads = self.get_or_build_first_set(&beta_z);

                        //* for any ω in FIRST(βz)
                        for lookahead in possible_lookaheads.iter() {
                            something_changed = new_state.items.insert(LRItem {
                                lhs: *lhs,
                                rhs: rhs.clone(),
                                dot_pos: 0,
                                lookahead: lookahead.clone(),
                            }) || something_changed;
                        }
                    }
                }
            }

            old_state = new_state;
        }

        //* return I
        old_state
    }

    /// Compute the "goto" of an LR(1) DFA state for a given symbol in the sense of Appel's book,
    /// page 59-60
    fn lr_goto(&self, old_state: &LRState<SymbolType>, symbol: SymbolType) -> LRState<SymbolType> {
        // comments starting with //* are pseudo code from the book
        // I is old_state
        // X is symbol

        //* J <- {}
        let mut new_state = LRState {
            items: HashSet::new(),
            is_accept: false,
        };

        //* for any item (A -> α.Xβ, z) in I
        for item in &old_state.items {
            if item.rhs.get(item.dot_pos) == Some(&symbol) {
                //* add (A -> αX.β, z) to J
                new_state.items.insert(LRItem {
                    dot_pos: item.dot_pos + 1,
                    ..item.clone()
                });
            }
        }

        //* return Closure(I)
        self.lr_closure(new_state)
    }

    /// Compute the states and edges of the LR(1) DFA
    fn build_dfa(&mut self) {
        let mut current_states = vec![self.lr_closure(LRState {
            items: HashSet::from([LRItem {
                // S' -> S$
                lhs: self.start_symbol,
                rhs: vec![self.main_symbol, self.end_symbol],
                dot_pos: 0,
                lookahead: self.end_symbol, // non-important
            }]),
            is_accept: false,
        })];
        let mut current_edges: Vec<LREdge<SymbolType>> = Vec::new();

        let mut something_changed = true;
        while something_changed {
            something_changed = false;
            let mut working_states = current_states.clone();
            let mut working_edges = current_edges.clone();

            for state in &mut current_states {
                for item in &state.items {
                    if item.dot_pos < item.rhs.len() {
                        let next_symbol = item.rhs[item.dot_pos];
                        if next_symbol == self.end_symbol {
                            state.is_accept = true;
                            continue;
                        }

                        let new_state = self.lr_goto(state, next_symbol);
                        if !working_states.contains(&new_state) {
                            something_changed = true;
                            working_states.push(new_state.clone());
                        }

                        let new_edge = LREdge {
                            src: working_states.iter().position(|s| s == state).expect("ICE"),
                            dst: working_states
                                .iter()
                                .position(|s| s == &new_state)
                                .expect("ICE"),
                            symbol: next_symbol,
                        };
                        if !working_edges.contains(&new_edge) {
                            something_changed = true;
                            working_edges.push(new_edge);
                        }
                    }
                }
            }

            current_states = working_states;
            current_edges = working_edges;
        }

        self.lr_states = current_states;
        self.lr_edges = current_edges;
    }

    /// Build a dot representation of the parser's DFA
    fn dfa_to_dot(&self) -> String {
        let mut dot_representation = String::new();
        dot_representation += "digraph {";

        // represent states
        for (i, state) in self.lr_states.iter().enumerate() {
            dot_representation += "\tnode [shape=record];\n";
            dot_representation += &format!("\t\"state{}\" [label=\"{{", i);
            for item in state.items.iter() {
                dot_representation += &(item.to_string().replace(">", "\\>") + "|");
            }
            if Some('|') == dot_representation.chars().last() {
                dot_representation.remove(dot_representation.len() - 1);
            }
            dot_representation += &format!("}}\" xlabel=\"{}\"];\n", i);
            if state.is_accept {
                dot_representation += &format!("\tend{} [shape=none label=\"\"];\n", i);
                dot_representation += &format!("\tstate{} -> end{}\n", i, i);
            }
        }

        dot_representation += "\n";

        // represent edges
        for edge in self.lr_edges.iter() {
            dot_representation += &format!(
                "\tstate{} -> state{} [label=\"{}\"]\n",
                edge.src, edge.dst, edge.symbol
            );
        }

        dot_representation += "}";

        return dot_representation;
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
        self.parsing_table = vec![HashMap::new(); self.lr_states.len()];

        for (i, state) in self.lr_states.iter().enumerate() {
            for item in &state.items {
                let (transition, action) =
                    if state.is_accept && item.rhs[item.dot_pos] == self.end_symbol {
                        (item.lookahead, ParseAction::Accept)
                    } else if item.dot_pos == item.rhs.len() {
                        (
                            item.lookahead,
                            ParseAction::Reduce(GrammarRule {
                                lhs: item.lhs,
                                rhs: item.rhs.clone(),
                            }),
                        )
                    } else {
                        let destination_state = self
                            .lr_edges
                            .iter()
                            .find(|edge| {
                                edge.src == i
                                    && item.dot_pos < item.rhs.len()
                                    && edge.symbol == item.rhs[item.dot_pos]
                            })
                            .ok_or_else(|| {
                                format!(
                                    "ICE: could not find an edge from state {} with symbol {:?}.",
                                    i, item.rhs[item.dot_pos]
                                )
                            })?
                            .dst;
                        if item.rhs[item.dot_pos].is_terminal() {
                            (
                                item.rhs[item.dot_pos],
                                ParseAction::Shift(destination_state),
                            )
                        } else {
                            (item.rhs[item.dot_pos], ParseAction::Goto(destination_state))
                        }
                    };

                // Add the action to the parsing table
                if action == ParseAction::None {
                    continue;
                }

                // for error reporting
                let mut wanted_to_insert: Option<ParseAction<SymbolType>> = None;
                let mut conflicting_present_action: Option<ParseAction<SymbolType>> = None;

                let new_action = self.parsing_table[i]
                    .entry(transition)
                    .and_modify(|existing_action| {
                        if *existing_action != action {
                            // Save the conflicting actions for later reporting and use
                            // ParseAction::None to signal that there has been a conflict.
                            wanted_to_insert = Some(action.clone());
                            conflicting_present_action = Some(existing_action.clone());
                            *existing_action = ParseAction::None
                        }
                    })
                    .or_insert(action);

                if *new_action == ParseAction::None {
                    // TODO: find a way to build the string only when entering the if
                    return Err(
                        format!(
                            "Ambiguous grammar: duplicate parsing table entry for state {} and lookahead '{}': existing action was {} but we tried to insert: {}",
                            i,
                            transition,
                            conflicting_present_action.unwrap_or(ParseAction::None),
                            wanted_to_insert.unwrap_or(ParseAction::None),
                        )
                    );
                }
            }
        }

        Ok(())
    }

    /// Build a text representation of the parser's parsing table
    fn parsing_table_to_string(&self) -> String {
        let mut text_representation = String::new();
        let mut rules: Vec<GrammarRule<SymbolType>> = Vec::new();

        text_representation += "    ";
        for symbol in SymbolType::possible_symbols()
            .filter(SymbolType::is_terminal)
            .chain(std::iter::once(self.start_symbol)) // XXX: hack to mark the terminal/non-terminal separation
            .chain(
                SymbolType::possible_symbols()
                    .filter(|sym| *sym != self.start_symbol && SymbolType::is_non_terminal(sym)),
            )
        {
            if symbol == self.start_symbol {
                text_representation += " "
            } else {
                text_representation += &format!(" {:^3} ", format!("{}", symbol))
            };
        }

        // horizontal header delimitor
        text_representation += &format!(
            "\n{:-<1$}\n",
            "   ",
            SymbolType::possible_symbols().count() * 5
        );

        for (i, state) in self.parsing_table.iter().enumerate() {
            text_representation += &format!("{:>2} |", i);
            for symbol in
                SymbolType::possible_symbols()
                    .filter(SymbolType::is_terminal)
                    .chain(std::iter::once(self.start_symbol)) // XXX: hack to mark the terminal/non-terminal separation
                    .chain(SymbolType::possible_symbols().filter(|sym| {
                        *sym != self.start_symbol && SymbolType::is_non_terminal(sym)
                    }))
            {
                let action = state.get(&symbol).unwrap_or(&ParseAction::None);
                if symbol == self.start_symbol {
                    text_representation += "|";
                } else if let ParseAction::Reduce(rule) = action {
                    let rule_index = rules.iter().position(|r| r == rule).unwrap_or_else(|| {
                        rules.push(rule.clone());
                        rules.len() - 1
                    });
                    text_representation += &format!(" r{:^2} ", rule_index);
                } else {
                    text_representation += &format!(" {:^3} ", format!("{}", action));
                }
            }
            text_representation += "\n";
        }
        text_representation += "Rule list:\n";
        for (i, rule) in rules.iter().enumerate() {
            text_representation += &format!("{:>2}: {}\n", i, rule);
        }

        text_representation
    }

    /// Parse the input string and return a boolean indicating if it is syntactically correct.
    ///
    /// The current algorithm is LL(1) (predictive parsing)
    pub fn parse(&self, input: &str) -> Result<bool, String> {
        let mut token_stream = self.lexer.scan(input).peekable();
        let mut parse_stack = Vec::<(usize, SymbolType)>::new();
        let mut current_state = 0usize;

        while let Some(token) = token_stream.peek() {
            let symbol = token.symbol();
            match self.parsing_table[current_state]
                .get(&symbol.to_default())
                .unwrap_or(&ParseAction::None)
            {
                ParseAction::Accept => return Ok(true),
                ParseAction::Shift(state) => {
                    // Push the token to the stack and go to the table-indicated state
                    parse_stack.push((
                        *state,
                        *token_stream
                            .next()
                            .ok_or("ICE: peeked a token but cannot advance the iterator")?
                            .symbol(),
                    ));
                    current_state = *state;
                }
                ParseAction::Reduce(rule) => {
                    // Pop enough tokens from the stack to reconstitute the grammar rule number
                    // `rule` (checking we indeed have the correct token variants in the correct
                    // order).
                    // To find the next state, first go back to the state we were in before we
                    // pushed the first token from the rule we reduced, then use the "Goto" action
                    // for that state and reduced symbol to find the next current state.
                    for expected_symbol in rule.rhs.iter().rev() {
                        if let Some((_state, top_symbol)) = parse_stack.pop() {
                            if top_symbol.to_default() != *expected_symbol {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                    let return_state = parse_stack
                        .last()
                        .map(|(state, _symbol)| *state)
                        // if the parse stack is empty, go back to the initial state (0)
                        .unwrap_or(0usize);

                    if let ParseAction::Goto(goto_state) =
                        &self.parsing_table[return_state][&rule.lhs]
                    {
                        current_state = *goto_state;
                        parse_stack.push((current_state, rule.lhs));
                    } else {
                        return Err("ICE: no goto action after we reduce a rule".to_string());
                    }
                }
                ParseAction::Goto(_) | ParseAction::None => {
                    return Ok(false);
                }
            }
        }

        // We consumed every token of the input, including a special "end of input" token that
        // should have triggered either an `Accept` action after a `Reduce`, or a parse error. We
        // should not reach this code.
        Err("ICE: reached the end of the input without triggering an Accept action or a parsing error".to_string())
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

        // Special symbols
        ParseStart,
        ParseEnd, // usually denoted '$' in grammar rules
    }

    impl Symbol for G311Symbol {
        type ValueIterator = G311SymbolIter;
        fn is_terminal(&self) -> bool {
            use G311Symbol::*;
            !matches!(*self, Stm | StmList | Expr | ParseStart)
        }

        fn is_ignored(&self) -> bool {
            self == &G311Symbol::WhiteSpace
        }

        fn possible_symbols() -> G311SymbolIter {
            Self::iter()
        }

        fn to_default(&self) -> Self {
            match self {
                Self::Num(_) => Self::Num(Default::default()),
                _ => *self,
            }
        }
    }

    impl Display for G311Symbol {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            use G311Symbol::*;
            match self {
                Begin => write!(f, "begin"),
                Else => write!(f, "else"),
                End => write!(f, "end"),
                EqualSign => write!(f, "="),
                If => write!(f, "if"),
                Num(_) => write!(f, "num"),
                Print => write!(f, "print"),
                Semicolon => write!(f, ";"),
                Then => write!(f, "then"),
                WhiteSpace => write!(f, " "),
                Stm => write!(f, "S"),
                StmList => write!(f, "L"),
                Expr => write!(f, "E"),
                ParseStart => write!(f, "S'"),
                ParseEnd => write!(f, "$"),
            }
        }
    }

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
        type SymbolType = G311Symbol;

        fn is_ignored(&self) -> bool {
            self.symbol.is_ignored()
        }

        fn symbol(&self) -> &Self::SymbolType {
            &self.symbol
        }

        fn build_end_of_input_token(location: Location) -> Self {
            G311Token {
                symbol: G311Symbol::ParseEnd,
                location,
            }
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
    // this test only checks that the parser builds successfully, accepts a few valid input and
    // rejects a few invalid ones.
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

        let parser = Parser::new(
            G311_LEXING_RULES.to_owned(),
            grammar_rules,
            G311Symbol::ParseStart,
            G311Symbol::Stm,
            G311Symbol::ParseEnd,
        )
        .unwrap();
        println!("{}", parser.dfa_to_dot());
        println!("{}", parser.parsing_table_to_string());

        assert!(
            parser.parse("begin if 2 = 2 then print 1 = 1 else print 0 = 1; print 42 = 1337 end")
                == Ok(true)
        );

        // use `print` with a `Num` instead of a full `Expr`
        assert!(
            parser.parse("begin if 2 = 2 then print 1 else print 0; print 42 end") == Ok(false)
        );
        // trailing token after the main Stm
        assert!(
            parser.parse(
                "begin if 2 = 2 then print 1 = 1 else print 0 = 1; print 42 = 1337 end begin end"
            ) == Ok(false)
        );
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

        // Special symbols
        ParseStart,
        ParseEnd,
    }

    impl Symbol for G312Symbol {
        type ValueIterator = G312SymbolIter;
        fn is_terminal(&self) -> bool {
            use G312Symbol::*;
            matches!(*self, D | C | A | ParseEnd)
        }

        fn is_ignored(&self) -> bool {
            false
        }

        fn possible_symbols() -> G312SymbolIter {
            Self::iter()
        }

        fn to_default(&self) -> Self {
            *self
        }
    }

    impl Display for G312Symbol {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            use G312Symbol::*;
            match self {
                D => write!(f, "d"),
                C => write!(f, "c"),
                A => write!(f, "a"),
                Z => write!(f, "z"),
                Y => write!(f, "y"),
                X => write!(f, "x"),
                ParseStart => write!(f, "S'"),
                ParseEnd => write!(f, "$"),
            }
        }
    }

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
        type SymbolType = G312Symbol;

        fn is_ignored(&self) -> bool {
            false
        }

        fn symbol(&self) -> &Self::SymbolType {
            &self.symbol
        }

        fn build_end_of_input_token(location: Location) -> Self {
            G312Token {
                symbol: G312Symbol::ParseEnd,
                location,
            }
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
    // Ambiguous grammar (multiple shift-reduce conflicts)
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

        let parser = Parser::new(
            G312_LEXING_RULES.to_owned(),
            grammar_rules.clone(),
            G312Symbol::ParseStart,
            G312Symbol::Z,
            G312Symbol::ParseEnd,
        );
        if let Err(error_message) = parser {
            assert!(error_message.starts_with("Ambiguous grammar"));
        } else {
            panic!("Parser building was expected to fail on a shift-reduce conflict but was successful")
        }
    }

    // Parsing the grammar 3.20 in Andrew Appel's book (page 57)
    // WIP
    #[derive(Debug, PartialEq, Hash, Eq, EnumIter, Clone, Copy)]
    enum G320Symbol {
        // Terminal symbols
        LParen,
        RParen,
        X,
        Comma,

        // Non-terminal symbols
        S,
        L,

        // Special symbols
        ParseStart,
        ParseEnd,
    }

    impl Symbol for G320Symbol {
        type ValueIterator = G320SymbolIter;
        fn is_terminal(&self) -> bool {
            use G320Symbol::*;
            !matches!(*self, S | L | ParseStart)
        }

        fn is_ignored(&self) -> bool {
            false
        }

        fn possible_symbols() -> G320SymbolIter {
            Self::iter()
        }

        fn to_default(&self) -> Self {
            *self
        }
    }

    impl Display for G320Symbol {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            use G320Symbol::*;
            match self {
                LParen => write!(f, "("),
                RParen => write!(f, ")"),
                X => write!(f, "x"),
                Comma => write!(f, ","),
                S => write!(f, "S"),
                L => write!(f, "L"),
                ParseStart => write!(f, "S'"),
                ParseEnd => write!(f, "$"),
            }
        }
    }

    struct G320Token {
        symbol: G320Symbol,
        location: Location,
    }

    impl G320Token {
        pub fn new(symbol: G320Symbol, location: Location) -> Self {
            assert!(
                symbol.is_terminal(),
                "cannot create a token with non-terminal symbol {:?}",
                symbol
            );
            G320Token { symbol, location }
        }
    }

    impl Token for G320Token {
        type SymbolType = G320Symbol;

        fn is_ignored(&self) -> bool {
            false
        }

        fn symbol(&self) -> &Self::SymbolType {
            &self.symbol
        }

        fn build_end_of_input_token(location: Location) -> Self {
            G320Token {
                symbol: G320Symbol::ParseEnd,
                location,
            }
        }
    }

    const G320_LEXING_RULES: &[LexerRule<G320Token>] = {
        use G320Symbol::*;
        &[
            (r"^x", |loc, _| G320Token::new(X, loc)),
            (r"^\(", |loc, _| G320Token::new(LParen, loc)),
            (r"^\)", |loc, _| G320Token::new(RParen, loc)),
            (r"^,", |loc, _| G320Token::new(Comma, loc)),
        ]
    };

    #[test]
    // this test only checks that the parser builds successfully
    fn parse_g320_grammar() {
        let grammar_rules: GrammarRules<G320Symbol> = {
            use G320Symbol::*;
            gen_grammar_rules!(
                S -> LParen L RParen,
                S -> X,
                L -> S,
                L -> L Comma S,
            )
        };

        let parser = Parser::new(
            G320_LEXING_RULES.to_owned(),
            grammar_rules,
            G320Symbol::ParseStart,
            G320Symbol::S,
            G320Symbol::ParseEnd,
        )
        .unwrap();
        println!("{}", parser.dfa_to_dot());
        println!("{}", parser.parsing_table_to_string());

        // Correct inputs
        assert!(parser.parse("x") == Ok(true));
        assert!(parser.parse("(x)") == Ok(true));
        assert!(parser.parse("(x,x)") == Ok(true));
        assert!(parser.parse("(x,x,x,x,x)") == Ok(true));
        assert!(parser.parse("(x,((x,(x)),x),x)") == Ok(true));

        // Invalid inputs
        assert!(parser.parse("x,x") == Ok(false));
        assert!(parser.parse("((x,((x") == Ok(false));
    }

    // Parsing the grammar 3.26 in Andrew Appel's book (page 65)
    // WIP
    #[derive(Debug, PartialEq, Hash, Eq, EnumIter, Clone, Copy)]
    enum G326Symbol {
        // Terminal symbols
        Equal,
        X,
        Star,

        // Non-terminal symbols
        S,
        V,
        E,

        // Special symbols
        ParseStart,
        ParseEnd,
    }

    impl Symbol for G326Symbol {
        type ValueIterator = G326SymbolIter;
        fn is_terminal(&self) -> bool {
            use G326Symbol::*;
            matches!(*self, Equal | X | Star | ParseEnd)
        }

        fn is_ignored(&self) -> bool {
            false
        }

        fn possible_symbols() -> G326SymbolIter {
            Self::iter()
        }

        fn to_default(&self) -> Self {
            *self
        }
    }

    impl Display for G326Symbol {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            use G326Symbol::*;
            match self {
                Equal => write!(f, "="),
                X => write!(f, "x"),
                Star => write!(f, "*"),
                S => write!(f, "S"),
                V => write!(f, "V"),
                E => write!(f, "E"),
                ParseStart => write!(f, "S'"),
                ParseEnd => write!(f, "$"),
            }
        }
    }

    struct G326Token {
        symbol: G326Symbol,
        location: Location,
    }

    impl G326Token {
        pub fn new(symbol: G326Symbol, location: Location) -> Self {
            assert!(
                symbol.is_terminal(),
                "cannot create a token with non-terminal symbol {:?}",
                symbol
            );
            G326Token { symbol, location }
        }
    }

    impl Token for G326Token {
        type SymbolType = G326Symbol;

        fn is_ignored(&self) -> bool {
            false
        }

        fn symbol(&self) -> &Self::SymbolType {
            &self.symbol
        }

        fn build_end_of_input_token(location: Location) -> Self {
            G326Token {
                symbol: G326Symbol::ParseEnd,
                location,
            }
        }
    }

    const G326_LEXING_RULES: &[LexerRule<G326Token>] = {
        use G326Symbol::*;
        &[
            (r"^x", |loc, _| G326Token::new(X, loc)),
            (r"^=", |loc, _| G326Token::new(Equal, loc)),
            (r"^\*", |loc, _| G326Token::new(Star, loc)),
        ]
    };

    #[test]
    // this test only checks that the parser builds successfully
    // rejects some inputs
    fn parse_g326_grammar() {
        let grammar_rules: GrammarRules<G326Symbol> = {
            use G326Symbol::*;
            gen_grammar_rules!(
                S -> V Equal E,
                S -> E,
                E -> V,
                V -> X,
                V -> Star E,
            )
        };

        let parser = Parser::new(
            G326_LEXING_RULES.to_owned(),
            grammar_rules,
            G326Symbol::ParseStart,
            G326Symbol::S,
            G326Symbol::ParseEnd,
        )
        .unwrap();
        println!("{}", parser.dfa_to_dot());
        println!("{}", parser.parsing_table_to_string());
        assert!(parser.parse("x=x") == Ok(true));
        assert!(parser.parse("x=*x") == Ok(true));
        assert!(parser.parse("x=*****x") == Ok(true));
        assert!(parser.parse("*x=x") == Ok(true));
        assert!(parser.parse("*x=*x") == Ok(true));
        assert!(parser.parse("***x=x") == Ok(true));
        assert!(parser.parse("x*=x") == Ok(false));
    }
}
