//! A proof-of-concept parser for grammar 3.11 in Andrew Appel's book (page 45)
//! WIP
use strum::{EnumIter, IntoEnumIterator};

use tc::{
    gen_grammar,
    parsing::{self, Grammar, Location, Symbol},
};

#[derive(Debug, PartialEq, Hash, Eq, EnumIter)]
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

impl parsing::Symbol<G311SymbolIter> for G311Symbol {
    fn is_terminal(&self) -> bool {
        use G311Symbol::*;
        !matches!(*self, Stm | StmList | Expr)
    }

    fn possible_values() -> G311SymbolIter {
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

impl parsing::Token for G311Token {
    fn is_ignored(&self) -> bool {
        self.symbol == G311Symbol::WhiteSpace
    }
}

const G311_LEXING_RULES: &[parsing::LexerRule<G311Token>] = {
    use G311Symbol::*;
    &[
        (r"^begin", |loc, _| G311Token::new(Begin, loc)),
        (r"^else", |loc, _| G311Token::new(Else, loc)),
        (r"^end", |loc, _| G311Token::new(End, loc)),
        (r"^=", |loc, _| G311Token::new(EqualSign, loc)),
        (r"^if", |loc, _| G311Token::new(If, loc)),
        (r"^\d+", |loc, matched_text| {
            G311Token::new(
                Num(matched_text
                    .parse()
                    .unwrap_or_else(|err| panic!("invalid integer literal at {}: {}", loc, err))),
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
fn parse_ll1_grammar() {
    let lexer = parsing::Lexer::new(G311_LEXING_RULES.to_owned());
    let input = "begin if 2 = 2 then print 1 else print 0; print 42 end".to_owned();
    for token in lexer.scan(&input) {
        println!("{:?}", token);
    }

    let grammar: Grammar<G311Symbol> = {
        use G311Symbol::*;
        gen_grammar!(
            Stm -> If Expr Then Stm Else Stm,
            Stm -> Begin Stm StmList,
            Stm -> Print Expr,
            StmList -> End,
            StmList -> Semicolon Stm StmList,
            Expr -> Num(0) EqualSign Num(0),
        )
    };

    dbg!(grammar);
}
