//! A proof-of-concept parser for grammar 3.11 in Andrew Appel's book (page 45)
//! WIP
use tc::{
    gen_grammar,
    parser::{self, Grammar, Location},
};

/// Terminal grammar symbols
#[derive(Debug, PartialEq, Hash, Eq)]
enum G311TokenVariant {
    Begin,
    Else,
    End,
    EqualSign,
    If,
    Num,
    Print,
    Semicolon,
    Then,
    WhiteSpace,
}

#[derive(Debug)]
struct G311Token {
    variant: G311TokenVariant,
    location: Location,
    parameter: Option<i32>,
}

impl G311Token {
    pub fn new(variant: G311TokenVariant, location: Location, parameter: Option<i32>) -> Self {
        G311Token {
            variant,
            location,
            parameter,
        }
    }
}

impl parser::Token for G311Token {
    fn is_ignored(&self) -> bool {
        self.variant == G311TokenVariant::WhiteSpace
    }
}

const G311_LEXING_RULES: &[parser::LexerRule<G311Token>] =
    {
        use G311TokenVariant::*;
        &[
            (r"^begin", |loc, _| G311Token::new(Begin, loc, None)),
            (r"^else", |loc, _| G311Token::new(Else, loc, None)),
            (r"^end", |loc, _| G311Token::new(End, loc, None)),
            (r"^=", |loc, _| G311Token::new(EqualSign, loc, None)),
            (r"^if", |loc, _| G311Token::new(If, loc, None)),
            (r"^\d+", |loc, matched_text| {
                G311Token::new(
                    Num,
                    loc,
                    Some(matched_text.parse().unwrap_or_else(|err| {
                        panic!("invalid integer literal at {}: {}", loc, err)
                    })),
                )
            }),
            (r"^print", |loc, _| G311Token::new(Print, loc, None)),
            (r"^;", |loc, _| G311Token::new(Semicolon, loc, None)),
            (r"^then", |loc, _| G311Token::new(Then, loc, None)),
            (r"^\s+", |loc, _| G311Token::new(WhiteSpace, loc, None)),
        ]
    };

/// Non-terminal grammar symbols
#[derive(Debug, Hash, PartialEq, Eq)]
enum G311NonTerminal {
    Stm,
    StmList,
    Expr,
}

#[derive(Debug, Hash, PartialEq, Eq)]
enum G311Symbol {
    /// Terminal symbol
    T(G311TokenVariant),
    /// Non-terminal symbol
    NT(G311NonTerminal),
}

impl From<G311NonTerminal> for G311Symbol {
    fn from(sym: G311NonTerminal) -> Self {
        G311Symbol::NT(sym)
    }
}

impl From<G311TokenVariant> for G311Symbol {
    fn from(sym: G311TokenVariant) -> Self {
        G311Symbol::T(sym)
    }
}

#[test]
fn parse_ll1_grammar() {
    let lexer = parser::Lexer::new(G311_LEXING_RULES.to_owned());
    let input = "begin if 2 = 2 then print 1 else print 0; print 42 end".to_owned();
    for token in lexer.scan(&input) {
        println!("{:?}", token);
    }

    use G311NonTerminal::*;
    use G311TokenVariant::*;
    let grammar: Grammar<G311Symbol, G311NonTerminal> = gen_grammar!(
        Stm -> If Expr Then Stm Else Stm,
        Stm -> Begin Stm StmList,
        Stm -> Print Expr,
        StmList -> End,
        StmList -> Semicolon Stm StmList,
        Expr -> Num EqualSign Num,
    );

    dbg!(grammar);
}
