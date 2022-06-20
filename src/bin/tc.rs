use std::io;

use tc::parser::lexer::Lexer;

fn main() {
    let lexer = Lexer::new(io::stdin().lock());
    for token in lexer {
        println!("{:?}", token);
    }
}