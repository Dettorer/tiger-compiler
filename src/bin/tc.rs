use std::io;

use tiger_compiler::parser::lexer::TokenIterator;

fn main() {
    let lexer = TokenIterator::new(io::stdin().lock());
    println!("There are {} tokens in the input", lexer.count());
}
