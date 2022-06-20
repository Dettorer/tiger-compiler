use std::io;

use tc::parser::lexer::TokenStream;

fn main() {
    let lexer = TokenStream::new(io::stdin().lock());
    println!("There are {} tokens in the input", lexer.into_iter().count());
}
