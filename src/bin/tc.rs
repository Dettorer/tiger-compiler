use std::io::{self, Read};

use tc::parser::Lexer;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    let lexer = Lexer::new(&input);
    for token in lexer {
        println!("{:?}", token);
    }

    Ok(())
}
