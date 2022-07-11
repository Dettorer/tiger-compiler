use std::io::{self, Read};

use tc::parsing::build_tiger_lexer;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    let lexer = build_tiger_lexer();
    for token in lexer.scan(&input) {
        println!("{:?}", token);
    }

    Ok(())
}
