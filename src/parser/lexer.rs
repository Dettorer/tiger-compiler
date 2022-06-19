use std::io::BufRead;

pub struct TokenIterator<R: BufRead> {
    input: R,
}

pub enum Token {}

impl<R: BufRead> TokenIterator<R> {
    pub fn new(input: R) -> Self {
        TokenIterator { input }
    }
}

impl<R: BufRead> Iterator for TokenIterator<R> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::{self, BufReader};

    #[test]
    fn empty() {
        let lexer = TokenIterator::new("".as_bytes());
        assert_eq!(lexer.count(), 0);
    }

    fn token_count_in_example(file_name: &str) -> io::Result<usize> {
        let path = format!("tests/tiger_examples/{}", file_name);
        let reader = BufReader::new(File::open(path)?);
        let it = TokenIterator::new(reader);
        Ok(it.count())
    }

    fn check_token_count(file_name: &str, expected: usize) {
        assert_eq!(
            token_count_in_example(file_name).unwrap(),
            expected,
            "expected {} tokens in the example file {}",
            expected,
            file_name
        );
    }

    #[test]
    fn test_token_count() {
        check_token_count("test1.tig", 21);
        check_token_count("test2.tig", 25);
        check_token_count("test3.tig", 37);
        check_token_count("test4.tig", 32);
        check_token_count("test5.tig", 55);
        check_token_count("test6.tig", 41);
    }
}
