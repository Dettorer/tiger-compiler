#[derive(Copy, Clone, Debug)]
pub struct TextPoint {
    pub line: usize,
    pub column: usize,
}

impl std::fmt::Display for TextPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Location {
    pub start: TextPoint,
    pub end: TextPoint,
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}->{}", self.start, self.end)
    }
}
