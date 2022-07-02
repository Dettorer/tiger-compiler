/// A position in a character stream.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct TextPoint {
    /// The vertical position of the point (starting at 1)
    pub line: usize,
    /// The horizontal position of the point (starting at 1)
    pub column: usize,
    /// The index in the character stream (starting at 0)
    pub index: usize,
}

impl std::fmt::Display for TextPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// A text region defined by a start point and an end point.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Location {
    pub start: TextPoint,
    pub end: TextPoint,
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}->{}", self.start, self.end)
    }
}
