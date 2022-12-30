//! Displaying and parsing types using GAP syntax.
use std::{fmt, str::FromStr};

/// Wrapper type that uses GAP syntax to format or parse the contained type.
pub struct Gap<T>(pub T);

impl<T: FmtGap> fmt::Display for Gap<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_gap(f)
    }
}

impl<T: FmtGap> fmt::Debug for Gap<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_gap(f)
    }
}

impl<T: FromGapStr> FromStr for Gap<T> {
    type Err = T::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        T::from_gap_str(s).map(Gap)
    }
}

/// Displays a type using GAP syntax.
pub trait FmtGap {
    /// Displays a type using GAP syntax.
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

/// Parses a type using GAP syntax.
pub trait FromGapStr: Sized {
    /// Type for parse errors.
    type Err;

    /// Parses a type using GAP syntax.
    fn from_gap_str(s: &str) -> Result<Self, Self::Err>;
}

impl<T> FmtGap for &'_ T
where
    T: FmtGap,
{
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::fmt_gap(self, f)
    }
}

impl<T> FmtGap for &'_ mut T
where
    T: FmtGap,
{
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::fmt_gap(self, f)
    }
}
