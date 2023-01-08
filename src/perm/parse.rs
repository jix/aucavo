use std::{fmt, mem::take, ops};

use crate::{
    as_slice::AsMutSlice,
    point::{AsPointSlice, Point},
};

use super::Perm;

/// Error type for [`Cycles::parse`] and [`Cycles::parse_decomposition`].
#[derive(Debug)]
pub struct ParseError {
    kind: ParseErrorKind,
    bytes_left: usize,
}

impl ParseError {
    fn unexpected(bytes: &[u8]) -> Self {
        Self {
            kind: if bytes.is_empty() {
                ParseErrorKind::UnexepctedEnd
            } else {
                ParseErrorKind::UnexpectedCharacter
            },
            bytes_left: bytes.len(),
        }
    }

    /// Number of input bytes following the error position
    pub fn bytes_left(&self) -> usize {
        self.bytes_left
    }

    /// Splits the input string or byte slice at the error position
    ///
    /// This can panic with out of bounds indexing when the `input` parameter does not match the
    /// input passed to the parsing function.
    pub fn split_input_on_error<'a, T>(&self, input: &'a T) -> (&'a T, &'a T)
    where
        T: AsRef<[u8]>,
        T: ops::Index<ops::RangeTo<usize>, Output = T>,
        T: ops::Index<ops::RangeFrom<usize>, Output = T>,
    {
        let len = input.as_ref().len();
        let pos = len - self.bytes_left;
        (&input[..pos], &input[pos..])
    }
}

#[derive(Debug)]
enum ParseErrorKind {
    UnexpectedCharacter,
    UnexepctedEnd,
    TrailingData,
    InvalidPoint,
    RepeatedPoint,
}

impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ParseErrorKind::UnexpectedCharacter => write!(f, "unexpected character"),
            ParseErrorKind::UnexepctedEnd => write!(f, "unexpected end of input"),
            ParseErrorKind::TrailingData => write!(f, "unexpected trailing data"),
            ParseErrorKind::InvalidPoint => {
                write!(f, "unsupported point index")
            }
            ParseErrorKind::RepeatedPoint => {
                write!(f, "cycles are not disjoint or have repeated points")
            }
        }
    }
}

pub fn parse_into_identity<T: AsPointSlice + AsMutSlice + ?Sized>(
    target: &mut Perm<T>,
    offset: usize,
    commas: bool,
    mut pending: &[u8],
) -> Result<(), ParseError> {
    fn skip_ascii_whitespace(bytes: &[u8]) -> &[u8] {
        let mut pending = bytes;
        while let Some((&first, rest)) = pending.split_first() {
            if !first.is_ascii_whitespace() {
                break;
            }
            pending = rest;
        }
        pending
    }

    fn split_ascii_digits(bytes: &[u8]) -> (&str, &[u8]) {
        let mut pending = bytes;
        while let Some((&first, rest)) = pending.split_first() {
            if !first.is_ascii_digit() {
                break;
            }
            pending = rest;
        }

        let (digits, rest) = bytes.split_at(bytes.len() - pending.len());

        // SAFETY: we checked that digits contains only ascii digits
        unsafe { (std::str::from_utf8_unchecked(digits), rest) }
    }

    fn parse_point<'a, 'b, T: AsPointSlice + AsMutSlice + ?Sized>(
        bytes: &'a [u8],
        offset: usize,
        perm: &'b mut Perm<T>,
    ) -> Result<(T::Pt, &'a [u8]), ParseError> {
        let (point, rest) = split_ascii_digits(bytes);

        if point.is_empty() {
            return Err(ParseError::unexpected(bytes));
        }

        let index = str::parse::<usize>(point)
            .ok()
            .and_then(|index| index.checked_sub(offset))
            .filter(|&index| perm.try_extend_degree(index + 1))
            .ok_or(ParseError {
                kind: ParseErrorKind::InvalidPoint,
                bytes_left: bytes.len(),
            })?;

        Ok((
            <T::Pt as Point>::from_index(index),
            skip_ascii_whitespace(rest),
        ))
    }

    pending = skip_ascii_whitespace(pending);
    let mut empty = true;

    'cycles: while let Some((b'(', rest)) = pending.split_first() {
        pending = skip_ascii_whitespace(rest);

        if take(&mut empty) {
            if let Some((b')', rest)) = pending.split_first() {
                pending = skip_ascii_whitespace(rest);
                break;
            }
        }

        let (point, rest) = parse_point(pending, offset, target)?;
        let last_point_pending = pending;
        pending = rest;

        let degree_only = target.image(point) != point;

        let mut prev_point = point;

        loop {
            if let Some((b')', rest)) = pending.split_first() {
                pending = skip_ascii_whitespace(rest);
                continue 'cycles;
            }

            if degree_only {
                return Err(ParseError {
                    kind: ParseErrorKind::RepeatedPoint,
                    bytes_left: last_point_pending.len(),
                });
            }

            if commas {
                if let Some((b',', rest)) = pending.split_first() {
                    pending = skip_ascii_whitespace(rest);
                } else {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedCharacter,
                        bytes_left: pending.len(),
                    });
                }
            }

            let (point, rest) = parse_point(pending, offset, target)?;
            if point == prev_point || target.image(point) != point {
                return Err(ParseError {
                    kind: ParseErrorKind::RepeatedPoint,
                    bytes_left: pending.len(),
                });
            }
            pending = rest;

            // TODO use some better and safe API when added
            // SAFETY: swapping two points maintains a valid permutation
            unsafe {
                target
                    .images_dyn()
                    .as_mut_slice()
                    .swap(prev_point.index(), point.index())
            };
            prev_point = point;
        }
    }

    if empty {
        return Err(ParseError::unexpected(pending));
    }

    if !pending.is_empty() {
        return Err(ParseError {
            kind: ParseErrorKind::TrailingData,
            bytes_left: pending.len(),
        });
    }

    Ok(())
}
