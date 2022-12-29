//! Products of cycles (cyclic permutations).
use std::{
    borrow::Borrow,
    convert::Infallible,
    fmt::{self, Write},
    marker::PhantomData,
    mem::{replace, MaybeUninit},
};

use smallvec::SmallVec;

use crate::{
    inplace::{Inplace, InplaceWithTemp},
    perm::{Perm, PermVal},
    point::Point,
};

/// A permutation represented as product of cycles (cyclic permutations).
///
/// The cycle permutations are applied left-to-right (the default in Aucavo).
///
/// A cycle decomposition of a permutation can be obtained from [`Perm::cycles`].
///
/// This type does not prevent adding improper cycles that have repeated points. The permutation
/// this represents is undefined and different methods may interpret such improper cycles
/// differently but must interpret it as some valid permutation.
#[derive(Default)]
pub struct Cycles<Pt: Point> {
    points: Vec<Pt>,
    ends: Vec<usize>,
    degree: usize,
}

impl<Pt: Point> Cycles<Pt> {
    /// Multiplies a cycle on the right.
    #[inline]
    pub fn push_cycle(&mut self, cycle: impl IntoIterator<Item = impl Borrow<Pt>>) {
        let last_end = self.points.len();
        self.points.extend(cycle.into_iter().map(|x| *x.borrow()));
        for pt in &self.points[last_end..] {
            self.degree = self.degree.max(pt.index() + 1);
        }
        let new_end = self.points.len();
        if last_end != new_end {
            self.ends.push(new_end);
        }
    }

    #[inline]
    fn push_to_last_cycle(&mut self, point: Pt) {
        self.degree = self.degree.max(point.index() + 1);
        self.points.push(point);
        if let Some(end) = self.ends.last_mut() {
            *end += 1;
        }
    }

    /// Multiplies a cycle-decomposition of a permutation on the right, using provided temporary
    /// storage.
    ///
    /// The provided temporary storage must be initialized to all `false` and be of sufficient size.
    fn push_decomposition(&mut self, perm: &Perm<Pt>, seen: &mut [bool]) {
        for (a, mut b) in perm.iter() {
            if a == b || seen[a.index()] {
                continue;
            }
            seen[a.index()] = true;

            let mut next = Some(a);

            self.push_cycle(std::iter::from_fn(|| {
                let current = next?;
                if b == a {
                    next = None;
                } else {
                    seen[b.index()] = true;
                    next = Some(b);
                    b = perm.image(b);
                }
                Some(current)
            }));
        }
    }

    /// The provided temporary storage must be initialized to all `false` and be of sufficient size.
    fn is_decomposition(&self, seen: &mut [bool]) -> bool {
        !self
            .points
            .iter()
            .any(|&pt| replace(&mut seen[pt.index()], true))
    }

    /// Returns an iterator over the cycles.
    #[inline]
    pub fn iter(&self) -> Iter<Pt> {
        Iter {
            points: &self.points,
            offset: 0,
            ends: &self.ends,
        }
    }

    /// Returns the number of cycles.
    #[inline]
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    /// Returns whether no cycles are present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// Resets this value to an empty product.
    #[inline]
    pub fn clear(&mut self) {
        self.points.clear();
        self.ends.clear();
        self.degree = 0;
    }

    /// Inverts all cycles in place.
    ///
    /// When the cycles are disjoint, this is equivalent to inverting the product.
    pub fn invert_cycles(&mut self) {
        let mut start = 0;
        for &end in &self.ends {
            self.points[start + 1..end].reverse();
            start = end;
        }
    }

    /// Parses a product of cycles.
    ///
    /// Accepts the same syntax as produced by `Cycles` [`fmt::Display`] implementation.
    // TODO document the syntax
    #[inline]
    pub fn parse(s: &(impl AsRef<[u8]> + ?Sized)) -> Parse<Pt> {
        Parse {
            bytes: s.as_ref(),
            check: false,
            _phantom: PhantomData,
        }
    }

    /// Parses a cycle decomposition.
    ///
    /// Same as [`parse`][`Self::parse`], but additionally checks that the parsed cycles are proper
    /// cycles without duplicated points and that the cycles are disjoint.
    #[inline]
    pub fn parse_decomposition(s: &(impl AsRef<[u8]> + ?Sized)) -> Parse<Pt> {
        Parse {
            bytes: s.as_ref(),
            check: true,
            _phantom: PhantomData,
        }
    }
}

impl<'a, Pt: Point> IntoIterator for &'a Cycles<Pt> {
    type Item = &'a [Pt];

    type IntoIter = Iter<'a, Pt>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// [`Inplace`] operation implementing [`Cycles::parse`] and [`Cycles::parse_decomposition`].
pub struct Parse<'a, Pt: Point> {
    bytes: &'a [u8],
    check: bool,
    _phantom: PhantomData<Pt>,
}

/// Error type for [`Cycles::parse`] and [`Cycles::parse_decomposition`].
#[derive(Debug)]
pub struct ParseError {
    kind: ParseErrorKind,
}

#[derive(Debug)]
enum ParseErrorKind {
    UnexpectedCharacter,
    InvalidPoint,
    RepeatedPoint,
}

impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ParseErrorKind::UnexpectedCharacter => write!(f, "unexpected character in permutation"),
            ParseErrorKind::InvalidPoint => {
                write!(f, "unsupported point index")
            }
            ParseErrorKind::RepeatedPoint => {
                write!(f, "cycles are not disjoint or have repeated points")
            }
        }
    }
}

impl<Pt: Point> Inplace<Cycles<Pt>, ()> for Parse<'_, Pt> {
    type Err = ParseError;

    #[inline]
    fn try_build(self) -> Result<Cycles<Pt>, Self::Err>
    where
        Cycles<Pt>: Sized,
    {
        self.try_build_with_temp(&mut Default::default())
    }

    #[inline]
    fn try_assign_to(self, output: &mut Cycles<Pt>) -> Result<(), Self::Err> {
        self.try_assign_to_with_temp(output, &mut Default::default())
    }
}

impl<Pt: Point> InplaceWithTemp<Cycles<Pt>, ()> for Parse<'_, Pt> {
    type Temp = SmallVec<[bool; 256]>; // TUNE

    #[inline]
    fn try_build_with_temp(self, temp: &mut Self::Temp) -> Result<Cycles<Pt>, Self::Err>
    where
        Cycles<Pt>: Sized,
    {
        let mut cycles = Cycles::default();
        self.try_assign_to_with_temp(&mut cycles, temp)?;
        Ok(cycles)
    }

    fn try_assign_to_with_temp(
        self,
        output: &mut Cycles<Pt>,
        temp: &mut Self::Temp,
    ) -> Result<(), Self::Err> {
        output.clear();

        let mut pending = self.bytes;

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

        fn parse_point<Pt: Point>(bytes: &[u8]) -> Result<(Pt, &[u8]), ParseError> {
            let (num, rest) = split_ascii_digits(bytes);

            if num.is_empty() {
                return Err(ParseError {
                    kind: ParseErrorKind::UnexpectedCharacter,
                });
            }

            let num = Pt::from_str(num).map_err(|_| ParseError {
                kind: ParseErrorKind::InvalidPoint,
            })?;

            if num.index() >= Pt::MAX_DEGREE {
                return Err(ParseError {
                    kind: ParseErrorKind::InvalidPoint,
                });
            }

            Ok((num, skip_ascii_whitespace(rest)))
        }

        pending = skip_ascii_whitespace(pending);

        'cycles: while let Some((b'(', rest)) = pending.split_first() {
            pending = skip_ascii_whitespace(rest);

            if let Some((b')', rest)) = pending.split_first() {
                pending = skip_ascii_whitespace(rest);
                continue;
            }

            let (point, rest) = parse_point::<Pt>(pending)?;
            pending = rest;
            output.push_cycle([point]);

            loop {
                if let Some((b')', rest)) = pending.split_first() {
                    pending = skip_ascii_whitespace(rest);
                    continue 'cycles;
                }

                let (point, rest) = parse_point::<Pt>(pending)?;
                pending = rest;
                output.push_to_last_cycle(point);
            }
        }

        if !pending.is_empty() {
            return Err(ParseError {
                kind: ParseErrorKind::UnexpectedCharacter,
            });
        }

        if self.check {
            temp.clear();
            temp.resize(output.degree, false);

            if !output.is_decomposition(temp.as_mut_slice()) {
                return Err(ParseError {
                    kind: ParseErrorKind::RepeatedPoint,
                });
            }
        }

        Ok(())
    }
}

/// Cycle decomposition of a permutation.
///
/// See [`Perm::cycles`] and [`Cycles`].
pub struct CycleDecomposition<'a, Pt: Point>(&'a Perm<Pt>);

impl<'a, Pt: Point> CycleDecomposition<'a, Pt> {
    /// Returns the cycle decomposition of a permutation.
    ///
    /// See [`Perm::cycles`] and [`Cycles`].
    #[inline]
    pub fn new(perm: &'a Perm<Pt>) -> Self {
        Self(perm)
    }
}

impl<Pt: Point> Inplace<Cycles<Pt>, ()> for CycleDecomposition<'_, Pt> {
    type Err = Infallible;

    #[inline]
    fn try_build(self) -> Result<Cycles<Pt>, Self::Err>
    where
        Cycles<Pt>: Sized,
    {
        let mut cycles = Cycles::default();
        self.assign_to(&mut cycles);
        Ok(cycles)
    }

    #[inline]
    fn try_assign_to(self, output: &mut Cycles<Pt>) -> Result<(), Self::Err> {
        self.try_assign_to_with_temp(output, &mut Default::default())
    }
}

impl<Pt: Point> InplaceWithTemp<Cycles<Pt>, ()> for CycleDecomposition<'_, Pt> {
    type Temp = SmallVec<[bool; 256]>; // TUNE

    #[inline]
    fn try_build_with_temp(self, temp: &mut Self::Temp) -> Result<Cycles<Pt>, Self::Err>
    where
        Cycles<Pt>: Sized,
    {
        let mut cycles = Cycles::default();
        self.assign_to_with_temp(&mut cycles, temp);
        Ok(cycles)
    }

    fn try_assign_to_with_temp(
        self,
        output: &mut Cycles<Pt>,
        temp: &mut Self::Temp,
    ) -> Result<(), Self::Err> {
        output.clear();
        output.degree = self.0.degree();
        let perm = self.0.as_min_degree();
        temp.clear();
        temp.resize(perm.degree(), false);
        output.push_decomposition(perm, temp);
        Ok(())
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for &Cycles<Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.degree
    }

    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<Pt>]) {
        // SAFETY: completely initialize with the identity permutation
        for (i, p) in output.iter_mut().enumerate() {
            *p = MaybeUninit::new(Pt::from_index(i));
        }

        // SAFETY: swapping elements to apply the cycles ensures we end up with a valid permutation
        // even for improper cycles.
        for cycle in self.iter().rev() {
            let mut points = cycle.iter();
            if let Some(mut last) = points.next() {
                for p in points {
                    output.swap(p.index(), last.index());
                    last = p;
                }
            }
        }
    }
}

/// Iterator over [`Cycles`].
pub struct Iter<'a, Pt: Point> {
    points: &'a [Pt],
    ends: &'a [usize],
    offset: usize,
}

impl<'a, Pt: Point> Iterator for Iter<'a, Pt> {
    type Item = &'a [Pt];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (&next_end, ends) = self.ends.split_first()?;
        let len = next_end - self.offset;
        self.ends = ends;
        self.offset = next_end;

        let (next_cycle, points) = self.points.split_at(len);
        self.points = points;

        Some(next_cycle)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.ends.len(), Some(self.ends.len()))
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.ends.len()
    }
}

impl<'a, Pt: Point> DoubleEndedIterator for Iter<'a, Pt> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let (_, ends) = self.ends.split_last()?;
        self.ends = ends;
        let start = ends.last().copied().unwrap_or_default();

        let (points, next_cycle) = self.points.split_at(start - self.offset);
        self.points = points;

        Some(next_cycle)
    }
}

impl<'a, Pt: Point> ExactSizeIterator for Iter<'a, Pt> {
    #[inline]
    fn len(&self) -> usize {
        self.ends.len()
    }
}

impl<Pt: Point> fmt::Debug for Cycles<Pt> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<Pt: Point> fmt::Display for Cycles<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            f.write_str("()")
        } else {
            for cycle in self {
                let mut sep = '(';
                for pt in cycle {
                    f.write_char(sep)?;
                    sep = ' ';
                    fmt::Display::fmt(pt, f)?;
                }
                f.write_char(')')?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{inplace::AssignInplace, perm::ArrayPerm};

    use super::*;

    #[test]
    #[allow(clippy::needless_borrow)]
    fn push_iter_display() {
        let mut c = Cycles::<u32>::default();

        c.push_cycle([0, 1, 2]);
        c.push_cycle(&[10, 11, 12]);

        c.push_cycle([3, 5, 4]);
        c.push_cycle([6]);
        c.push_cycle(&[]);
        c.push_cycle([13, 15, 14]);

        let mut it = c.iter();

        assert_eq!(it.next(), Some([0, 1, 2].as_slice()));
        assert_eq!(it.next(), Some([10, 11, 12].as_slice()));
        assert_eq!(it.next(), Some([3, 5, 4].as_slice()));
        assert_eq!(it.next(), Some([6].as_slice()));
        assert_eq!(it.next(), Some([13, 15, 14].as_slice()));
        assert_eq!(it.next(), None);

        assert_eq!(c.to_string(), "(0 1 2)(10 11 12)(3 5 4)(6)(13 15 14)");
    }

    #[test]
    fn roundtrip_decompose() {
        type SmallPerm = ArrayPerm<u32, 7>;
        let mut c = Cycles::<u32>::default();
        let mut temp = Default::default();
        let mut h = SmallPerm::default();
        let mut g_inv = SmallPerm::default();

        for g in SmallPerm::all() {
            c.assign(g.cycles().with_temp(&mut temp));
            for cycle in &c {
                assert!(cycle.len() >= 2);
            }
            h.assign(&c);
            assert_eq!(h.as_slice(), g.as_slice());
            c.invert_cycles();
            h.assign(&c);
            g_inv.assign(g.inv());
            assert_eq!(h.as_slice(), g_inv.as_slice());
        }
    }

    #[test]
    fn parse() {
        let input = "(0 1 2)(10 11 12)(3 5 4)(6)(13 15 14)";
        let mut cycles: Cycles<u32> = Cycles::parse(input).try_build().unwrap();
        assert_eq!(cycles.to_string(), input);

        let equivalent = " ( 0 1 2 ) ( 10  11  12 )  ( 3    5 4   )(6)(   13 15 14)   ";
        cycles.try_assign(Cycles::parse(equivalent)).unwrap();
        assert_eq!(cycles.to_string(), input);
    }

    #[test]
    fn roundtrip_decompose_parse() {
        type SmallPerm = ArrayPerm<u32, 7>;
        let mut c = Cycles::<u32>::default();
        let mut d = Cycles::<u32>::default();
        let mut temp = Default::default();
        let mut h = SmallPerm::default();

        for g in SmallPerm::all() {
            c.assign(g.cycles().with_temp(&mut temp));
            let c_str = c.to_string();
            d.try_assign(Cycles::parse_decomposition(&c_str).with_temp(&mut temp))
                .unwrap();
            h.assign(&d);
            assert_eq!(h, g);
        }
    }
}
