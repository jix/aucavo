//! Products of cycles (cyclic permutations).
use std::{
    borrow::Borrow,
    fmt::{self, Write},
    mem::MaybeUninit,
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
        let new_end = self.points.len();
        if last_end + 1 >= new_end {
            self.points.truncate(last_end);
        } else {
            for pt in &self.points[last_end..] {
                self.degree = self.degree.max(pt.index() + 1);
            }
            self.ends.push(self.points.len());
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
}

impl<'a, Pt: Point> IntoIterator for &'a Cycles<Pt> {
    type Item = &'a [Pt];

    type IntoIter = Iter<'a, Pt>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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

impl<'a, Pt: Point> CycleDecomposition<'a, Pt> {}

impl<Pt: Point> Inplace<Cycles<Pt>, ()> for CycleDecomposition<'_, Pt> {
    #[inline]
    fn build(self) -> Cycles<Pt>
    where
        Cycles<Pt>: Sized,
    {
        let mut cycles = Cycles::default();
        self.assign_to(&mut cycles);
        cycles
    }

    #[inline]
    fn assign_to(self, output: &mut Cycles<Pt>) {
        self.assign_to_with_temp(output, &mut Default::default());
    }
}

impl<Pt: Point> InplaceWithTemp<Cycles<Pt>, ()> for CycleDecomposition<'_, Pt> {
    type Temp = SmallVec<[bool; 256]>; // TUNE

    #[inline]
    fn build_with_temp(self, temp: &mut Self::Temp) -> Cycles<Pt>
    where
        Cycles<Pt>: Sized,
    {
        let mut cycles = Cycles::default();
        self.assign_to_with_temp(&mut cycles, temp);
        cycles
    }

    fn assign_to_with_temp(self, output: &mut Cycles<Pt>, temp: &mut Self::Temp) {
        output.clear();
        output.degree = self.0.degree();
        let perm = self.0.as_min_degree();
        temp.clear();
        temp.resize(perm.degree(), false);
        output.push_decomposition(perm, temp);
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
        assert_eq!(it.next(), Some([13, 15, 14].as_slice()));
        assert_eq!(it.next(), None);

        assert_eq!(c.to_string(), "(0 1 2)(10 11 12)(3 5 4)(13 15 14)");
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
            h.assign(&c);
            assert_eq!(h.as_slice(), g.as_slice());
            c.invert_cycles();
            h.assign(&c);
            g_inv.assign(g.inv());
            assert_eq!(h.as_slice(), g_inv.as_slice());
        }
    }
}
