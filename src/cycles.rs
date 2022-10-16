use std::{
    borrow::Borrow,
    fmt::{self, Write},
};

use crate::point::Point;

#[derive(Default)]
pub struct Cycles<Pt: Point> {
    points: Vec<Pt>,
    ends: Vec<usize>,
}

impl<Pt: Point> Cycles<Pt> {
    #[inline]
    pub fn push(&mut self, cycle: impl IntoIterator<Item = impl Borrow<Pt>>) {
        let last_end = self.points.len();
        self.points.extend(cycle.into_iter().map(|x| *x.borrow()));
        let new_end = self.points.len();
        if last_end + 1 >= new_end {
            self.points.truncate(last_end);
        } else {
            self.ends.push(self.points.len());
        }
    }

    #[inline]
    pub fn iter(&self) -> Iter<Pt> {
        Iter {
            points: &self.points,
            offset: 0,
            ends: &self.ends,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.ends.len(), Some(self.ends.len()))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.ends.len()
    }
}

impl<'a, Pt: Point> DoubleEndedIterator for Iter<'a, Pt> {
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
    fn len(&self) -> usize {
        self.ends.len()
    }
}

impl<Pt: Point> fmt::Debug for Cycles<Pt> {
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
    use super::*;

    #[test]
    fn push_iter_display() {
        let mut c = Cycles::<u32>::default();

        c.push([0, 1, 2]);
        c.push(&[10, 11, 12]);

        c.push([3, 5, 4]);
        c.push([6]);
        c.push(&[]);
        c.push([13, 15, 14]);

        let mut it = c.iter();

        assert_eq!(it.next(), Some([0, 1, 2].as_slice()));
        assert_eq!(it.next(), Some([10, 11, 12].as_slice()));
        assert_eq!(it.next(), Some([3, 5, 4].as_slice()));
        assert_eq!(it.next(), Some([13, 15, 14].as_slice()));
        assert_eq!(it.next(), None);

        assert_eq!(c.to_string(), "(0 1 2)(10 11 12)(3 5 4)(13 15 14)");
    }
}
