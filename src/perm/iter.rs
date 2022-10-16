use super::Perm;
use crate::point::Point;

pub struct Iter<'a, Pt: Point> {
    offset: usize,
    inner: &'a [Pt],
}

impl<'a, Pt: Point> Iter<'a, Pt> {
    #[inline]
    pub(super) fn new(inner: &'a Perm<Pt>) -> Self {
        Self {
            offset: 0,
            inner: inner.as_slice(),
        }
    }

    /// Returns an iterator yielding only the moved points.
    pub fn moved(self) -> IterMoved<'a, Pt> {
        IterMoved { inner: self }
    }

    #[inline]
    pub(crate) fn skip(&mut self, n: usize) {
        if let Some(rest) = self.inner.get(n..) {
            self.inner = rest;
            self.offset += n;
        } else {
            self.inner = &[];
        }
    }

    #[inline]
    pub(crate) fn skip_back(&mut self, n: usize) {
        if let Some(rest) = self.inner.get(..self.inner.len().wrapping_sub(n)) {
            self.inner = rest;
        } else {
            self.inner = &[];
        }
    }
}

impl<'a, Pt: Point> Iterator for Iter<'a, Pt> {
    type Item = (Pt, Pt);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((&first, rest)) = self.inner.split_first() {
            self.inner = rest;
            let pt = Pt::from_index(self.offset);
            self.offset += 1;
            Some((pt, first))
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.len(), Some(self.inner.len()))
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.inner.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.skip(n);
        self.next()
    }
}

impl<'a, Pt: Point> DoubleEndedIterator for Iter<'a, Pt> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some((&last, rest)) = self.inner.split_last() {
            self.inner = rest;
            let pt = Pt::from_index(self.offset + rest.len());
            Some((pt, last))
        } else {
            None
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.skip_back(n);
        self.next_back()
    }
}

impl<'a, Pt: Point> ExactSizeIterator for Iter<'a, Pt> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

pub struct IterMoved<'a, Pt: Point> {
    inner: Iter<'a, Pt>,
}

impl<'a, Pt: Point> Iterator for IterMoved<'a, Pt> {
    type Item = (Pt, Pt);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (a, b) = self.inner.next()?;
            if a != b {
                return Some((a, b));
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.inner.len()))
    }
}

impl<'a, Pt: Point> DoubleEndedIterator for IterMoved<'a, Pt> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let (a, b) = self.inner.next_back()?;
            if a != b {
                return Some((a, b));
            }
        }
    }
}
