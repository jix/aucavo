//! Operations on permutations.
//!
//! To allow operations returning permutations without unnecessary copies or allocations, most
//! operations return a value of an operation-specific type that implements [`PermVal`]. Such
//! values can be assigned in-place to values of types implementing [`StorePerm`] via the
//! [`Inplace`] trait.
//!
//! This module contains such operation-specific types returned by [`Perm`]'s methods. While
//! they can be constructed directly using `T::new(...)`, calling the corresponding method of
//! [`Perm`] is usually the more ergonomic choice.
use super::*;

/// Inverse of a permutation.
///
/// See [`Perm::inv`].
pub struct Inv<'a, Pt: Point>(&'a Perm<Pt>);

impl<'a, Pt: Point> Inv<'a, Pt> {
    /// Returns the inverse of a permutation.
    ///
    /// See [`Perm::inv`].
    #[inline]
    pub fn new(perm: &'a Perm<Pt>) -> Self {
        Self(perm)
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice. Here we depend on `Perm` being a valid permutation to
// ensure we overwrite every entry.
unsafe impl<Pt: Point> PermVal<Pt> for Inv<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.0.degree()
    }

    #[inline]
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<Pt>]) {
        for (i, j) in self.0.as_slice().iter().enumerate() {
            output[j.index()] = MaybeUninit::new(Pt::from_index(i));
        }
    }
}

/// Product of two permutations.
///
/// See [`Perm::prod`].
pub struct Prod<'a, Pt: Point> {
    degree: usize,
    left: &'a Perm<Pt>,
    right: &'a Perm<Pt>,
}

impl<'a, Pt: Point> Prod<'a, Pt> {
    /// Returns the product of two permutations.
    ///
    /// See [`Perm::prod`].
    #[inline]
    pub fn new(left: &'a Perm<Pt>, right: &'a Perm<Pt>) -> Self {
        Prod {
            degree: left.degree().max(right.degree()),
            left,
            right,
        }
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for Prod<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.degree
    }

    #[inline]
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<Pt>]) {
        // TODO optimized implementations
        for (index, p) in output.iter_mut().enumerate() {
            *p = MaybeUninit::new(self.right.image(self.left.image_of_index(index)));
        }
    }
}
