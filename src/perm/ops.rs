//! Operations on permutations.
//!
//! To allow operations returning permutations without unnecessary copies or allocations, most
//! operations return a value of an operation-specific type that implements [`PermVal`].
//!
//! This module contains such operation-specific types returned by [`Perm`]'s methods.

use std::mem::MaybeUninit;

use crate::point::Point;

use super::{Perm, PermVal};

/// Inverse of a permutation.
///
/// See [`Perm::inv`].
pub struct Inverse<'a, Pt: Point>(&'a Perm<[Pt]>);

impl<'a, Pt: Point> Inverse<'a, Pt> {
    pub(super) fn new(perm: &'a Perm<[Pt]>) -> Self {
        Self(perm)
    }
}

// SAFETY: `write_to_uninitialized_unchecked` initializes a `target` of len `degree` fully with a
// valid permutation
unsafe impl<'a, Pt: Point> PermVal for Inverse<'a, Pt> {
    type Pt = Pt;

    #[inline(always)]
    fn degree(&self) -> usize {
        self.0.degree()
    }

    #[inline]
    unsafe fn write_to_uninitialized_unchecked(self, target: &mut [MaybeUninit<Self::Pt>]) {
        let images = self.0.images();

        for (index, image) in images.iter().enumerate() {
            // SAFETY: writes distinct images for every point, access in range for valid
            // permutations.
            unsafe {
                target
                    .get_unchecked_mut(image.index())
                    .write(Pt::from_index(index));
            }
        }
    }
}

/// Product of two permutations.
///
/// See [`Perm::prod`].
pub struct Product<'a, Pt: Point> {
    degree: usize,
    left: &'a Perm<[Pt]>,
    right: &'a Perm<[Pt]>,
}

impl<'a, Pt: Point> Product<'a, Pt> {
    pub(super) fn new(left: &'a Perm<[Pt]>, right: &'a Perm<[Pt]>) -> Self {
        Self {
            degree: left.degree().max(right.degree()),
            left,
            right,
        }
    }
}

// SAFETY: `write_to_uninitialized_unchecked` initializes a `target` of len `degree` fully with a
// valid permutation
unsafe impl<'a, Pt: Point> PermVal for Product<'a, Pt> {
    type Pt = Pt;

    #[inline(always)]
    fn degree(&self) -> usize {
        self.degree
    }

    #[inline]
    unsafe fn write_to_uninitialized_unchecked(self, target: &mut [MaybeUninit<Self::Pt>]) {
        // TODO replace with better implementation
        for index in 0..self.degree {
            // SAFETY: writes distinct images for every point, caller has to provide `target` with
            // len `self.degree`
            unsafe {
                target
                    .get_unchecked_mut(index)
                    .write(self.right.image(self.left.image_of_index(index)));
            }
        }
    }
}
