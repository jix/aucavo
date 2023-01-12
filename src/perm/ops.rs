//! Operations on permutations.
//!
//! To allow operations returning permutations without unnecessary copies or allocations, most
//! operations return a value of an operation-specific type that implements [`PermVal`].
//!
//! This module contains such operation-specific types returned by [`Perm`]'s methods.

use std::{marker::PhantomData, mem::MaybeUninit};

use rand_core::RngCore;

use crate::{point::Point, rand::Sample};

use super::{raw, Perm, PermVal};

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
        // SAFETY: target has requested degree, passed perm is a valid perm
        unsafe { raw::write_inverse(target, self.0.images()) };
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
        // SAFETY: target has requested degree, passed perms are valid and target has the same
        // degree as the max degree among left and right (computed above in `new`)
        unsafe {
            raw::write_product_extend_smaller(target, self.left.images(), self.right.images())
        };
    }
}

/// A random permutation.
///
/// See [`Sample::next_perm`][`crate::rand::Sample::next_perm`].
pub struct Random<'a, Pt: Point, R: RngCore + ?Sized> {
    degree: usize,
    rng: &'a mut R,
    _marker: PhantomData<Pt>,
}

impl<'a, Pt: Point, R: RngCore + ?Sized> Random<'a, Pt, R> {
    pub(crate) fn new(degree: usize, rng: &'a mut R) -> Self {
        assert!(degree <= Pt::MAX_DEGREE);
        Self {
            degree,
            rng,
            _marker: PhantomData,
        }
    }
}

// SAFETY: `write_to_uninitialized_unchecked` initializes a `target` of len `degree` fully with a
// valid permutation
unsafe impl<'a, Pt: Point, R: RngCore> PermVal for Random<'a, Pt, R> {
    type Pt = Pt;

    fn degree(&self) -> usize {
        self.degree
    }

    unsafe fn write_to_uninitialized_unchecked(self, target: &mut [MaybeUninit<Self::Pt>]) {
        let target = raw::write_identity(target);

        // Fisher-Yates shuffle
        let base = target.as_mut_ptr();
        for i in 0..self.degree {
            // FUTURE: use swap_unchecked when available on stable
            // SAFETY: both points are in range
            unsafe {
                std::ptr::swap(
                    base.add(self.degree - i - 1),
                    base.add(self.rng.next_index(self.degree - i)),
                )
            };
        }
    }
}
