//! Permutations.
use std::{
    mem::MaybeUninit,
    ops::{Deref, Range},
};

use smallvec::{smallvec, SmallVec};

use crate::{
    inplace::Inplace,
    point::{Point, PointIter, PointRange},
};

/// A permutation.
#[repr(transparent)]
pub struct Perm<P: Point> {
    // SAFETY: must always be a valid permutation.
    slice: [P],
}

impl<P: Point> Perm<P> {
    /// The identity permutation.
    #[inline]
    pub const fn identity() -> &'static Self {
        // SAFETY: an empty slice is a valid permutation
        unsafe { Self::from_slice_unchecked(&[]) }
    }

    /// Checks whether a slice contains permutation of `0..slice.len()`.
    ///
    /// If the length of `slice` exceeds `P::MAX_DEGREE` this also returns `false`, even when it
    /// would be a valid permutation otherwise.
    pub fn is_perm(slice: &[P]) -> bool {
        if slice.len() > P::MAX_DEGREE {
            return false;
        }
        let mut seen: SmallVec<[bool; 256]> = smallvec![false; slice.len()]; // TUNE
        for &p in slice {
            if let Some(seen_p) = seen.get_mut(p.index()) {
                if std::mem::replace(seen_p, true) {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }

    /// Creates a `Perm` reference from a slice containing the images of the first n points.
    ///
    /// Panics for non-permutation arguments.
    #[inline]
    pub fn from_slice(slice: &[P]) -> &Self {
        assert!(Self::is_perm(slice));
        // SAFETY: `Self::is_perm` above checks the exact required invariant below
        unsafe { Self::from_slice_unchecked(slice) }
    }

    /// Creates a mutable `Perm` reference from a slice containing the images of the first n points.
    ///
    /// Panics for non-permutation arguments.
    #[inline]
    pub fn from_slice_mut(slice: &mut [P]) -> &mut Self {
        assert!(Self::is_perm(slice));
        // SAFETY: `Self::is_perm` above checks the exact required invariant below
        unsafe { Self::from_slice_unchecked_mut(slice) }
    }

    /// Creates a `Perm` reference from a slice containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `slice` must be a permutation of the points `0..slice.len()`.
    #[inline]
    pub const unsafe fn from_slice_unchecked(slice: &[P]) -> &Self {
        // SAFETY: `Self` is a `repr(transparent)` wrapper for `[P]`
        unsafe { &*(slice as *const [P] as *const Self) }
    }

    /// Creates a mutable `Perm` reference from a slice containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `slice` must be a permutation of the points `0..slice.len()`.
    #[inline]
    pub unsafe fn from_slice_unchecked_mut(slice: &mut [P]) -> &mut Self {
        // SAFETY: `Self` is a `repr(transparent)` wrapper for `[P]`
        unsafe { &mut *(slice as *mut [P] as *mut Self) }
    }

    /// Returns the slice containing the images of `self.points()`.
    #[inline]
    pub fn as_slice(&self) -> &[P] {
        &self.slice
    }

    /// Returns the mutable slice containing the images of `self.points()`.
    ///
    /// # Safety
    /// A `Perm` must always be a valid permutation and users may depend on this for memory safety.
    /// The user of this method has to ensure this invariant is maintained, even in the present of
    /// panics.
    #[inline]
    pub unsafe fn as_mut_slice(&mut self) -> &mut [P] {
        &mut self.slice
    }

    /// Returns the size of the set the permutation is defined on.
    ///
    /// Unless documented otherwise, a smaller degree permutation is implicitly extended by adding
    /// fixed points when a larger degree permutation is expected.
    #[inline]
    pub fn degree(&self) -> usize {
        self.slice.len()
    }

    /// Returns the image of a point under the permutation.
    #[inline]
    pub fn image(&self, point: P) -> P {
        self.image_of_index(point.index())
    }

    /// Returns the image of the `index`-th point under the permutation.
    #[inline]
    pub fn image_of_index(&self, index: usize) -> P {
        // NOTE: This could use a safe .get() instead, but as this will be called from inner loops
        // and as in the past I had issues with `Option` causing very poor codegen, I'll use this
        // simpler to optimize unsafe version instead. When I'm confident that a current rustc/llvm
        // won't generate silly code for this in any call site this might be inlined into, I will
        // change this.
        if index < self.slice.len() {
            // SAFETY: if condition is the exact required bound check
            unsafe { *self.slice.get_unchecked(index) }
        } else {
            P::from_index(index)
        }
    }

    /// Returns the set on which the permutation is defined on.
    #[inline]
    pub fn points(&self) -> PointRange<P> {
        PointIter::new(self.indices())
    }

    /// Returns the indices of the points in the set on which the permutation is defined on.
    #[inline]
    pub fn indices(&self) -> Range<usize> {
        0..self.degree()
    }

    /// Returns the inverse of this permutation.
    #[inline]
    pub fn inv(&self) -> ops::Inv<P> {
        ops::Inv::new(self)
    }

    /// Returns the product of this permutation with another permutation.
    ///
    /// Aucavo follows the convention where applying the product of two permutations is the same as
    /// applying the _left_ permutation first, followed by the _right_ permutation. This is the same
    /// convention used by the computer algebra system GAP and it is often used in _computational_
    /// group theory literature.
    #[inline]
    pub fn prod<'a>(&'a self, other: &'a Perm<P>) -> ops::Prod<'a, P> {
        ops::Prod::new(self, other)
    }
}

/// Owned permutation backed by a [`Vec`].
///
/// Most functionality is provided via the [`Deref`] implementation to [`Perm`].
#[derive(Default)]
pub struct VecPerm<P: Point> {
    // SAFETY: must always be a valid permutation.
    vec: Vec<P>,
}

impl<P: Point> Deref for VecPerm<P> {
    type Target = Perm<P>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: `VecPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_slice_unchecked(self.vec.as_slice()) }
    }
}

impl<P: Point> VecPerm<P> {
    /// Returns a new `VecPerm` initialized to the identity permutation.
    #[inline]
    pub fn identity() -> Self {
        Self::default()
    }
}

/// Types that can store a permutation.
///
/// Implementing this trait allows storing [`PermVal`]s in the implementing type via the blanket
/// impl of [`Inplace`] that delegates to [`PermVal`].
///
/// # Safety
/// Implementers should make sure to consider the safety requirements of [`PermVal`].
pub trait StorePerm {
    /// Point representation used.
    type Point: Point;

    /// Returns a new value storing the given permutation.
    ///
    /// Not available for unsized types.
    ///
    /// Callers should use the blanket implementation of [`Inplace`] instead of calling this
    /// directly.
    fn build_from_perm_val(perm: impl PermVal<Self::Point>) -> Self
    where
        Self: Sized;

    /// Assign the given permutation to a value in-place.
    ///
    /// An implementation can chose to automatically grow its storage when assigning a permutation
    /// of a larger degree than the previously stored permutation. Alternatively it is allowed to
    /// panic. Implementations are expected to document their degree-growing behavior.
    ///
    /// Callers should use the blanket implementation of [`Inplace`] instead of calling this
    /// directly.
    fn assign_perm_val(&mut self, perm: impl PermVal<Self::Point>);

    // TODO unchecked/checked methods for assignment with matching degree?
    // TODO consts and/or subtraits indiciating the growing behavior?
}

/// Panics when assigning a permutation with a larger degree than the existing value.
impl<P: Point> StorePerm for Perm<P> {
    type Point = P;
    fn build_from_perm_val(_perm: impl PermVal<P>) -> Self
    where
        Self: Sized,
    {
        unreachable!()
    }

    #[inline]
    fn assign_perm_val(&mut self, perm: impl PermVal<P>) {
        let mut degree = perm.degree();

        // We use that `split_at_mut` panics when the degree is too large
        let (new_perm, fixed_suffix) = self.slice.split_at_mut(degree);

        // SAFETY: `PermVal` guarantees that `write_to_slice` writes a fully initialized valid
        // permutation when the passed slice has the requested size.
        unsafe {
            let new_perm: &mut [MaybeUninit<P>] =
                &mut *(new_perm as *mut [P] as *mut [MaybeUninit<P>]);
            perm.write_to_slice(new_perm);
        };

        for p in fixed_suffix {
            *p = P::from_index(degree);
            degree += 1;
        }
    }
}

/// Allocates new storage when assigning a permutation with a larger degree than the existing value.
///
/// The implementation uses `reserve_exact` to only allocate as much memory as required. While this
/// saves memory for typical uses cases involving permutations, it can cause quadratic runtime when
/// gorwing the degree of a permutation one at a time.
impl<P: Point> StorePerm for VecPerm<P> {
    type Point = P;

    #[inline]
    fn build_from_perm_val(perm: impl PermVal<P>) -> Self
    where
        Self: Sized,
    {
        let degree = perm.degree();
        let mut vec = Vec::with_capacity(degree);

        // SAFETY: `get_unchecked_mut` is in bounds as we reserved sufficient capacity, `set_len` is
        // allowed as `PermVal` guarantees that `write_to_slice` writes a fully initialized valid
        // permutation when the passed slice has the requested size.
        unsafe {
            perm.write_to_slice(vec.spare_capacity_mut().get_unchecked_mut(..degree));
            vec.set_len(degree);
        }

        Self { vec }
    }

    #[inline]
    fn assign_perm_val(&mut self, perm: impl PermVal<P>) {
        let mut degree = perm.degree();

        let new_degree = self.vec.len().max(degree);

        self.vec.clear();
        self.vec.reserve_exact(new_degree);

        // SAFETY: `get_unchecked_mut` is in bounds as we reserved sufficient capacity, `set_len` is
        // allowed as `PermVal` guarantees that `write_to_slice` writes a fully initialized valid
        // permutation when the passed slice has the requested size. In the case that `new_degree >
        // degree` the missing values are already initialized, but need to be overwritten as fixed
        // points to maintain `VecPerm`'s invariant.
        unsafe {
            let data = self.vec.spare_capacity_mut();
            perm.write_to_slice(data.get_unchecked_mut(..degree));

            for p in data.get_unchecked_mut(degree..new_degree) {
                *p = MaybeUninit::new(P::from_index(degree));
                degree += 1;
            }

            self.vec.set_len(new_degree);
        }
    }
}

impl<T: ?Sized> StorePerm for &mut T
where
    T: StorePerm,
{
    type Point = T::Point;
    fn build_from_perm_val(_perm: impl PermVal<Self::Point>) -> Self
    where
        Self: Sized,
    {
        unreachable!()
    }

    #[inline]
    fn assign_perm_val(&mut self, perm: impl PermVal<Self::Point>) {
        T::assign_perm_val(self, perm)
    }
}

/// Values representing a permutation.
///
/// Many permutation producing operations return an operation-specific type (e.g. [`ops::Inv`],
/// [`ops::Prod`]) implementing this trait. To turn such a value into a generic permutation type
/// implementing [`StorePerm`] (e.g. [`&mut Perm`][`Perm`] or [`VecPerm`]), use the [`Inplace`]
/// trait that is also implemented by such operation-specific types.
///
/// Using this trait directly is only required when implementing new low-level permutation producing
/// operations or when implementing [`StorePerm`] for a new type.
///
/// When implementing `PermVal` for a type, usually that should be accompanied by an implementation
/// of [`Inplace<O>`] for any [`O: StorePerm`][`StorePerm`].
///
/// # Safety
/// Implementations must uphold the documented safety requirements for both
/// [`degree`][`Self::degree`] as well as [`write_to_slice`][`Self::write_to_slice`], as callers do
/// rely on them for safety.
pub unsafe trait PermVal<P: Point>: Sized {
    /// Returns the size of the set the permutation is defined on.
    ///
    /// # Safety
    /// Calling this repeatedly must always return the same value. Implementations of
    /// [`write_to_slice`][`Self::write_to_slice`] may require the passed `output` slice of this
    /// length.
    fn degree(&self) -> usize;

    /// Writes a permutation to the provided slice.
    ///
    /// # Safety
    /// Callers must provide a slice having the length returned by [`degree`][`Self::degree`].
    /// Implementations may not read the existing contents of the slice and must overwrite it
    /// completely with a valid permutation.
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<P>]);
}

/// Disambiguator for the [`Inplace`] impl assigning [`PermVal`]s to [`StorePerm`]s.
pub enum InplacePerm {}

impl<O: StorePerm + ?Sized, T> Inplace<O, InplacePerm> for T
where
    T: PermVal<O::Point>,
{
    #[inline]
    fn build(self) -> O
    where
        O: Sized,
    {
        O::build_from_perm_val(self)
    }

    #[inline]
    fn assign_to(self, output: &mut O) {
        O::assign_perm_val(output, self)
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<P: Point> PermVal<P> for &Perm<P> {
    #[inline]
    fn degree(&self) -> usize {
        Perm::degree(self)
    }

    #[inline]
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<P>]) {
        let slice: &[MaybeUninit<P>] =
            // SAFETY: safe cast of &[P] to &[MaybeUninit<P>]
            // FUTURE: Use a safe alternative when available (e.g. #79995)
            unsafe { &*(self.as_slice() as *const [P] as *const [MaybeUninit<P>]) };
        output.copy_from_slice(slice);
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<P: Point> PermVal<P> for &mut Perm<P> {
    #[inline]
    fn degree(&self) -> usize {
        (self as &Perm<P>).degree()
    }

    #[inline]
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<P>]) {
        // SAFETY: forwarding to `&Perm<P>`'s implementation upholds all safety requirements on both
        // the implementation and the call site.
        unsafe { (self as &Perm<P>).write_to_slice(output) }
    }
}

pub mod ops {
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
    pub struct Inv<'a, P: Point>(&'a Perm<P>);

    impl<'a, P: Point> Inv<'a, P> {
        /// Returns the inverse of a permutation.
        ///
        /// See [`Perm::inv`].
        #[inline]
        pub fn new(perm: &'a Perm<P>) -> Self {
            Self(perm)
        }
    }

    // SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
    // passed a `degree()` length slice. Here we depend on `Perm` being a valid permutation to
    // ensure we overwrite every entry.
    unsafe impl<P: Point> PermVal<P> for Inv<'_, P> {
        #[inline]
        fn degree(&self) -> usize {
            self.0.degree()
        }

        #[inline]
        unsafe fn write_to_slice(self, output: &mut [MaybeUninit<P>]) {
            for (i, j) in self.0.as_slice().iter().enumerate() {
                output[j.index()] = MaybeUninit::new(P::from_index(i));
            }
        }
    }

    /// Product of two permutations.
    ///
    /// See [`Perm::prod`].
    pub struct Prod<'a, P: Point> {
        pub(super) degree: usize,
        pub(super) left: &'a Perm<P>,
        pub(super) right: &'a Perm<P>,
    }

    impl<'a, P: Point> Prod<'a, P> {
        /// Returns the product of two permutations.
        ///
        /// See [`Perm::prod`].
        #[inline]
        pub fn new(left: &'a Perm<P>, right: &'a Perm<P>) -> Self {
            Prod {
                degree: left.degree().max(right.degree()),
                left,
                right,
            }
        }
    }

    // SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
    // passed a `degree()` length slice.
    unsafe impl<P: Point> PermVal<P> for Prod<'_, P> {
        #[inline]
        fn degree(&self) -> usize {
            self.degree
        }

        #[inline]
        unsafe fn write_to_slice(self, output: &mut [MaybeUninit<P>]) {
            // TODO optimized implementations
            for (index, p) in output.iter_mut().enumerate() {
                *p = MaybeUninit::new(self.right.image(self.left.image_of_index(index)));
            }
        }
    }
}
