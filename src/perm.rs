//! Permutations.

use std::{
    cmp,
    mem::MaybeUninit,
    ops::{Deref, DerefMut, Range},
    str::FromStr,
};

use crate::{
    as_slice::{
        AsMutSlice, DynSlice, NewSlice, ReserveSlice, SpecializeAsDynSlice,
        SpecializeAsReserveSlice,
    },
    point::{AsPointSlice, Point, PointIter, PointRange},
};

mod fmt;
mod parse;
mod raw;

pub mod ops;

/// Module to guard against mutation of the image slice from safe code
mod __ {
    use crate::as_slice::AsMutSlice;

    use super::*;

    /// A permutation.
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    pub struct Perm<T: AsPointSlice + ?Sized>(T);

    impl<T: AsPointSlice + ?Sized> Perm<T> {
        /// Creates a `Perm` from a value containing a slice of point images.
        ///
        /// # Safety
        /// The argument `images` must be a permutation of the points `0..images.as_slice().len()`.
        #[inline(always)]
        pub unsafe fn from_images_unchecked(images: T) -> Self
        where
            T: Sized,
        {
            Perm(images)
        }

        /// Creates a `Perm` reference from a reference to a value containing a slice of point
        /// images.
        ///
        /// # Safety
        /// The argument `images` must be a permutation of the points `0..images.as_slice().len()`.
        #[inline(always)]
        pub unsafe fn from_images_unchecked_ref(images: &T) -> &Self {
            // SAFETY: caller is required to provide a valid permutation
            unsafe { &*(images as *const T as *const Self) }
        }

        /// Creates a mutable `Perm` reference from a mutable reference to a value containing a
        /// slice of point images.
        ///
        /// # Safety
        /// The argument `images` must be a permutation of the points `0..images.as_slice().len()`.
        #[inline(always)]
        pub unsafe fn from_images_unchecked_mut(images: &mut T) -> &mut Self {
            // SAFETY: caller is required to provide a valid permutation
            unsafe { &mut *(images as *mut T as *mut Self) }
        }

        /// Returns a slice containing the images of `self.domain()`.
        #[inline(always)]
        pub fn images(&self) -> &[T::Pt] {
            self.0.as_slice()
        }

        /// Returns a mutable slice containing the images of `self.domain()`.
        ///
        /// # Safety
        /// A `Perm` must always contain a valid permutation and users may depend on this for memory
        /// safety. Callers of this method have to ensure this invariant is maintained, even in the
        /// present of panics.
        #[inline(always)]
        pub unsafe fn images_mut(&mut self) -> &mut [T::Pt]
        where
            T: AsMutSlice,
        {
            self.0.as_mut_slice()
        }

        /// Returns a `MaybeUninit` slice containing the images of `self.domain()`.
        ///
        /// # Safety
        /// A `Perm` must always contain a valid and fully initialized permutation and users may
        /// depend on this for memory safety. Callers of this method have to ensure this invariant
        /// is maintained, even in the present of panics.
        #[inline(always)]
        pub(crate) fn maybe_uninit_images(&self) -> &[MaybeUninit<T::Pt>]
        where
            T: AsMutSlice,
        {
            // SAFETY: safe cast from &[T::Pt] to &[MaybeUninit<T::Pt>]
            unsafe { &*(self.0.as_slice() as *const [T::Pt] as *const [MaybeUninit<T::Pt>]) }
        }

        /// Returns a mutable `MaybeUninit` slice containing the images of `self.domain()`.
        ///
        /// # Safety
        /// A `Perm` must always contain a valid and fully initialized permutation and users may
        /// depend on this for memory safety. Callers of this method have to ensure this invariant
        /// is maintained, even in the present of panics.
        #[inline(always)]
        pub(crate) unsafe fn maybe_uninit_images_mut(&mut self) -> &mut [MaybeUninit<T::Pt>]
        where
            T: AsMutSlice,
        {
            // SAFETY: cast from &mut [T::Pt] to &mut [MaybeUninit<T::Pt>], caller is required to
            // maintain a valid initialized permutation within the returned slice
            unsafe { &mut *(self.0.as_mut_slice() as *mut [T::Pt] as *mut [MaybeUninit<T::Pt>]) }
        }

        /// Returns a mutable reference to the value containing the images of `self.domain()`.
        ///
        /// # Safety
        /// A `Perm` must always contain a valid permutation and users may depend on this for memory
        /// safety. Callers of this method have to ensure this invariant is maintained, even in the
        /// present of panics.
        #[inline(always)]
        pub unsafe fn images_dyn(&mut self) -> &mut T {
            &mut self.0
        }
    }
}

pub use __::Perm;

impl<Pt: Point> Perm<[Pt]> {
    #[inline]
    fn image_of_index_impl(&self, index: usize) -> Pt {
        // NOTE: This could use a safe .get() instead, but as this will be called from inner loops
        // and as in the past I had issues with `Option` causing very poor codegen, I'll use this
        // simpler to optimize unsafe version instead. When I'm confident that a current rustc/llvm
        // won't generate silly code for this in any call site this might be inlined into, I will
        // change this.
        if index < self.degree() {
            // SAFETY: if condition is the exact required bound check
            unsafe { *self.images().get_unchecked(index) }
        } else {
            Pt::from_index(index)
        }
    }

    #[inline]
    fn shrink_to_degree(&self, degree: usize) -> &Perm<[Pt]> {
        let mut shrunk = self.images();
        while shrunk.len() > degree {
            if let Some((&last, rest)) = shrunk.split_last() {
                if last.index() != rest.len() {
                    break;
                }
                shrunk = rest;
            } else {
                break;
            }
        }

        // SAFETY: we only remove fixed points, so shrunk stays a permutation
        unsafe { Perm::from_images_unchecked_ref(shrunk) }
    }

    #[inline]
    fn eq_impl(&self, other: &Self) -> bool {
        let mut lhs = self;
        let mut rhs = other;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs) = Self::eq_fixup(lhs, rhs);
        }

        lhs.images() == rhs.images()
    }

    #[cold] // TUNE
    fn eq_fixup<'a>(mut lhs: &'a Self, mut rhs: &'a Self) -> (&'a Self, &'a Self) {
        if lhs.degree() > rhs.degree() {
            (lhs, rhs) = (rhs, lhs);
        }
        rhs = rhs.shrink_to_degree(lhs.degree());
        (lhs, rhs)
    }

    #[inline]
    fn cmp_impl(&self, other: &Self) -> cmp::Ordering {
        let mut lhs = self;
        let mut rhs = other;
        let mut flip = false;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs, flip) = Self::cmp_fixup(lhs, rhs);
        }

        let mut result = lhs.images().cmp(&rhs.images()[..lhs.degree()]);

        if result.is_eq() && lhs.degree() != rhs.degree() {
            result = cmp::Ordering::Less;
        }

        if flip {
            result.reverse()
        } else {
            result
        }
    }

    #[cold] // TUNE
    fn cmp_fixup<'a>(mut lhs: &'a Self, mut rhs: &'a Self) -> (&'a Self, &'a Self, bool) {
        let mut flip = false;
        if lhs.degree() > rhs.degree() {
            (lhs, rhs) = (rhs, lhs);
            flip = true;
        }
        rhs = rhs.shrink_to_degree(lhs.degree());
        (lhs, rhs, flip)
    }

    #[inline(never)]
    #[cold]
    fn cannot_extend_degree(&self, degree: usize) -> ! {
        panic!("cannot extend degree from {} to {degree}", self.degree())
    }
}

impl<T: AsPointSlice + ?Sized> Perm<T> {
    /// Creates a `Perm` from a value containing a slice of point images.
    ///
    /// Panics when `images` is not a valid permutation or when the length of `images` exceeds
    /// `T::Pt::MAX_DEGREE`.
    #[inline(always)]
    pub fn from_images(images: T) -> Option<Self>
    where
        T: Sized,
    {
        // SAFETY: `is_perm` checks the precondition for `from_images_unchecked`
        raw::is_perm(images.as_slice()).then(|| unsafe { Self::from_images_unchecked(images) })
    }

    /// Creates a `Perm` reference from a reference to a value containing a slice of point images.
    ///
    /// Panics when `images` is not a valid permutation or when the length of `images` exceeds
    /// `T::Pt::MAX_DEGREE`.
    #[inline(always)]
    pub fn from_images_ref(images: &T) -> Option<&Self>
    where
        T: Sized,
    {
        // SAFETY: `is_perm` checks the precondition for `from_images_unchecked`
        raw::is_perm(images.as_slice()).then(|| unsafe { Self::from_images_unchecked_ref(images) })
    }

    /// Creates a mutable `Perm` reference from a mutable reference to a value containing a slice of
    /// point images.
    ///
    /// Panics when `images` is not a valid permutation or when the length of `images` exceeds
    /// `T::Pt::MAX_DEGREE`.
    #[inline(always)]
    pub fn from_images_mut(images: &mut T) -> Option<&mut Self>
    where
        T: Sized,
    {
        // SAFETY: `is_perm` checks the precondition for `from_images_unchecked`
        raw::is_perm(images.as_slice()).then(|| unsafe { Self::from_images_unchecked_mut(images) })
    }

    /// Returns the size of the set the permutation acts on.
    ///
    /// A permutation acts on the set `0..self.degree()`.
    ///
    /// Unless documented otherwise, a smaller degree permutation is implicitly extended by adding
    /// fixed points when a larger degree permutation is expected.
    #[inline(always)]
    pub fn degree(&self) -> usize {
        self.images().len()
    }

    /// Returns the set the permutation acts on.
    #[inline(always)]
    fn domain(&self) -> PointRange<T::Pt> {
        PointIter::new(self.domain_indices())
    }

    /// Returns the indices of the points in the set the permutation acts on.
    ///
    /// See also [`Point::index`].
    #[inline(always)]
    fn domain_indices(&self) -> Range<usize> {
        0..self.degree()
    }

    /// Returns the image of the point with the given `index` under the permutation.
    ///
    /// Returns `T::Pt::from_index(index)` when `index` is not below the permutation's degree.
    #[inline(always)]
    pub fn image_of_index(&self, index: usize) -> T::Pt {
        Perm::image_of_index_impl(self.as_ref(), index)
    }

    /// Returns the image of a point under the permutation.
    ///
    /// When `point` is not in the permutation's domain, this returns `point`, implicitly extending
    /// the permutation with fixed points.
    #[inline(always)]
    pub fn image(&self, point: T::Pt) -> T::Pt {
        Perm::image_of_index_impl(self.as_ref(), point.index())
    }

    /// Returns the same permutation acting on a set with trailing fixed points removed.
    #[inline(always)]
    pub fn as_min_degree(&self) -> &Perm<[T::Pt]> {
        self.as_ref().shrink_to_degree(0)
    }

    /// Returns the inverse of this permutation.
    #[inline(always)]
    pub fn inv(&self) -> ops::Inverse<T::Pt> {
        ops::Inverse::new(self.as_ref())
    }

    /// Returns the product of this permutation with another permutation.
    ///
    /// Aucavo follows the convention where applying the product of two permutations is the same as
    /// applying the _left_ permutation first, followed by the _right_ permutation. This is the same
    /// convention used by the computer algebra system GAP and it is often used in _computational_
    /// group theory literature.
    #[inline(always)]
    pub fn prod<'a, R: AsPointSlice<Pt = T::Pt> + ?Sized>(
        &'a self,
        right: &'a Perm<R>,
    ) -> ops::Product<'a, T::Pt> {
        ops::Product::new(self.as_ref(), right.as_ref())
    }
}

impl<T: AsPointSlice + AsMutSlice + ?Sized> Perm<T> {
    /// Extends the degree of this permutation in-place.
    ///
    /// Panics if `degree` exceeds `Pt::MAX_DEGREE` or if `T` cannot store a permutation of the
    /// given degree.
    #[inline(always)]
    pub fn extend_degree(&mut self, degree: usize) {
        if self.degree() < degree {
            self.extend_degree_required(degree)
        }
    }

    /// Tries to extends the degree of this permutation in-place.
    ///
    /// Returns `false` if `degree` exceeds `Pt::MAX_DEGREE` or if `T` cannot store a permutation of the
    /// given degree. If the degree was successfully extended `true` is returned.
    #[inline(always)]
    #[must_use]
    pub fn try_extend_degree(&mut self, degree: usize) -> bool {
        self.degree() >= degree || self.try_extend_degree_required(degree)
    }

    #[inline(always)]
    fn extend_degree_required(&mut self, degree: usize) {
        if !self.try_extend_degree(degree) {
            self.as_ref().cannot_extend_degree(degree)
        }
    }

    #[inline(always)]
    fn try_extend_degree_required(&mut self, degree: usize) -> bool {
        struct ExtendDegree<'a, T: AsPointSlice + AsMutSlice + ?Sized> {
            target: &'a mut Perm<T>,
            degree: usize,
        }

        impl<'a, T: AsPointSlice + AsMutSlice + ?Sized> SpecializeAsDynSlice<T, bool>
            for ExtendDegree<'a, T>
        {
            #[inline(never)]
            fn base(self) -> bool {
                false
            }

            #[inline(never)]
            fn specialized(self) -> bool
            where
                T: DynSlice,
            {
                if self.degree > T::Pt::MAX_DEGREE {
                    return false;
                }

                let prev_degree = self.target.degree();
                // SAFETY: `post` initializes the new elements with an identitiy mapping leaving a
                // fully initialized valid permutation
                unsafe {
                    self.target.images_dyn().resize_with(
                        self.degree,
                        |_| (),
                        |slice| {
                            raw::write_identity_padding(slice, prev_degree);
                        },
                    )
                }

                true
            }
        }

        T::specialize_as_dyn_slice(ExtendDegree {
            target: self,
            degree,
        })
    }

    #[inline(always)]
    fn assign_perm_val_default<V: PermVal<Pt = T::Pt>>(&mut self, perm: V) {
        struct AssignPermVal<'a, T: AsPointSlice + AsMutSlice + ?Sized, V: PermVal<Pt = T::Pt>> {
            target: &'a mut Perm<T>,
            perm: V,
        }

        impl<'a, T: AsPointSlice + AsMutSlice + ?Sized, V: PermVal<Pt = T::Pt>>
            SpecializeAsDynSlice<T, ()> for AssignPermVal<'a, T, V>
        {
            #[inline]
            fn base(self) {
                let target = self.target.as_mut();
                let target_degree = target.degree();
                let perm_degree = self.perm.degree();
                if target_degree < perm_degree {
                    target.cannot_extend_degree(perm_degree);
                }

                // SAFETY: `write_to_uninitialized_unchecked` and `write_identity_padding` fully
                // overwrite the returned slice with a valid permutation,
                // `write_to_uninitialized_unchecked` gets passed a slice of the requested len
                // `perm_degree`.
                unsafe {
                    self.perm
                        .write_to_uninitialized_unchecked(raw::write_identity_padding(
                            target.maybe_uninit_images_mut(),
                            perm_degree,
                        ))
                };
            }

            #[inline(always)]
            fn specialized(self)
            where
                T: DynSlice,
            {
                T::specialize_as_reserve_slice(self)
            }
        }

        impl<'a, T: AsPointSlice + DynSlice + ?Sized, V: PermVal<Pt = T::Pt>>
            SpecializeAsReserveSlice<T, ()> for AssignPermVal<'a, T, V>
        {
            #[inline]
            fn base(self) {
                let target_degree = self.target.degree();
                let perm_degree = self.perm.degree();

                // SAFETY: `write_to_uninitialized_unchecked` and `write_identity_padding` fully
                // initialize the slice with a valid permutation
                // `write_to_uninitialized_unchecked` gets passed a slice of the requested len
                // `perm_degree`.
                unsafe {
                    self.target
                        .images_dyn()
                        .replace_with(perm_degree.max(target_degree), |slice| {
                            self.perm
                                .write_to_uninitialized_unchecked(raw::write_identity_padding(
                                    slice,
                                    perm_degree,
                                ))
                        })
                };
            }

            #[inline]
            fn specialized(self)
            where
                T: ReserveSlice,
            {
                // SAFETY: `write_to_uninitialized_unchecked`  fully
                // initializes the slice with a valid permutation
                // `write_to_uninitialized_unchecked` gets passed a slice of the requested len
                // `self.perm.degree()`.
                unsafe {
                    self.target
                        .images_dyn()
                        .replace_with(self.perm.degree(), |slice| {
                            self.perm.write_to_uninitialized_unchecked(slice)
                        })
                };
            }
        }

        T::specialize_as_dyn_slice(AssignPermVal { target: self, perm })
    }

    /// Sets this permutation to a given value.
    ///
    /// See [`PermVal::assign_to`] for more details.
    #[inline(always)]
    pub fn assign<V: PermVal<Pt = T::Pt>>(&mut self, value: V) {
        value.assign_to(self)
    }
}

impl<T: AsPointSlice + NewSlice> Perm<T> {
    /// Returns a new permutation of a given value
    ///
    /// See [`PermVal::into_perm`] for more details.
    #[inline(always)]
    pub fn new<V: PermVal<Pt = T::Pt>>(perm: V) -> Self {
        perm.into_perm()
    }

    /// Returns the identity permutation.
    ///
    /// This returns a degree-0 permutation.
    #[inline(always)]
    pub fn identity() -> Self {
        // SAFETY: the emtpy slice is a valid degree-0 permutation
        unsafe { Self::from_images_unchecked(T::new_empty()) }
    }
}

impl<T: AsPointSlice + AsMutSlice + NewSlice> FromStr for Perm<T> {
    type Err = parse::ParseError;

    #[inline(always)]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut new = Self::identity();
        parse::parse_into_identity(&mut new, 0, false, s.as_bytes())?;
        Ok(new)
    }
}

impl<T: AsPointSlice + NewSlice> Default for Perm<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::identity()
    }
}

impl<T: AsPointSlice + ?Sized> AsRef<Perm<[T::Pt]>> for Perm<T> {
    #[inline(always)]
    fn as_ref(&self) -> &Perm<[T::Pt]> {
        // SAFETY: `images` returns a valid permutation
        unsafe { Perm::from_images_unchecked_ref(self.images()) }
    }
}

impl<T: AsPointSlice + AsMutSlice + ?Sized> AsMut<Perm<[T::Pt]>> for Perm<T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut Perm<[T::Pt]> {
        // SAFETY: `images` returns a valid permutation
        unsafe { Perm::from_images_unchecked_mut(self.images_mut()) }
    }
}

impl<T: AsPointSlice> Deref for Perm<T> {
    type Target = Perm<[T::Pt]>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<T: AsPointSlice + AsMutSlice> DerefMut for Perm<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

impl<T: AsPointSlice + ?Sized, U: AsPointSlice<Pt = T::Pt> + ?Sized> PartialEq<Perm<U>>
    for Perm<T>
{
    #[inline(always)]
    fn eq(&self, other: &Perm<U>) -> bool {
        self.as_ref().eq_impl(other.as_ref())
    }
}

impl<T: AsPointSlice + ?Sized, U: AsPointSlice<Pt = T::Pt> + ?Sized> PartialEq<Perm<U>>
    for &Perm<T>
{
    #[inline(always)]
    fn eq(&self, other: &Perm<U>) -> bool {
        self.as_ref().eq_impl(other.as_ref())
    }
}

impl<T: AsPointSlice + ?Sized, U: AsPointSlice<Pt = T::Pt> + ?Sized> PartialEq<&Perm<U>>
    for Perm<T>
{
    #[inline(always)]
    fn eq(&self, other: &&Perm<U>) -> bool {
        self.as_ref().eq_impl(other.as_ref())
    }
}

impl<T: AsPointSlice + ?Sized> Eq for Perm<T> {}

impl<T: AsPointSlice + ?Sized, U: AsPointSlice<Pt = T::Pt> + ?Sized> PartialOrd<Perm<U>>
    for Perm<T>
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Perm<U>) -> Option<cmp::Ordering> {
        Some(self.as_ref().cmp_impl(other.as_ref()))
    }
}

impl<T: AsPointSlice + ?Sized, U: AsPointSlice<Pt = T::Pt> + ?Sized> PartialOrd<Perm<U>>
    for &Perm<T>
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Perm<U>) -> Option<cmp::Ordering> {
        Some(self.as_ref().cmp_impl(other.as_ref()))
    }
}

impl<T: AsPointSlice + ?Sized, U: AsPointSlice<Pt = T::Pt> + ?Sized> PartialOrd<&Perm<U>>
    for Perm<T>
{
    #[inline(always)]
    fn partial_cmp(&self, other: &&Perm<U>) -> Option<cmp::Ordering> {
        Some(self.as_ref().cmp_impl(other.as_ref()))
    }
}

impl<T: AsPointSlice + ?Sized> Ord for Perm<T> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ref().cmp_impl(other.as_ref())
    }
}

/// Values representing a permutation.
///
/// Many permutation producing operations return an operation-specific type (e.g. [`ops::Inverse`],
/// [`ops::Product`]) implementing this trait.
///
/// Use [`into_perm`][`Self::into_perm`] or [`Perm::new`] to obtain a the resulting permutation as a
/// new value. Alternatively use [`assign_to`][`Self::assign_to`] or [`Perm::assign`] to assign the
/// permutation to an existing value.
///
/// # Safety
/// Implementations must uphold the documented safety requirements for both
/// [`degree`][`Self::degree`] as well as
/// [`write_to_uninitialized_unchecked`][`Self::write_to_uninitialized_unchecked`], as callers do
/// rely on them for safety.
pub unsafe trait PermVal: Sized {
    /// Type of points the permutation acts on.
    type Pt: Point;

    /// The degree of the represented permutation.
    ///
    /// This is always a valid degree for which `self.degree() <= Self::Pt::MAX_DEGREE` holds.
    fn degree(&self) -> usize;

    /// Writes the permutation into an uninitialized image slice of the correct length.
    ///
    /// # Safety
    /// The `target` slice must have a length matching the value previously returned by
    /// `Self::degree` and implementations may assume this without checking. Implementations have to
    /// fully initialize `target` with a valid permutation.
    unsafe fn write_to_uninitialized_unchecked(self, target: &mut [MaybeUninit<Self::Pt>]);

    /// Sets the given permutation to this value.
    ///
    /// This tries to extend the degree of the target value as required. If the target value cannot
    /// store a permutation of the required degree, this panics. When `target`'s degree can be
    /// reduced without reallocation (e.g. when target is a `Perm<Vec<_>>`) the target degree is set
    /// to exactly the degree of this value. Otherwise `target`'s degree is set to the maximum of
    /// the degree it had before calling this and the degree of this value
    #[inline(always)]
    fn assign_to<T: AsPointSlice<Pt = Self::Pt> + AsMutSlice + ?Sized>(self, target: &mut Perm<T>) {
        target.assign_perm_val_default(self)
    }

    /// Returns this value as a new permutation.
    #[inline(always)]
    fn into_perm<T: AsPointSlice<Pt = Self::Pt> + NewSlice>(self) -> Perm<T> {
        // SAFETY: a) `new_with` provides `write_to_uninitialized_unchecked` with a slice of the
        // requested length `degree`, then `write_to_uninitialized_unchecked` initializes it fully
        // with a valid permutation as required by `new_with` and `from_images_unchecked`
        //
        unsafe {
            Perm::from_images_unchecked(T::new_with(self.degree(), |slice| {
                self.write_to_uninitialized_unchecked(slice)
            }))
        }
    }
}

// SAFETY: `write_to_uninitialized_unchecked` initializes a `target` of len `degree` fully with a
// valid permutation
unsafe impl<'a, T: AsPointSlice + ?Sized> PermVal for &'a Perm<T> {
    type Pt = T::Pt;

    #[inline(always)]
    fn degree(&self) -> usize {
        Perm::degree(self)
    }

    #[inline(always)]
    unsafe fn write_to_uninitialized_unchecked(self, target: &mut [MaybeUninit<Self::Pt>]) {
        target.copy_from_slice(self.as_ref().maybe_uninit_images())
    }
}

// SAFETY: `write_to_uninitialized_unchecked` initializes a `target` of len `degree` fully with a
// valid permutation
unsafe impl<T: AsPointSlice> PermVal for Perm<T> {
    type Pt = T::Pt;

    #[inline(always)]
    fn degree(&self) -> usize {
        Perm::degree(self)
    }

    #[inline(always)]
    unsafe fn write_to_uninitialized_unchecked(self, target: &mut [MaybeUninit<Self::Pt>]) {
        target.copy_from_slice(self.as_ref().maybe_uninit_images())
    }
}
