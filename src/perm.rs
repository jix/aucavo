//! Permutations.
use std::{borrow::Borrow, cmp, convert::Infallible, fmt, hash, mem::MaybeUninit, ops::Range};

use smallvec::{smallvec, SmallVec};

use crate::{
    cycles::CycleDecomposition,
    gap,
    inplace::Inplace,
    point::{Point, PointIter, PointRange},
};

use self::iter::Iter;

pub mod iter;
pub mod ops;
pub mod raw;

mod array_perm;
mod small_perm;
mod vec_perm;

pub use array_perm::ArrayPerm;
pub use small_perm::SmallPerm;
pub use vec_perm::VecPerm;

// SAFETY: Limit amount of code that can access fields with safety invariants
mod field_safety {
    use super::*;
    /// A permutation.
    #[repr(transparent)]
    pub struct Perm<Pt: Point> {
        // SAFETY: must always be a valid permutation.
        slice: [Pt],
    }

    impl<Pt: Point> Perm<Pt> {
        /// Returns the slice containing the images of `self.domain()`.
        #[inline(always)]
        pub fn as_slice(&self) -> &[Pt] {
            &self.slice
        }

        /// Returns the mutable slice containing the images of `self.domain()`.
        ///
        /// # Safety
        /// A `Perm` must always be a valid permutation and users may depend on this for memory
        /// safety. The user of this method has to ensure this invariant is maintained, even in the
        /// present of panics.
        #[inline(always)]
        pub unsafe fn as_mut_slice(&mut self) -> &mut [Pt] {
            &mut self.slice
        }

        /// Returns an unsafe mutable pointer to the images of `self.domain()`.
        #[inline(always)]
        pub fn as_mut_ptr(&mut self) -> *mut Pt {
            self.slice.as_mut_ptr()
        }

        /// Returns an unsafe pointer to the images of `self.domain()`.
        #[inline(always)]
        pub fn as_ptr(&self) -> *const Pt {
            self.slice.as_ptr()
        }
    }
}

pub use field_safety::Perm;

impl<Pt: Point> Perm<Pt> {
    /// The identity permutation.
    #[inline]
    pub const fn identity() -> &'static Self {
        // SAFETY: an empty slice is a valid permutation
        unsafe { Self::from_slice_unchecked(&[]) }
    }

    /// Checks whether a slice contains permutation of `0..slice.len()`.
    ///
    /// If the length of `slice` exceeds `Pt::MAX_DEGREE` this also returns `false`, even when it
    /// would be a valid permutation otherwise.
    pub fn is_perm(slice: &[Pt]) -> bool {
        if slice.len() > Pt::MAX_DEGREE {
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
    pub fn from_slice(slice: &[Pt]) -> &Self {
        assert!(Self::is_perm(slice));
        // SAFETY: `Self::is_perm` above checks the exact required invariant below
        unsafe { Self::from_slice_unchecked(slice) }
    }

    /// Creates a mutable `Perm` reference from a slice containing the images of the first n points.
    ///
    /// Panics for non-permutation arguments.
    #[inline]
    pub fn from_mut_slice(slice: &mut [Pt]) -> &mut Self {
        assert!(Self::is_perm(slice));
        // SAFETY: `Self::is_perm` above checks the exact required invariant below
        unsafe { Self::from_mut_slice_unchecked(slice) }
    }

    /// Creates a `Perm` reference from a slice containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `slice` must be a permutation of the points `0..slice.len()`.
    #[inline]
    pub const unsafe fn from_slice_unchecked(slice: &[Pt]) -> &Self {
        // SAFETY: `Self` is a `repr(transparent)` wrapper for `[Pt]`
        unsafe { &*(slice as *const [Pt] as *const Self) }
    }

    /// Creates a mutable `Perm` reference from a slice containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `slice` must be a permutation of the points `0..slice.len()`.
    #[inline]
    pub unsafe fn from_mut_slice_unchecked(slice: &mut [Pt]) -> &mut Self {
        // SAFETY: `Self` is a `repr(transparent)` wrapper for `[Pt]`
        unsafe { &mut *(slice as *mut [Pt] as *mut Self) }
    }

    /// Creates a `Perm` reference from an unsafe pointer of a given degree
    ///
    /// # Safety
    /// The argument `ptr` must point to a permutation of `0..degree`.
    #[inline]
    pub unsafe fn from_raw_parts<'a>(ptr: *const Pt, degree: usize) -> &'a Self {
        // SAFETY: documented caller as responsible for the requirements
        unsafe { Self::from_slice_unchecked(std::slice::from_raw_parts(ptr, degree)) }
    }

    /// Creates a mutable `Perm` reference from an unsafe pointer of a given degree
    ///
    /// # Safety
    /// The argument `ptr` must point to a permutation of `0..degree`.
    #[inline]
    pub unsafe fn from_raw_parts_mut<'a>(ptr: *mut Pt, degree: usize) -> &'a mut Self {
        // SAFETY: documented caller as responsible for the requirements
        unsafe { Self::from_mut_slice_unchecked(std::slice::from_raw_parts_mut(ptr, degree)) }
    }

    /// Parses a permutation from a string containing a cycle decomposition.
    #[inline]
    pub fn parse(s: &(impl AsRef<[u8]> + ?Sized)) -> ops::Parse<Pt> {
        ops::Parse::new(s)
    }

    /// Parses a permutation from a string containing a cycle decomposition using GAP syntax.
    #[inline]
    pub fn parse_gap(s: &(impl AsRef<[u8]> + ?Sized)) -> ops::Parse<Pt> {
        ops::Parse::gap(s)
    }

    /// Returns the size of the set the permutation acts on.
    ///
    /// A `Perm` acts on the set `0..self.degree()`.
    ///
    /// Unless documented otherwise, a smaller degree permutation is implicitly extended by adding
    /// fixed points when a larger degree permutation is expected.
    #[inline(always)]
    pub fn degree(&self) -> usize {
        self.as_slice().len()
    }

    /// Returns the image of a point under the permutation.
    ///
    /// When `point` is not in the permutation's domain, this returns `point`, implicitly extending
    /// the permutation with fixed points.
    #[inline]
    pub fn image(&self, point: Pt) -> Pt {
        self.image_of_index(point.index())
    }

    /// Returns the image of the `index`-th point under the permutation.
    #[inline]
    pub fn image_of_index(&self, index: usize) -> Pt {
        // NOTE: This could use a safe .get() instead, but as this will be called from inner loops
        // and as in the past I had issues with `Option` causing very poor codegen, I'll use this
        // simpler to optimize unsafe version instead. When I'm confident that a current rustc/llvm
        // won't generate silly code for this in any call site this might be inlined into, I will
        // change this.
        if index < self.degree() {
            // SAFETY: if condition is the exact required bound check
            unsafe { *self.as_slice().get_unchecked(index) }
        } else {
            Pt::from_index(index)
        }
    }

    /// Returns the set the permutation acts on.
    #[inline]
    pub fn domain(&self) -> PointRange<Pt> {
        PointIter::new(self.domain_indices())
    }

    /// Returns the indices of the points in the set the permutation acts on.
    ///
    /// See also [`Point::index`].
    #[inline]
    pub fn domain_indices(&self) -> Range<usize> {
        0..self.degree()
    }

    /// Returns the same permutation acting on a set with trailing fixed points removed.
    #[inline]
    pub fn as_min_degree(&self) -> &Self {
        self.shrink_to_degree(0)
    }

    /// Returns an iterator over all (point, image) pairs of the permutation.
    #[inline]
    pub fn iter(&self) -> Iter<Pt> {
        Iter::new(self)
    }

    /// Returns the cycle decomposition of this permutation.
    ///
    /// The cycle decomposition represents a permutation as a product of disjoint nontrivial cycles.
    /// As disjoint cycles commute, the order does not matter. To produce a canonical output, this
    /// method orders the cycles in increasing order of their smallest moved point. Every cycle is
    /// produced starting with its smallest moved point.
    ///
    /// This returns an [`Inplace`] value. To get a value that implements [`IntoIterator`] use
    /// [`.cycles().build()`][`Inplace::build`] or [`assign`][`AssignInplace::assign`] it to an
    /// existing value.
    #[inline]
    pub fn cycles(&self) -> CycleDecomposition<Pt> {
        CycleDecomposition::new(self)
    }

    #[inline]
    fn shrink_to_degree(&self, degree: usize) -> &Self {
        let mut shrunk = self.as_slice();
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
        unsafe { Self::from_slice_unchecked(shrunk) }
    }

    /// Returns the inverse of this permutation.
    #[inline]
    pub fn inv(&self) -> ops::Inv<Pt> {
        ops::Inv::new(self)
    }

    /// Returns the product of this permutation with another permutation.
    ///
    /// Aucavo follows the convention where applying the product of two permutations is the same as
    /// applying the _left_ permutation first, followed by the _right_ permutation. This is the same
    /// convention used by the computer algebra system GAP and it is often used in _computational_
    /// group theory literature.
    #[inline]
    pub fn prod<'a>(&'a self, other: &'a Perm<Pt>) -> ops::Prod<'a, Pt> {
        ops::Prod::new(self, other)
    }

    /// Returns the `n`-th power of this permutation.
    #[inline]
    pub fn pow(&self, n: isize) -> ops::Pow<Pt> {
        ops::Pow::new(self, n)
    }

    /// Advances to the lexicographically next permutation.
    ///
    /// This steps lexicographically through permutations of the same degree. It returns `false` and
    /// resets to the identity permutation (lexicographically first) when called on the
    /// lexciographically last permutation.
    #[inline]
    pub fn lexicographical_next(&mut self) -> bool {
        // SAFETY: modifies `self` as a valid permutation
        unsafe { raw::lexicographical_next(self.as_mut_ptr(), self.degree()) }
    }
}

impl<Pt: Point> fmt::Display for Perm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.cycles().build(), f)
    }
}

impl<Pt: Point> gap::FmtGap for Perm<Pt> {
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.cycles().build().fmt_gap(f)
    }
}

impl<Pt: Point> fmt::Debug for Perm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ 0..{}", self, self.degree())
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized> PartialEq<Rhs> for Perm<Pt> {
    #[inline]
    fn eq(&self, other: &Rhs) -> bool {
        let mut lhs = self;
        let mut rhs = other.borrow();

        if lhs.degree() != rhs.degree() {
            (lhs, rhs) = Self::eq_fixup(lhs, rhs);
        }

        lhs.as_slice() == rhs.as_slice()
    }
}

impl<Pt: Point> Perm<Pt> {
    #[inline]
    #[cold] // TUNE
    fn eq_fixup<'a>(mut lhs: &'a Self, mut rhs: &'a Self) -> (&'a Self, &'a Self) {
        if lhs.degree() > rhs.degree() {
            (lhs, rhs) = (rhs, lhs);
        }
        rhs = rhs.shrink_to_degree(lhs.degree());
        (lhs, rhs)
    }
}

impl<Pt: Point> Eq for Perm<Pt> {}

impl<Pt: Point> hash::Hash for Perm<Pt> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        let min_degree = self.as_min_degree();
        min_degree.as_slice().hash(state);
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized> PartialOrd<Rhs> for Perm<Pt> {
    #[inline]
    fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
        Some(self.cmp(other.borrow()))
    }
}

impl<Pt: Point> Ord for Perm<Pt> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let mut lhs = self;
        let mut rhs = other;
        let mut flip = false;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs, flip) = Self::cmp_fixup(lhs, rhs);
        }

        let mut result = lhs.as_slice().cmp(&rhs.as_slice()[..lhs.as_slice().len()]);

        if result.is_eq() && lhs.degree() != rhs.degree() {
            result = cmp::Ordering::Less;
        }

        if flip {
            result.reverse()
        } else {
            result
        }
    }
}

impl<Pt: Point> Perm<Pt> {
    #[inline]
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
}

/// Types that can store a permutation.
///
/// As a user, there is usually no need to use nor to implement this trait. This trait is the unsafe
/// low level interface implemented for [`Perm`] storing type like [`VecPerm`], [`ArrayPerm`], etc.
/// It makes it possible to assign permutations to values of these type or to obtain new values of
/// this type from a permutation.
///
/// Operations that produce such permutations do not use this trait directly, instead they implement
/// [`PermVal`] and rely on an [`Inplace`] instance that enables assigning [`PermVal`]s to
/// [`StorePerm`]s or building new [`StorePerm`]s from [`PermVal`]s.
///
/// # Safety
///
/// The following sequence must be safe for any implementing type `O` of this trait:
///
/// ```no_run
/// # use aucavo::{point::Point, perm::*};
///
/// fn overwrite<O: StorePerm>(t: &mut O, degree: usize) {
///     unsafe {
///         assert!(degree <= O::Point::MAX_DEGREE);
///         let target = t.prepare_assign_with_degree(degree);
///         init(target, degree);
///         t.assume_assign_init(degree);
///     }
/// }
///
/// unsafe fn init<Pt: Point>(target: *mut Pt, degree: usize) {
/// #    raw::write_identity(target, degree);
///     // See below for details
/// }
/// ```
///
/// Here `O` may rely on `degree <= O::Point::MAX_DEGREE`. When `prepare_assign_with_degree` does
/// not panic, it must return a `*mut Pt` pointer with storage for `degree` points and `init` may
/// rely on this for safety. When `init` does not panic, it must have initialized `target` with a
/// valid permutation of degree `degree`. When `init` does panic, it may do so a) before writing
/// anything to `target` or b) after having overwritten `target` with a valid permutation. It may
/// never read from `target`, nor write uninitialized data to `target`, nor panic with a partially
/// overwritten or otherwise non-permutation `target`. Finally `assume_assign_init` may assume that
/// the parameter has the same value previously passed to `prepare_assign_with_degree`.
///
/// For types `O: Sized` the following additional sequence must be safe:
///
/// ```no_run
/// # use aucavo::{point::Point, perm::*};
///
/// fn overwrite<O: StorePerm>(degree: usize) -> O {
///     unsafe {
///         assert!(degree <= O::Point::MAX_DEGREE);
///         let mut u = O::new_uninit_with_degree(degree);
///         let target = O::prepare_new_uninit_with_degree(&mut u, degree);
///         init(target, degree);
///         O::assume_new_init(u, degree)
///     }
/// }
///
/// unsafe fn init<Pt: Point>(target: *mut Pt, degree: usize) {
/// #    raw::write_identity(target, degree);
///     // See below for details
/// }
/// ```
///
/// Here `O` may rely on `degree <= O::Point::MAX_DEGREE`. Here `prepare_new_uninit_with_degree` may
/// assume that the `degree` parameter has the same value previously passed to
/// `new_uninit_with_degree`.  When `prepare_new_uninit_with_degree` does not panic, it must return
/// a `*mut Pt` pointer with storage for `degree` points and `init` may rely on this for safety.
/// When `init` does not panic, it must have initialized `target` with a valid permutation of degree
/// `degree`. When `init` does panic, it may do so a) before writing anything to `target` or b)
/// after having overwritten `target` with a valid permutation. It may never read from `target`, nor
/// write uninitialized data to `target`, nor panic with a partially overwritten or otherwise
/// non-permutation `target`. Finally `assume_new_init` may assume that the `degree` parameter has
/// the same value previously passed to `new_uninit_with_degree` and to
/// `prepare_new_uninit_with_degree`.
///
/// Users of this trait may only invoke the methods following either of these two call sequences.
pub unsafe trait StorePerm {
    /// Point representation used.
    type Point: Point;
    /// Type for an uninitialized value.
    type Uninit;

    /// Builds a new uninitialized value, preparing to store a permutation of the given degree.
    ///
    /// # Safety
    /// See [`StorePerm`] for a complete description.
    unsafe fn new_uninit_with_degree(degree: usize) -> Self::Uninit
    where
        Self: Sized;

    /// Prepares the uninitialized value for writing a permutation of the given degree.
    ///
    /// # Safety
    /// See [`StorePerm`]  for a complete description. Implementations may expect `degree` to be
    /// the same value provided for `new_uninit_with_degree` and have to return a value of that
    /// degree.
    unsafe fn prepare_new_uninit_with_degree(
        uninit: &mut Self::Uninit,
        degree: usize,
    ) -> *mut Self::Point
    where
        Self: Sized;

    /// Returns an initialized value after a permutation was written to it.
    ///
    /// # Safety
    /// See [`StorePerm`] for a complete description. Implementations may expect `degree` to be the
    /// same value provided for `new_uninit_with_degree` and `prepare_new_uninit_with_degree`.
    /// Implementations may also assume that the permutation was initialized before this was called.
    /// Implementation have to ensure that a panic before reaching this point is safe.
    unsafe fn assume_new_init(uninit: Self::Uninit, degree: usize) -> Self
    where
        Self: Sized;

    /// Prepares an existing value for assigning a new permutation of the given degree.
    ///
    /// # Safety
    /// See [`StorePerm`] for a complete description.
    unsafe fn prepare_assign_with_degree(&mut self, degree: usize) -> *mut Self::Point;

    /// Finalizes a value after it was overwritten with a permutation of the given degree.
    ///
    /// # Safety
    /// See [`StorePerm`] for a complete description. Implementations may expect `degree` to be the
    /// same value provided for `prepare_assign_with_degree`. Implementations may also assume that
    /// the permutation was initialized before this was called. Implementation have to ensure that a
    /// panic before reaching this point is safe.
    unsafe fn assume_assign_init(&mut self, degree: usize);
}

/// Panics when assigning a permutation with a larger degree than the existing value.
// SAFETY: See `StorePerm`'s safety section for details
unsafe impl<Pt: Point> StorePerm for Perm<Pt> {
    type Point = Pt;
    type Uninit = MaybeUninit<Pt>;

    unsafe fn new_uninit_with_degree(_degree: usize) -> Self::Uninit
    where
        Self: Sized,
    {
        unreachable!()
    }

    unsafe fn prepare_new_uninit_with_degree(
        _uninit: &mut Self::Uninit,
        _degree: usize,
    ) -> *mut Self::Point
    where
        Self: Sized,
    {
        unreachable!()
    }

    unsafe fn assume_new_init(_uninit: Self::Uninit, _degree: usize) -> Self
    where
        Self: Sized,
    {
        unreachable!()
    }

    #[inline]
    unsafe fn prepare_assign_with_degree(&mut self, degree: usize) -> *mut Self::Point {
        assert!(degree <= self.degree());
        // SAFETY: Both `StorePerm` and the assert guarantee `self.slice.len() <= Pt::MAX_DEGREE`
        let target = self.as_mut_ptr();
        // SAFETY: initializes padding for excess points not written by the caller
        unsafe { raw::write_identity_padding(target, degree, self.degree()) };
        target
    }

    #[inline]
    unsafe fn assume_assign_init(&mut self, _degree: usize) {}
}

// SAFETY: See `StorePerm`'s safety section for details
unsafe impl<T: ?Sized> StorePerm for &mut T
where
    T: StorePerm,
{
    type Point = T::Point;
    type Uninit = T::Uninit;

    unsafe fn new_uninit_with_degree(_degree: usize) -> Self::Uninit
    where
        Self: Sized,
    {
        unreachable!()
    }

    unsafe fn prepare_new_uninit_with_degree(
        _uninit: &mut Self::Uninit,
        _degree: usize,
    ) -> *mut Self::Point
    where
        Self: Sized,
    {
        unreachable!()
    }

    unsafe fn assume_new_init(_uninit: Self::Uninit, _degree: usize) -> Self
    where
        Self: Sized,
    {
        unreachable!()
    }

    unsafe fn prepare_assign_with_degree(&mut self, degree: usize) -> *mut Self::Point {
        // SAFETY: forwarding to an implementation with the same safety requirements
        unsafe { T::prepare_assign_with_degree(self, degree) }
    }

    unsafe fn assume_assign_init(&mut self, degree: usize) {
        // SAFETY: forwarding to an implementation with the same safety requirements
        unsafe { T::assume_assign_init(self, degree) }
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
/// operations.
///
/// # Safety
/// Implementations must uphold the documented safety requirements for both
/// [`degree`][`Self::degree`] as well as [`write_into_mut_ptr`][`Self::write_into_mut_ptr`], as
/// callers do rely on them for safety.
pub unsafe trait PermVal<Pt: Point>: Sized {
    /// Returns the size of the set the permutation acts on.
    ///
    /// See also [`Perm::degree`].
    ///
    /// # Safety
    /// Calling this repeatedly must always return the same value. Implementations of
    /// [`write_into_mut_ptr`][`Self::write_into_mut_ptr`] may require the passed `target` to have
    /// this degree.
    fn degree(&self) -> usize;

    /// Writes a permutation to a potentially uninitialized target.
    ///
    /// # Safety
    /// Callers must provide a target pointing at storage for [`self.degree()`][`Self::degree`]
    /// points. Implementations may not read from `target` and must fully initialize it with a valid
    /// permutation of degree [`self.degree()`][`Self::degree`] and/or panic. When implementations
    /// panic the data at `target` must either be left in its original state or have been completely
    /// overwritten with a valid permutation.
    unsafe fn write_into_mut_ptr(self, target: *mut Pt);
}

/// Disambiguator for the [`Inplace`] impl assigning [`PermVal`]s to [`StorePerm`]s.
pub enum InplacePerm {}

impl<O: StorePerm + ?Sized, T> Inplace<O, InplacePerm> for T
where
    T: PermVal<O::Point>,
{
    type Err = Infallible;

    #[inline]
    fn try_build(self) -> Result<O, Self::Err>
    where
        O: Sized,
    {
        // SAFETY: As described in [`StorePerm`]'s safety section
        unsafe {
            let degree = self.degree();
            let mut uninit = O::new_uninit_with_degree(degree);
            let target = O::prepare_new_uninit_with_degree(&mut uninit, degree);
            self.write_into_mut_ptr(target);
            Ok(O::assume_new_init(uninit, degree))
        }
    }

    #[inline]
    fn try_assign_to(self, output: &mut O) -> Result<(), Self::Err> {
        // SAFETY: As described in [`StorePerm`]'s safety section
        unsafe {
            let degree = self.degree();
            let target = output.prepare_assign_with_degree(degree);
            self.write_into_mut_ptr(target);
            output.assume_assign_init(degree);
        }
        Ok(())
    }
}

// SAFETY: `write_into_mut_ptr(output)` completly overwrites `output` with a valid permutation of
// length `degree()`.
unsafe impl<Pt: Point> PermVal<Pt> for &Perm<Pt> {
    #[inline]
    fn degree(&self) -> usize {
        Perm::degree(self)
    }

    #[inline]
    unsafe fn write_into_mut_ptr(self, target: *mut Pt) {
        // SAFETY: copies existing valid permutation of the correct length
        unsafe { target.copy_from_nonoverlapping(self.as_ptr(), Perm::degree(self)) };
    }
}

// SAFETY: `write_into_mut_ptr(output)` completly overwrites `output` with a valid permutation of
// length `degree()`.
unsafe impl<Pt: Point> PermVal<Pt> for &mut Perm<Pt> {
    #[inline]
    fn degree(&self) -> usize {
        (self as &Perm<Pt>).degree()
    }

    #[inline]
    unsafe fn write_into_mut_ptr(self, target: *mut Pt) {
        // SAFETY: forwarding to `&Perm<Pt>`'s implementation upholds all safety requirements on
        // both the implementation and the call site.
        unsafe { (self as &Perm<Pt>).write_into_mut_ptr(target) }
    }
}

#[cfg(test)]
mod tests {
    use crate::inplace::AssignInplace;

    use super::*;

    #[test]
    fn array_perm_all_order() {
        let perms: Vec<_> = ArrayPerm::<u8, 5>::all().collect();

        for pairs in perms.windows(2) {
            assert!(pairs[0] < pairs[1]);
        }
    }

    #[test]
    fn parse_mut_perm() {
        let mut g: ArrayPerm<u8, 5> = Default::default();
        let g: &mut Perm<u8> = &mut g;

        for h in ArrayPerm::<u8, 5>::all() {
            g.try_assign(Perm::parse(&h.to_string())).unwrap();
            assert_eq!(*g, h);
        }
    }

    #[test]
    fn parse_vec_perm() {
        let mut g: VecPerm<u8> = Default::default();

        for h in ArrayPerm::<u8, 5>::all() {
            g.try_assign(Perm::parse(&h.to_string())).unwrap();
            assert_eq!(g, h);
        }
    }

    #[test]
    fn parse_array_perm() {
        let mut g: ArrayPerm<u8, 5> = Default::default();

        for h in ArrayPerm::<u8, 5>::all() {
            g.try_assign(Perm::parse(&h.to_string())).unwrap();
            assert_eq!(g, h);
        }
    }

    #[test]
    fn parse_small_perm_tiny() {
        let mut g: SmallPerm<u8, 4> = Default::default();

        for h in ArrayPerm::<u8, 5>::all() {
            g.try_assign(Perm::parse(&h.to_string())).unwrap();
            assert_eq!(g, h);
        }
    }

    #[test]
    fn parse_small_perm_large() {
        let mut g: SmallPerm<u8, 16> = Default::default();

        for h in ArrayPerm::<u8, 5>::all() {
            g.try_assign(Perm::parse(&h.to_string())).unwrap();
            assert_eq!(g, h);
        }
    }
}
