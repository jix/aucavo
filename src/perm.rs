//! Permutations.
use std::{
    borrow::Borrow,
    cmp, fmt, hash,
    mem::MaybeUninit,
    ops::{Deref, DerefMut, Range},
};

use smallvec::{smallvec, SmallVec};

use crate::{
    cycles::CycleDecomposition,
    inplace::{AssignInplace, Inplace},
    point::{Point, PointIter, PointRange},
};

use self::iter::{AllArrayPerms, Iter};

pub mod iter;
pub mod ops;

/// A permutation.
#[repr(transparent)]
pub struct Perm<Pt: Point> {
    // SAFETY: must always be a valid permutation.
    slice: [Pt],
}

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

    /// Returns the slice containing the images of `self.domain()`.
    #[inline]
    pub fn as_slice(&self) -> &[Pt] {
        &self.slice
    }

    /// Returns the mutable slice containing the images of `self.domain()`.
    ///
    /// # Safety
    /// A `Perm` must always be a valid permutation and users may depend on this for memory safety.
    /// The user of this method has to ensure this invariant is maintained, even in the present of
    /// panics.
    #[inline]
    pub unsafe fn as_mut_slice(&mut self) -> &mut [Pt] {
        &mut self.slice
    }

    /// Returns the size of the set the permutation acts on.
    ///
    /// A `Perm` acts on the set `0..self.degree()`.
    ///
    /// Unless documented otherwise, a smaller degree permutation is implicitly extended by adding
    /// fixed points when a larger degree permutation is expected.
    #[inline]
    pub fn degree(&self) -> usize {
        self.slice.len()
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
        if index < self.slice.len() {
            // SAFETY: if condition is the exact required bound check
            unsafe { *self.slice.get_unchecked(index) }
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
        let mut shrunk = &self.slice;
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

    /// Advances to the lexicographically next permutation.
    ///
    /// This steps lexicographically through permutations of the same degree. It returns `false` and
    /// resets to the identity permutation (lexicographically first) when called on the
    /// lexciographically last permutation.
    pub fn lexicographical_next(&mut self) -> bool {
        let mut right_to_left = self.slice.iter().copied().enumerate().rev();
        let Some((_, mut prev)) = right_to_left.next() else { return false };

        let Some((a, a_image)) = right_to_left.find(|&(_, current)| {
            let found = current < prev;
            prev = current;
            found
        }) else {
            self.assign(Self::identity());
            return false;
        };

        let b = a + 1 + self.slice[a + 2..].partition_point(|&b_image| b_image > a_image);

        self.slice.swap(a, b);
        self.slice[a + 1..].reverse();
        true
    }
}

impl<Pt: Point> fmt::Display for Perm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.cycles().build(), f)
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

/// Owned permutation backed by a [`Vec`].
///
/// Most functionality is provided via the [`Deref`] implementation to [`Perm`].
#[derive(Default)]
pub struct VecPerm<Pt: Point> {
    // SAFETY: must always be a valid permutation.
    vec: Vec<Pt>,
}

impl<Pt: Point> Deref for VecPerm<Pt> {
    type Target = Perm<Pt>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: `VecPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_slice_unchecked(self.vec.as_slice()) }
    }
}

impl<Pt: Point> DerefMut for VecPerm<Pt> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `VecPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_mut_slice_unchecked(self.vec.as_mut_slice()) }
    }
}

impl<Pt: Point> Borrow<Perm<Pt>> for VecPerm<Pt> {
    #[inline]
    fn borrow(&self) -> &Perm<Pt> {
        self.deref()
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized> PartialEq<Rhs> for VecPerm<Pt> {
    #[inline]
    fn eq(&self, other: &Rhs) -> bool {
        self.deref().eq(other.borrow())
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized> PartialOrd<Rhs> for VecPerm<Pt> {
    #[inline]
    fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
        Some(self.deref().cmp(other.borrow()))
    }
}

impl<Pt: Point> Eq for VecPerm<Pt> {}

impl<Pt: Point> Ord for VecPerm<Pt> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<Pt: Point> hash::Hash for VecPerm<Pt> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<Pt: Point> VecPerm<Pt> {
    /// Returns a new `VecPerm` initialized to the identity permutation.
    #[inline]
    pub fn identity() -> Self {
        Self::default()
    }

    /// Returns a new `VecPerm` initialized to the identity permutation.
    #[inline]
    pub fn identity_with_degree(degree: usize) -> Self {
        assert!(degree <= Pt::MAX_DEGREE);
        // SAFETY: initializes with a valid permutation
        Self {
            vec: (0..degree).map(Pt::from_index).collect(),
        }
    }
}

/// Owned permutation backed by an array.
///
/// These have a fixed degree and panic when assigning a permutation of a larger degree.
#[derive(Clone, Copy)]
pub struct ArrayPerm<Pt: Point, const N: usize> {
    // SAFETY: must always be a valid permutation.
    array: [Pt; N],
}

impl<Pt: Point, const N: usize> Default for ArrayPerm<Pt, N> {
    fn default() -> Self {
        #[allow(clippy::let_unit_value)]
        let _ = Self::ASSERT_VALID_DEGREE;
        assert!(N <= Pt::MAX_DEGREE);

        // FUTURE: I expect this to require less/no unsafe in the future
        let mut uninitialized: MaybeUninit<[Pt; N]> = MaybeUninit::uninit();
        // SAFETY: `MaybeUninit<[Pt; N]>` is valid iff `[MaybeUninit<Pt>; N]` is and they have the
        // same layout
        let transposed = unsafe { &mut *(uninitialized.as_mut_ptr() as *mut [MaybeUninit<Pt>; N]) };

        for (i, p) in transposed.iter_mut().enumerate() {
            p.write(Pt::from_index(i));
        }

        Self {
            // SAFETY: initialized as identity above, including a static check for the max degree
            array: unsafe { uninitialized.assume_init() },
        }
    }
}

impl<Pt: Point, const N: usize> Deref for ArrayPerm<Pt, N> {
    type Target = Perm<Pt>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: `ArrayPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_slice_unchecked(self.array.as_slice()) }
    }
}

impl<Pt: Point, const N: usize> DerefMut for ArrayPerm<Pt, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `ArrayPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_mut_slice_unchecked(self.array.as_mut_slice()) }
    }
}

impl<Pt: Point, const N: usize> Borrow<Perm<Pt>> for ArrayPerm<Pt, N> {
    #[inline]
    fn borrow(&self) -> &Perm<Pt> {
        self.deref()
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized, const N: usize> PartialEq<Rhs>
    for ArrayPerm<Pt, N>
{
    #[inline]
    fn eq(&self, other: &Rhs) -> bool {
        self.deref().eq(other.borrow())
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized, const N: usize> PartialOrd<Rhs>
    for ArrayPerm<Pt, N>
{
    #[inline]
    fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
        Some(self.deref().cmp(other.borrow()))
    }
}

impl<Pt: Point, const N: usize> Eq for ArrayPerm<Pt, N> {}

impl<Pt: Point, const N: usize> Ord for ArrayPerm<Pt, N> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<Pt: Point, const N: usize> hash::Hash for ArrayPerm<Pt, N> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<Pt: Point, const N: usize> ArrayPerm<Pt, N> {
    const ASSERT_VALID_DEGREE: () = Self::assert_valid_degree();

    const fn assert_valid_degree() {
        assert!(N <= Pt::MAX_DEGREE);
    }

    /// Returns an iterator over all permutations of a fixed degree.
    pub fn all() -> AllArrayPerms<Pt, N> {
        Default::default()
    }

    /// Returns a new `ArrayPerm` initialized to the identity permutation.
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
impl<Pt: Point> StorePerm for Perm<Pt> {
    type Point = Pt;
    fn build_from_perm_val(_perm: impl PermVal<Pt>) -> Self
    where
        Self: Sized,
    {
        unreachable!()
    }

    #[inline]
    fn assign_perm_val(&mut self, perm: impl PermVal<Pt>) {
        let mut degree = perm.degree();

        // We use that `split_at_mut` panics when the degree is too large
        let (new_perm, fixed_suffix) = self.slice.split_at_mut(degree);

        // SAFETY: `PermVal` guarantees that `write_to_slice` writes a fully initialized valid
        // permutation when the passed slice has the requested size.
        unsafe {
            let new_perm: &mut [MaybeUninit<Pt>] =
                &mut *(new_perm as *mut [Pt] as *mut [MaybeUninit<Pt>]);
            perm.write_to_slice(new_perm);
        };

        for p in fixed_suffix {
            *p = Pt::from_index(degree);
            degree += 1;
        }
    }
}

/// Allocates new storage when assigning a permutation with a larger degree than the existing value.
///
/// The implementation uses `reserve_exact` to only allocate as much memory as required. While this
/// saves memory for typical uses cases involving permutations, it can cause quadratic runtime when
/// gorwing the degree of a permutation one at a time.
impl<Pt: Point> StorePerm for VecPerm<Pt> {
    type Point = Pt;

    #[inline]
    fn build_from_perm_val(perm: impl PermVal<Pt>) -> Self
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
    fn assign_perm_val(&mut self, perm: impl PermVal<Pt>) {
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
                *p = MaybeUninit::new(Pt::from_index(degree));
                degree += 1;
            }

            self.vec.set_len(new_degree);
        }
    }
}

/// Panics when assigning a permutation with a larger degree than `N`.
impl<Pt: Point, const N: usize> StorePerm for ArrayPerm<Pt, N> {
    type Point = Pt;

    #[inline]
    fn build_from_perm_val(perm: impl PermVal<Self::Point>) -> Self
    where
        Self: Sized,
    {
        // FUTURE: I expect this to require less/no unsafe in the future
        let mut uninitialized: MaybeUninit<[Pt; N]> = MaybeUninit::uninit();
        // SAFETY: `MaybeUninit<[Pt; N]>` is valid iff `[MaybeUninit<Pt>; N]` is and they have the
        // same layout
        let transposed = unsafe { &mut *(uninitialized.as_mut_ptr() as *mut [MaybeUninit<Pt>; N]) };

        // We use that `split_at_mut` panics when the degree is too large
        let mut degree = perm.degree();
        let (new_perm, fixed_suffix) = transposed.split_at_mut(degree);

        // SAFETY: `PermVal` guarantees that `write_to_slice` writes a fully initialized valid
        // permutation when the passed slice has the requested size.
        unsafe {
            perm.write_to_slice(new_perm);
        };

        for p in fixed_suffix {
            p.write(Pt::from_index(degree));
            degree += 1;
        }

        Self {
            // SAFETY: fully initialized above
            array: unsafe { uninitialized.assume_init() },
        }
    }

    #[inline]
    fn assign_perm_val(&mut self, perm: impl PermVal<Self::Point>) {
        self.deref_mut().assign_perm_val(perm);
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
pub unsafe trait PermVal<Pt: Point>: Sized {
    /// Returns the size of the set the permutation acts on.
    ///
    /// See also [`Perm::degree`].
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
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<Pt>]);
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
unsafe impl<Pt: Point> PermVal<Pt> for &Perm<Pt> {
    #[inline]
    fn degree(&self) -> usize {
        Perm::degree(self)
    }

    #[inline]
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<Pt>]) {
        let slice: &[MaybeUninit<Pt>] =
            // SAFETY: safe cast of &[Pt] to &[MaybeUninit<Pt>]
            // FUTURE: Use a safe alternative when available (e.g. #79995)
            unsafe { &*(self.as_slice() as *const [Pt] as *const [MaybeUninit<Pt>]) };
        output.copy_from_slice(slice);
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for &mut Perm<Pt> {
    #[inline]
    fn degree(&self) -> usize {
        (self as &Perm<Pt>).degree()
    }

    #[inline]
    unsafe fn write_to_slice(self, output: &mut [MaybeUninit<Pt>]) {
        // SAFETY: forwarding to `&Perm<Pt>`'s implementation upholds all safety requirements on both
        // the implementation and the call site.
        unsafe { (self as &Perm<Pt>).write_to_slice(output) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_perm_all_order() {
        let perms: Vec<_> = ArrayPerm::<u8, 7>::all().collect();

        for pairs in perms.windows(2) {
            assert!(pairs[0] < pairs[1]);
        }
    }
}
