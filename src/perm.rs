//! Permutation data types and algorithms.

use crate::TmpVec;
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use smallvec::{Array, SmallVec};
use std::{
    borrow::Cow,
    fmt::{Debug, Display},
    hash::Hash,
    ptr::copy_nonoverlapping,
    rc::Rc,
    sync::Arc,
};

/// Set of values on which a permutation acts.
///
/// For the data types in this module, permutations act on a set of non-negative integers up to a
/// limit depending on which `Point` type is used. The `Point` type must behave exactly like a
/// Rust-builtin unsigned primitive integer type. The corresponding set of points are all values of
/// that integer type.
///
/// # Safety
///
/// Types implementing `Point` must behave like a Rust-builtin unsigned primitive integer type in
/// any observable way. Additionally every value of `Point` must be representable using a `usize`.
pub unsafe trait Point:
    PrimInt + Unsigned + AsPrimitive<usize> + Hash + Display + Debug
{
    /// Perform an `as` cast from a `usize` to a `Point` type.
    ///
    /// Like rusts `as` operator this truncates higher bits when the passed value does not fit into
    /// the `Point` type.
    fn unchecked_from_usize(value: usize) -> Self;
}

macro_rules! implement_point_trait {
    ($t:ty) => {
        unsafe impl Point for $t {
            #[inline(always)]
            fn unchecked_from_usize(value: usize) -> Self {
                value as Self
            }
        }
    };
}

implement_point_trait!(usize);
implement_point_trait!(u16);
implement_point_trait!(u8);

#[cfg(target_pointer_width = "64")]
implement_point_trait!(u64);
#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
implement_point_trait!(u32);

/// A permutation of points.
///
/// A permutation is a one-to-one mapping of a set of points onto itself. For a [`Perm`] this set of
/// points is an unsigned integer type implementing the [`Point`] trait.
///
/// Conceptually a `Perm` is a permutation on _all_ of [`Point`]'s values. To efficiently represent
/// permutations on smaller sets, a `Perm` is stored as a truncated arrangement (abbreviated as
/// `tarr` in method names) which lists the images of all points from 0 up to and including the
/// largest moved point.
///
/// This truncated arrangement is stored in a value of type parameter `S` implementing the
/// [`PermStorage`] trait. This includes [`Point`] slices and [`Vec`]s, as well as references,
/// [`Box`]es, [`Rc`]s, [`Arc`]s, [`Cow`]s containing
/// those.
///
/// The corresponding type of [`Point`]s of a `Perm<S>` can be accessed as the associated type
/// [`S::Point`][PermStorage::Point] of [`PermStorage`].
#[repr(transparent)]
pub struct Perm<S: ?Sized>(S);

impl<S: PermStorage> Perm<S> {
    /// Construct a permutation from a truncated arrangement.
    ///
    /// This method verifies that the given [`PermStorage`] value is in fact a valid truncated
    /// arrangement of a permutation. This can fail if it does not describe a permutation or if the
    /// passed value ends with a fixed point. In both cases the input value is returned unmodified
    /// within the [`Err`][Result::Err].
    pub fn from_tarr(tarr: S) -> Result<Perm<S>, S> {
        let stored_tarr = tarr.stored_tarr();
        let mut seen = tmpvec![false; stored_tarr.len()];
        let mut last_fixed = false;
        for (i, point) in stored_tarr.iter().enumerate() {
            last_fixed = i == point.as_();
            if let Some(seen_point) = seen.get_mut(point.as_()) {
                if *seen_point {
                    return Err(tarr);
                }
                *seen_point = true;
            } else {
                return Err(tarr);
            }
        }
        if last_fixed {
            Err(tarr)
        } else {
            Ok(Perm(tarr))
        }
    }

    /// Construct a permutation from a truncated arrangement without verifying it.
    ///
    /// # Safety
    ///
    /// The passed truncated arrangement must describe a permutation and must be minimal, i.e. it
    /// may not end with a fixed point.
    #[inline(always)]
    pub unsafe fn from_tarr_unchecked(tarr: S) -> Perm<S> {
        Perm(tarr)
    }

    /// Obtains the value storing this permutation's truncated arrangement.
    ///
    /// See also [`storage`][Self::storage].
    pub fn into_storage(self) -> S {
        self.0
    }
}

impl<S: PermStorage + ?Sized> Perm<S> {
    /// The truncated arrangement of the permutation.
    ///
    /// This is always returned as a slice, use [`storage`][Self::storage] to access the value
    #[inline(always)]
    pub fn tarr(&self) -> &[S::Point] {
        self.0.stored_tarr()
    }

    /// Return a reference to the value storing this permutation's truncated arrangement.
    ///
    /// In most cases using [`tarr`][Self::tarr], which always returns the truncated arrangement as
    /// slice, is preferable.
    ///
    /// See also [`into_storage`][Self::into_storage].
    #[inline(always)]
    pub fn storage(&self) -> &S {
        &self.0
    }

    /// Returns `true` for the identity permutation.
    #[inline(always)]
    pub fn is_identity(&self) -> bool {
        self.tarr().is_empty()
    }
}

impl<S: PermStorageMut + Default> Perm<S> {
    /// Create a new value storing a given permutation.
    #[inline(always)]
    pub fn new(expr: impl PermExpr<Point = S::Point>) -> Perm<S> {
        Perm(S::from_expr(expr))
    }

    /// The identity permutation.
    pub fn identity() -> Perm<S> {
        Default::default()
    }
}

impl<'a, S: ?Sized> From<Perm<&'a S>> for &'a Perm<S> {
    #[inline(always)]
    fn from(perm: Perm<&S>) -> Self {
        // SAFETY: This is a safe cast as Perm is repr(transparent)
        unsafe { &*(perm.0 as *const S as *const Perm<S>) }
    }
}

impl<'a, S: ?Sized> From<Perm<&'a mut S>> for &'a mut Perm<S> {
    #[inline(always)]
    fn from(perm: Perm<&mut S>) -> Self {
        // SAFETY: This is a safe cast as Perm is repr(transparent)
        unsafe { &mut *(perm.0 as *mut S as *mut Perm<S>) }
    }
}

impl<'a, S: ?Sized> From<&'a Perm<S>> for Perm<&'a S> {
    #[inline(always)]
    fn from(perm: &'a Perm<S>) -> Self {
        Perm(&perm.0)
    }
}

impl<'a, S: ?Sized> From<&'a mut Perm<S>> for Perm<&'a mut S> {
    #[inline(always)]
    fn from(perm: &'a mut Perm<S>) -> Self {
        Perm(&mut perm.0)
    }
}

impl<S: PermStorage + ?Sized> AsRef<Perm<[S::Point]>> for Perm<S> {
    #[inline(always)]
    fn as_ref(&self) -> &Perm<[S::Point]> {
        // SAFETY: as we get the tarr from a Perm, we don't need to check it
        unsafe { Perm::from_tarr_unchecked(self.tarr()).into() }
    }
}

impl<S: PermStorageMut + Default> Default for Perm<S> {
    fn default() -> Self {
        Perm(S::default())
    }
}

impl<S, T> PartialEq<Perm<T>> for Perm<S>
where
    S: PermStorage + ?Sized,
    T: PermStorage<Point = S::Point> + ?Sized,
{
    #[inline(always)]
    fn eq(&self, other: &Perm<T>) -> bool {
        // As the truncated arrangement is defined to have minimal length, it is unique for a given
        // permutation.
        self.tarr() == other.tarr()
    }
}

impl<S: PermStorage + ?Sized> Eq for Perm<S> {}

// Lexicographic order of the truncated arrangement is the same as lexicographic order of the full
// arrangement. The only difference could be, if a shorter truncated arrangement is a prefix of a
// longer one. In that case the prefix following value of the value of the longer one, which is
// fixed by the permutation corresponding to the shorter one, must map to a larger or equal value,
// as all smaller values are already taken by the shared prefix. Thus the shorter truncated
// arrangement comparing less than the longer one, matches the lexicographic order of the full
// arrangement.

/// Permutations are ordered lexicographically by their arrangement.
impl<S, T> PartialOrd<Perm<T>> for Perm<S>
where
    S: PermStorage + ?Sized,
    T: PermStorage<Point = S::Point> + ?Sized,
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Perm<T>) -> Option<std::cmp::Ordering> {
        self.tarr().partial_cmp(other.tarr())
    }

    #[inline(always)]
    fn lt(&self, other: &Perm<T>) -> bool {
        self.tarr().lt(other.tarr())
    }

    #[inline(always)]
    fn le(&self, other: &Perm<T>) -> bool {
        self.tarr().le(other.tarr())
    }

    #[inline(always)]
    fn gt(&self, other: &Perm<T>) -> bool {
        self.tarr().gt(other.tarr())
    }

    #[inline(always)]
    fn ge(&self, other: &Perm<T>) -> bool {
        self.tarr().ge(other.tarr())
    }
}

/// Permutations are ordered lexicographical by their arrangement.
impl<S: PermStorage + ?Sized> Ord for Perm<S> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.tarr().cmp(other.tarr())
    }
}

impl<S: PermStorage + ?Sized> Hash for Perm<S> {
    #[inline(always)]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tarr().hash(state)
    }
}

impl<S: PermStorage> Debug for Perm<S> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use less generic implementation to avoid generating too much code
        self.as_ref().debug_format(f)
    }
}

impl<S: PermStorage> Display for Perm<S> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use less generic implementation to avoid generating too much code
        self.as_ref().display_format(f)
    }
}

impl<P: Point> Perm<[P]> {
    fn display_format(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tarr = self.tarr();
        if tarr.is_empty() {
            f.write_str("()")?;
        } else {
            let mut output = tmpvec![false; tarr.len()];
            for (i, &j) in tarr.iter().enumerate() {
                if i == j.as_() || output[i] {
                    continue;
                }
                f.write_str("(")?;
                Display::fmt(&i, f)?;
                let mut k = j.as_();
                while k != i {
                    f.write_str(" ")?;
                    Display::fmt(&k, f)?;
                    output[k] = true;
                    k = tarr[k].as_();
                }
                f.write_str(")")?;
            }
        }
        Ok(())
    }

    fn debug_format(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_identity() {
            f.write_str("perm![]")?;
        } else {
            f.write_str("perm![")?;
            self.display_format(f)?;
            f.write_str("]")?;
        }
        Ok(())
    }
}

unsafe impl<S: PermStorage> PermExpr for Perm<S> {
    type Point = S::Point;

    #[inline(always)]
    fn assign_to_perm_storage<St: PermStorageMut<Point = Self::Point>>(self, target: &mut St) {
        target.set_stored_tarr_from_tarr_slice(self.tarr());
    }
}

unsafe impl<S: PermStorage + ?Sized> PermExpr for &Perm<S> {
    type Point = S::Point;

    #[inline(always)]
    fn assign_to_perm_storage<St: PermStorageMut<Point = Self::Point>>(self, target: &mut St) {
        target.set_stored_tarr_from_tarr_slice(self.tarr());
    }
}

/// Types that can be used by [`Perm`] to store a truncated arrangement.
///
/// You can think of this as [`AsRef<[P]>`][std::convert::AsRef] where `P` implements [`Point`] with
/// the additional guarantee, that the underlying slice of points accessed by
/// [`stored_tarr`][Self::stored_tarr] can only be changed by obtaining a _mutable_ reference to a
/// type of this trait.
///
/// # Safety
///
/// Any implementing type must guarantee that [`stored_tarr`][Self::stored_tarr] does not change
/// unless a mutable reference to the value of the implementing type is obtained.
///
/// If a type `T` also implements the [`Default`] trait, `T::default().stored_tarr()` must be the
/// empty slice.
pub unsafe trait PermStorage {
    /// The type of points of the stored permutation.
    type Point: Point;

    /// The stored truncated arrangement for a permutation.
    ///
    /// Note that there is no guarantee that the returned slice is valid truncated arrangement,
    /// unless this value is wrapped within a [`Perm`].
    ///
    /// # Safety
    ///
    /// Guaranteed to not change unless a mutable reference to this value is obtained, see also the
    /// trait level documentation.
    fn stored_tarr(&self) -> &[Self::Point];
}

unsafe impl<P: Point> PermStorage for [P] {
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        &self
    }
}

unsafe impl<P: Point> PermStorage for Vec<P> {
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        &self
    }
}

unsafe impl<P, A> PermStorage for SmallVec<A>
where
    P: Point,
    A: Array<Item = P>,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        &self
    }
}

unsafe impl<P, S> PermStorage for &S
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<P, S> PermStorage for &mut S
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<P, S> PermStorage for Box<S>
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<P, S> PermStorage for Rc<S>
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<P, S> PermStorage for Arc<S>
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<'a, P: Point> PermStorage for Cow<'a, [P]> {
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        self.as_ref().stored_tarr()
    }
}

/// Values representing a permutation.
///
/// These values can be turned into a [`Perm`] via the [`to_perm`][Self::to_perm] method or by
/// passing them to [`Perm::new`].
///
/// Often when a permutation is returned, it will be some type implementing `PermExpr` instead of a
/// `Perm`. When passing such values to methods that accept a `PermExpr`, for example
/// [`PermStorageMut::assign`], this can often avoid creating intermediate copies of permutations.
///
/// In general you should avoid using a `PermExpr` in multiple places. Instead first call `to_perm`
/// and use the resulting `Perm` or assigning it to an existing `Perm` and use that. This avoids
/// potentially computing the truncated arrangement of the represented permutations multiple times.
///
/// # Safety
///
/// Any implementing type must ensure that only valid permutations are represented.
pub unsafe trait PermExpr: Sized {
    /// The type of points of the represented permutation.
    type Point: Point;

    /// Overwrite the passed reference's value with this permutation's truncated arrangement.
    ///
    /// # Safety
    ///
    /// Implementors need to ensure that `target` is in a valid state even if a panic occurs.
    fn assign_to_perm_storage<S: PermStorageMut<Point = Self::Point>>(self, target: &mut S);

    /// Obtain this permutation as a [`Perm`].
    ///
    /// This is implemented by passing `self` to [`Perm::new`].
    #[inline(always)]
    fn to_perm<S: PermStorageMut<Point = Self::Point> + Default>(self) -> Perm<S> {
        Perm::new(self)
    }

    /// Product of two permutations.
    ///
    /// The return type implements [`PermExpr`].
    ///
    /// Following the convention of computational group theory, the product of two permutations is
    /// the permutation that results by applying the the permutation on the left followed by the
    /// permutation on the right. Many other areas of mathematics have the reverse of this as
    /// convention.
    fn product<T>(self, other: T) -> Product<Self, T>
    where
        T: PermExpr<Point = Self::Point>,
    {
        Product(self, other)
    }
}

/// Types that can be used by [`Perm`] to store and modify a truncated arrangement.
///
/// This is implemented by the subset of the types implementing [`PermStorage`] that also allow
/// mutation of the stored truncated arrangement. This includes the requirement to efficiently
/// resize the truncated arrangement and thus is not implemented for mutable or boxed slices.
///
/// # Safety
///
/// Any implementing type must guarantee that [`PermStorage::stored_tarr`] always returns the
/// currently stored truncated arrangement and respects any modification done via the methods of
/// this trait.
pub unsafe trait PermStorageMut: PermStorage + Sized {
    /// Set the stored permutation.
    ///
    /// This overwrites the currently stored permutation.
    fn assign(&mut self, expr: impl PermExpr<Point = Self::Point>) {
        expr.assign_to_perm_storage(self)
    }

    /// Create a new value storing a truncated arrangement specified by a [`PermExpr`].
    fn from_expr(expr: impl PermExpr<Point = Self::Point>) -> Self
    where
        Self: Default,
    {
        let mut result = Self::default();
        result.assign(expr);
        result
    }

    /// The capacity of the buffer storing the truncated arrangement.
    fn stored_tarr_capacity(&self) -> usize;

    /// Raw mutable pointer to the start of the buffer storing the truncated arrangement.
    fn stored_tarr_mut_ptr(&mut self) -> *mut Self::Point;

    /// Resize the buffer storing the truncated arrangement to have at least a given capacity.
    ///
    /// # Safety
    ///
    /// This invalidates any values stored in the excess capacity of the buffer (values past the
    /// currently stored truncated arrangement).
    fn ensure_stored_tarr_capacity(&mut self, cap: usize);

    /// Set the length of the stored truncated arrangement.
    ///
    /// # Safety
    ///
    /// This given length must be at or below the capacity of the buffer storing the truncated
    /// arrangement. The first `len` items of the buffer must be initialized.
    ///
    /// Calling this with a `len` of zero must be safe. Users of this trait, though, should prefer
    /// calling [`clear_stored_tarr`][Self::clear_stored_tarr] over setting the length to zero if
    /// possible.
    unsafe fn set_stored_tarr_len(&mut self, len: usize);

    /// Clear the stored truncated arrangement.
    ///
    /// # Safety
    ///
    /// This invalidates the whole buffer storing the truncated arrangement. It may also change the
    /// capacity of the buffer (this is useful for copy-on-write implementations).
    fn clear_stored_tarr(&mut self) {
        unsafe { self.set_stored_tarr_len(0) }
    }

    /// Prepare overwriting the stored truncated arrangement.
    ///
    /// This clears the stored truncated arrangement, then ensure that its buffer has at least the
    /// given capacity and finally returns a raw mutable pointer to the buffer.
    ///
    /// It is equivalent to calling [`clear_stored_tarr`][Self::clear_stored_tarr],
    /// [`ensure_stored_tarr_capacity`][Self::ensure_stored_tarr_capacity] and
    /// [`stored_tarr_mut_ptr`][Self::stored_tarr_mut_ptr] in sequence, but implementing types can
    /// optimize this sequence.
    fn overwrite_stored_tarr(&mut self, cap: usize) -> *mut Self::Point {
        self.clear_stored_tarr();
        self.ensure_stored_tarr_capacity(cap);
        self.stored_tarr_mut_ptr()
    }

    /// Assign the stored truncated arrangement from a slice.
    fn set_stored_tarr_from_tarr_slice(&mut self, slice: &[Self::Point]) {
        let buffer = self.overwrite_stored_tarr(slice.len());
        // SAFETY: overwrite_stored_tarr ensures a buffer of at least the given capacity
        unsafe {
            copy_nonoverlapping(slice.as_ptr(), buffer, slice.len());
            // SAFETY: we just initialized this number of elements
            self.set_stored_tarr_len(slice.len());
        }
    }
}

unsafe impl<'a, S: PermStorageMut> PermStorageMut for &'a mut S {
    fn stored_tarr_capacity(&self) -> usize {
        (**self).stored_tarr_capacity()
    }

    fn stored_tarr_mut_ptr(&mut self) -> *mut Self::Point {
        (**self).stored_tarr_mut_ptr()
    }

    fn ensure_stored_tarr_capacity(&mut self, cap: usize) {
        (**self).ensure_stored_tarr_capacity(cap)
    }

    unsafe fn set_stored_tarr_len(&mut self, len: usize) {
        (**self).set_stored_tarr_len(len)
    }

    fn assign(&mut self, expr: impl PermExpr<Point = Self::Point>) {
        (**self).assign(expr)
    }

    fn clear_stored_tarr(&mut self) {
        (**self).clear_stored_tarr()
    }

    fn overwrite_stored_tarr(&mut self, cap: usize) -> *mut Self::Point {
        (**self).overwrite_stored_tarr(cap)
    }

    fn set_stored_tarr_from_tarr_slice(&mut self, slice: &[Self::Point]) {
        (**self).set_stored_tarr_from_tarr_slice(slice)
    }
}

macro_rules! vec_like_perm_storage_mut_impl {
    () => {
        fn stored_tarr_capacity(&self) -> usize {
            self.capacity()
        }

        fn stored_tarr_mut_ptr(&mut self) -> *mut Self::Point {
            self.as_mut_ptr()
        }

        fn ensure_stored_tarr_capacity(&mut self, cap: usize) {
            let len = self.len();
            if cap > len {
                self.reserve(cap - len)
            }
        }

        unsafe fn set_stored_tarr_len(&mut self, len: usize) {
            self.set_len(len)
        }

        fn clear_stored_tarr(&mut self) {
            self.clear();
        }

        fn set_stored_tarr_from_tarr_slice(&mut self, slice: &[Self::Point]) {
            self.clear();
            self.extend_from_slice(slice);
        }
    };
}

unsafe impl<P: Point> PermStorageMut for Vec<P> {
    vec_like_perm_storage_mut_impl!();
}

unsafe impl<P, A> PermStorageMut for SmallVec<A>
where
    P: Point,
    A: Array<Item = P>,
{
    vec_like_perm_storage_mut_impl!();
}

macro_rules! rc_like_perm_storage_mut_impl {
    ($rc:ident) => {
        fn stored_tarr_capacity(&self) -> usize {
            (**self).stored_tarr_capacity()
        }

        fn stored_tarr_mut_ptr(&mut self) -> *mut Self::Point {
            $rc::make_mut(self).stored_tarr_mut_ptr()
        }

        fn ensure_stored_tarr_capacity(&mut self, cap: usize) {
            $rc::make_mut(self).ensure_stored_tarr_capacity(cap)
        }

        unsafe fn set_stored_tarr_len(&mut self, len: usize) {
            $rc::make_mut(self).set_stored_tarr_len(len)
        }

        fn clear_stored_tarr(&mut self) {
            // If this value is shared, avoid making a copy just to clear it
            if let Some(value) = $rc::get_mut(self) {
                value.clear_stored_tarr()
            } else {
                *self = Default::default()
            }
        }
    };
}

unsafe impl<S: PermStorageMut + Clone + Default> PermStorageMut for Rc<S> {
    rc_like_perm_storage_mut_impl!(Rc);
}

unsafe impl<S: PermStorageMut + Clone + Default> PermStorageMut for Arc<S> {
    rc_like_perm_storage_mut_impl!(Arc);
}

unsafe impl<'a, P: Point> PermStorageMut for Cow<'a, [P]> {
    fn stored_tarr_capacity(&self) -> usize {
        match self {
            Cow::Borrowed(slice) => slice.len(),
            Cow::Owned(vec) => vec.stored_tarr_capacity(),
        }
    }

    fn stored_tarr_mut_ptr(&mut self) -> *mut Self::Point {
        self.to_mut().stored_tarr_mut_ptr()
    }

    fn ensure_stored_tarr_capacity(&mut self, cap: usize) {
        self.to_mut().ensure_stored_tarr_capacity(cap)
    }

    unsafe fn set_stored_tarr_len(&mut self, len: usize) {
        self.to_mut().set_stored_tarr_len(len)
    }

    fn clear_stored_tarr(&mut self) {
        match self {
            Cow::Borrowed(_) => *self = Cow::Owned(vec![]),
            Cow::Owned(vec) => vec.clear_stored_tarr(),
        }
    }
}

/// Product of two permutations.
///
/// This type stores a left and a right subexpression and implements [`PermExpr`] if it is
/// implemented by both subexpressions.
///
/// Following the convention of computational group theory, the product of two permutations is the
/// permutation that results by applying the the permutation on the left followed by the permutation
/// on the right. Many other areas of mathematics have the reverse of this as convention.
pub struct Product<L, R>(pub L, pub R);

unsafe impl<L, R> PermExpr for Product<L, R>
where
    L: PermExpr,
    R: PermExpr<Point = L::Point>,
{
    type Point = L::Point;

    fn assign_to_perm_storage<St: PermStorageMut<Point = Self::Point>>(self, target: &mut St) {
        // TODO optimize and add specialization via const-prop-time dynamic dispatch
        // For now this is a naive implementation which always performs unnecessary copies
        let tmp_l: Perm<TmpVec<_>> = self.0.to_perm();
        let tmp_r: Perm<TmpVec<_>> = self.1.to_perm();
        let tarr_l = tmp_l.tarr();
        let tarr_r = tmp_r.tarr();

        let reserve_size = tarr_l.len().max(tarr_r.len());

        let buffer = target.overwrite_stored_tarr(reserve_size);

        for (i, j) in tarr_l.iter().enumerate() {
            // This is a (hopefully) branch free way of reading tarr_r[j] if in bounds and j if out
            // of bounds.
            let point = tarr_r.get(j.as_()).unwrap_or(j);
            // SAFETY: buffer has a size of reserve_size which is >= tarr_l.len()
            unsafe {
                buffer.add(i).write(*point);
            }
        }
        for (i, j) in tarr_r.iter().enumerate().skip(tarr_l.len()) {
            // SAFETY: buffer has a size of reserve_size which is >= tarr_r.len()
            unsafe {
                buffer.add(i).write(*j);
            }
        }

        let mut tarr_len = reserve_size;
        // SAFETY: As tarr_len starts with the size of buffer and is always kept positive,
        // `tarr_len - 1` is a valid offset to read from
        unsafe {
            while tarr_len > 0 && buffer.add(tarr_len - 1).read().as_() == tarr_len - 1 {
                tarr_len -= 1;
            }
        }

        // SAFETY: tarr_len <= reserve_size and we initialized all 0..reserve_size items
        unsafe { target.set_stored_tarr_len(tarr_len) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn perm_format() {
        let x: Perm<Vec<u32>> = Perm::from_tarr(vec![1, 2, 3, 0]).unwrap();
        assert_eq!(format!("{}", x), "(0 1 2 3)");
        assert_eq!(format!("{:?}", x), "perm![(0 1 2 3)]");
        let x: Perm<Vec<u32>> = Perm::from_tarr(vec![2, 3, 4, 1, 6, 7, 0, 5]).unwrap();
        assert_eq!(format!("{}", x), "(0 2 4 6)(1 3)(5 7)");
        let x: Perm<Vec<u32>> = Perm::identity();
        assert_eq!(format!("{}", x), "()");
        assert_eq!(format!("{:?}", x), "perm![]");
    }

    #[test]
    fn perm_product() {
        let x: Perm<Vec<u32>> = Perm::from_tarr(vec![1, 2, 3, 0]).unwrap();
        let y: Perm<Vec<u32>> = Perm::from_tarr(vec![1, 2, 3, 4, 5, 6, 0]).unwrap();

        let xx: Perm<Vec<u32>> = (&x).product(&x).to_perm();
        assert_eq!(xx, Perm::from_tarr(vec![2, 3, 0, 1]).unwrap());

        let xy: Perm<Vec<u32>> = (&x).product(&y).to_perm();
        assert_eq!(xy, Perm::from_tarr(vec![2, 3, 4, 1, 5, 6, 0]).unwrap());

        let yx: Perm<Vec<u32>> = (&y).product(&x).to_perm();
        assert_eq!(yx, Perm::from_tarr(vec![2, 3, 0, 4, 5, 6, 1]).unwrap());

        let yy: Perm<Vec<u32>> = (&y).product(&y).to_perm();
        assert_eq!(yy, Perm::from_tarr(vec![2, 3, 4, 5, 6, 0, 1]).unwrap());

        let y4: Perm<Vec<u32>> = (&yy).product(&yy).to_perm();
        assert_eq!(y4, Perm::from_tarr(vec![4, 5, 6, 0, 1, 2, 3]).unwrap());

        let y6: Perm<Vec<u32>> = (&y4).product(&yy).to_perm();
        assert_eq!(y6, Perm::from_tarr(vec![6, 0, 1, 2, 3, 4, 5]).unwrap());

        let y7: Perm<Vec<u32>> = (&y6).product(&y).to_perm();
        assert!(y7.is_identity());

        let z: Perm<Vec<u32>> = Perm::from_tarr(vec![6, 0, 1, 3, 2, 4, 5]).unwrap();

        let yz: Perm<Vec<u32>> = (&y).product(&z).to_perm();
        assert_eq!(yz, Perm::from_tarr(vec![0, 1, 3, 2]).unwrap());
    }
}
