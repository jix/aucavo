//! Permutation data types and algorithms.

use crate::TmpVec;
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use smallvec::{Array, SmallVec};
use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ptr::copy_nonoverlapping,
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
/// [`Box`]es, [`Rc`][std::rc::Rc]s, [`Arc`][std::sync::Arc]s, [`Cow`][std::borrow::Cow]s containing
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

impl<S: PermStorageNew> Perm<S> {
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

impl<'a, S: ?Sized> From<&'a Perm<S>> for Perm<&'a S> {
    fn from(perm: &'a Perm<S>) -> Self {
        Perm(&perm.0)
    }
}

impl<S: PermStorage + ?Sized> AsRef<Perm<[S::Point]>> for Perm<S> {
    #[inline(always)]
    fn as_ref(&self) -> &Perm<[S::Point]> {
        // SAFETY: as we get the tarr from a Perm, we don't need to check it
        unsafe { Perm::from_tarr_unchecked(self.tarr()).into() }
    }
}

impl<S: PermStorageNew> Default for Perm<S> {
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
    unsafe fn write_tarr_to_buffer(self, reserve: impl FnOnce(usize) -> *mut Self::Point) -> usize {
        self.as_ref().write_tarr_to_buffer(reserve)
    }
}

unsafe impl<S: PermStorage + ?Sized> PermExpr for &Perm<S> {
    type Point = S::Point;

    unsafe fn write_tarr_to_buffer(self, reserve: impl FnOnce(usize) -> *mut Self::Point) -> usize {
        let tarr = self.0.stored_tarr();
        let dst = reserve(tarr.len());
        copy_nonoverlapping(tarr.as_ptr(), dst, tarr.len());
        tarr.len()
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

unsafe impl<P, S> PermStorage for std::rc::Rc<S>
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<P, S> PermStorage for std::sync::Arc<S>
where
    P: Point,
    S: PermStorage<Point = P> + ?Sized,
{
    type Point = P;

    fn stored_tarr(&self) -> &[Self::Point] {
        S::stored_tarr(self)
    }
}

unsafe impl<'a, P: Point> PermStorage for std::borrow::Cow<'a, [P]> {
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

    /// Writes the truncated permutation to a buffer.
    ///
    /// *Note:* Unless you wish to implement this trait, [`PermStorageNew`] or [`PermStorageMut`]
    /// for a custom type, you will not need to use this method directly.
    ///
    /// The method is passed a `reserve` function which, given a size, must return a raw pointer to
    /// an uninitialized buffer of at least that size. Then this method writes the truncated
    /// arrangement into that buffer. Finally it returns the actual size of the truncated
    /// arrangement, which must be less than or equal to the buffer size it requested using
    /// `reserve`.
    ///
    /// If `write_tarr_to_buffer` returns 0, it is allowed (but not required) for this method to not
    /// call `reserve`.
    ///
    /// # Safety
    ///
    /// A caller of this method must ensure that the passed `reserve` value returns a buffer of the
    /// correct size or panics.
    ///
    /// An implementing type must ensure to initialize the buffer with a valid truncated arrangement
    /// of the size it returns.
    unsafe fn write_tarr_to_buffer(self, reserve: impl FnOnce(usize) -> *mut Self::Point) -> usize;

    /// Obtain the represented permutation as a [`Perm`].
    ///
    /// This is implemented by passing `self` to [`Perm::new`].
    #[inline(always)]
    fn to_perm<St: PermStorageNew<Point = Self::Point>>(self) -> Perm<St> {
        Perm::new(self)
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
pub unsafe trait PermStorageMut: PermStorage {
    /// Set the stored permutation.
    ///
    /// This overwrites the currently stored permutation.
    fn assign(&mut self, expr: impl PermExpr<Point = Self::Point>);
}

unsafe impl<Pt: Point> PermStorageMut for Vec<Pt> {
    fn assign(&mut self, expr: impl PermExpr<Point = Self::Point>) {
        unsafe {
            let length = expr.write_tarr_to_buffer(|capacity| {
                self.clear();
                self.reserve(capacity);
                self.as_mut_ptr()
            });
            debug_assert!(length <= self.capacity());
            self.set_len(length);
        }
    }
}

/// Types that can be used as storage for new [`Perm`] values.
///
/// This is a subset of the types implementing [`PermStorageMut`], as this comes with the additional
/// requirement of implementing `Default`.
///
/// # Safety
///
/// Any implementing type must guarantee that [`PermStorage::stored_tarr`] initially returns the
/// truncated assignment specified when creating values via this trait.
pub unsafe trait PermStorageNew: PermStorageMut + Default {
    /// Create a new value storing a given truncated arrangement.
    fn from_expr(expr: impl PermExpr<Point = Self::Point>) -> Self {
        let mut result = Self::default();
        result.assign(expr);
        result
    }
}

unsafe impl<P: Point> PermStorageNew for Vec<P> {}

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
}
