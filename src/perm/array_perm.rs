use std::{
    borrow::Borrow,
    cmp, fmt, hash,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use crate::{
    cycles::{self},
    gap,
    inplace::Inplace,
    point::Point,
};

use super::{iter::AllArrayPerms, raw};

use super::{Perm, StorePerm};

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

impl<Pt: Point, const N: usize> fmt::Display for ArrayPerm<Pt, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

impl<Pt: Point, const N: usize> gap::FmtGap for ArrayPerm<Pt, N> {
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt_gap(f)
    }
}

impl<Pt: Point, const N: usize> fmt::Debug for ArrayPerm<Pt, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), f)
    }
}

impl<Pt: Point, const N: usize> FromStr for ArrayPerm<Pt, N> {
    type Err = cycles::ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Perm::parse(s).try_build()
    }
}

impl<Pt: Point, const N: usize> gap::FromGapStr for ArrayPerm<Pt, N> {
    type Err = cycles::ParseError;

    fn from_gap_str(s: &str) -> Result<Self, Self::Err> {
        Perm::parse_gap(s).try_build()
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

/// Panics when assigning a permutation with a larger degree than `N`.
// SAFETY: See `StorePerm`'s safety section for details
unsafe impl<Pt: Point, const N: usize> StorePerm for ArrayPerm<Pt, N> {
    type Point = Pt;
    type Uninit = MaybeUninit<[Pt; N]>;

    #[inline]
    unsafe fn new_uninit_with_degree(degree: usize) -> Self::Uninit
    where
        Self: Sized,
    {
        assert!(N <= Pt::MAX_DEGREE);
        assert!(degree <= N);
        MaybeUninit::uninit()
    }

    #[inline]
    unsafe fn prepare_new_uninit_with_degree(
        uninit: &mut Self::Uninit,
        degree: usize,
    ) -> *mut Self::Point
    where
        Self: Sized,
    {
        let target = uninit.as_mut_ptr() as *mut Self::Point;
        // SAFETY: initializes padding for excess points not written by the caller
        unsafe { raw::write_identity_padding(target, degree, N) };
        target
    }

    #[inline]
    unsafe fn assume_new_init(uninit: Self::Uninit, _degree: usize) -> Self
    where
        Self: Sized,
    {
        // SAFETY: `StorePerm` requires that `0..degree` was initialized, we initialized `degree..N`
        // in `prepare_new_uninit_with_degree` via `pad_from_degree`.
        unsafe {
            Self {
                array: uninit.assume_init(),
            }
        }
    }

    #[inline]
    unsafe fn prepare_assign_with_degree(&mut self, degree: usize) -> *mut Self::Point {
        assert!(N <= Pt::MAX_DEGREE);
        assert!(degree <= N);

        let target = self.array.as_mut_ptr();
        // SAFETY: initializes padding for excess points not written by the caller
        unsafe { raw::write_identity_padding(target, degree, N) };
        target
    }

    #[inline]
    unsafe fn assume_assign_init(&mut self, _degree: usize) {}
}
