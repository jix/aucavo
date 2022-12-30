use std::{
    borrow::Borrow,
    cmp, fmt, hash,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use smallvec::SmallVec;

use crate::{
    cycles::{self},
    gap,
    inplace::Inplace,
    point::Point,
};

use super::{raw::MaybeUninitPerm, Perm, StorePerm};

/// Owned permutation backed by a [`SmallVec`].
///
/// Most functionality is provided via the [`Deref`] implementation to [`Perm`].
#[derive(Default)]
pub struct SmallPerm<Pt: Point, const N: usize> {
    // SAFETY: must always be a valid permutation.
    vec: SmallVec<[Pt; N]>,
}

impl<Pt: Point, const N: usize> Deref for SmallPerm<Pt, N> {
    type Target = Perm<Pt>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: `SmallPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_slice_unchecked(self.vec.as_slice()) }
    }
}

impl<Pt: Point, const N: usize> DerefMut for SmallPerm<Pt, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `SmallPerm`, like `Perm` always holds a valid permutation.
        unsafe { Perm::from_mut_slice_unchecked(self.vec.as_mut_slice()) }
    }
}

impl<Pt: Point, const N: usize> fmt::Display for SmallPerm<Pt, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

impl<Pt: Point, const N: usize> gap::FmtGap for SmallPerm<Pt, N> {
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt_gap(f)
    }
}

impl<Pt: Point, const N: usize> fmt::Debug for SmallPerm<Pt, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), f)
    }
}

impl<Pt: Point, const N: usize> FromStr for SmallPerm<Pt, N> {
    type Err = cycles::ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Perm::parse(s).try_build()
    }
}

impl<Pt: Point, const N: usize> gap::FromGapStr for SmallPerm<Pt, N> {
    type Err = cycles::ParseError;

    fn from_gap_str(s: &str) -> Result<Self, Self::Err> {
        Perm::parse_gap(s).try_build()
    }
}

impl<Pt: Point, const N: usize> Borrow<Perm<Pt>> for SmallPerm<Pt, N> {
    #[inline]
    fn borrow(&self) -> &Perm<Pt> {
        self.deref()
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized, const N: usize> PartialEq<Rhs>
    for SmallPerm<Pt, N>
{
    #[inline]
    fn eq(&self, other: &Rhs) -> bool {
        self.deref().eq(other.borrow())
    }
}

impl<Pt: Point, Rhs: Borrow<Perm<Pt>> + ?Sized, const N: usize> PartialOrd<Rhs>
    for SmallPerm<Pt, N>
{
    #[inline]
    fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
        Some(self.deref().cmp(other.borrow()))
    }
}

impl<Pt: Point, const N: usize> Eq for SmallPerm<Pt, N> {}

impl<Pt: Point, const N: usize> Ord for SmallPerm<Pt, N> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<Pt: Point, const N: usize> hash::Hash for SmallPerm<Pt, N> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<Pt: Point, const N: usize> SmallPerm<Pt, N> {
    /// Returns a new `SmallPerm` initialized to the identity permutation.
    #[inline]
    pub fn identity() -> Self {
        Self::default()
    }

    /// Returns a new `SmallPerm` initialized to the identity permutation.
    #[inline]
    pub fn identity_with_degree(degree: usize) -> Self {
        assert!(degree <= Pt::MAX_DEGREE);
        // SAFETY: initializes with a valid permutation
        Self {
            vec: (0..degree).map(Pt::from_index).collect(),
        }
    }
}

/// Allocates new storage when assigning a permutation with a larger degree than the existing value.
///
/// The implementation uses `reserve_exact` to only allocate as much memory as required. While this
/// saves memory for typical uses cases involving permutations, it can cause quadratic runtime when
/// gorwing the degree of a permutation one at a time.
// SAFETY: See `StorePerm`'s safety section for details
unsafe impl<Pt: Point, const N: usize> StorePerm for SmallPerm<Pt, N> {
    type Point = Pt;
    type Uninit = Self;

    #[inline]
    unsafe fn new_uninit_with_degree(degree: usize) -> Self::Uninit
    where
        Self: Sized,
    {
        Self {
            vec: SmallVec::with_capacity(degree),
        }
    }

    #[inline]
    unsafe fn prepare_new_uninit_with_degree(
        uninit: &mut Self::Uninit,
        degree: usize,
    ) -> &mut MaybeUninitPerm<Self::Point>
    where
        Self: Sized,
    {
        // SAFETY: we used `with_capacity(degree)` above to allocate sufficient storage and
        // `StorePerm` guarantees we get such a value in `uninit` and are called with matching
        // `degree`. `StorePerm` also guarantees that `degree` does not exceed `Pt::MAX_DEGREE`.
        unsafe {
            MaybeUninitPerm::from_mut_slice_unchecked(std::slice::from_raw_parts_mut(
                uninit.vec.as_mut_ptr() as *mut MaybeUninit<Pt>,
                degree,
            ))
        }
    }

    #[inline]
    unsafe fn assume_new_init(mut uninit: Self::Uninit, degree: usize) -> Self
    where
        Self: Sized,
    {
        // SAFETY: `StorePerm` guarantees that we prepared `uninit` with enough capacity and that it
        // was subsequently initialized with a valid permutation
        unsafe { uninit.vec.set_len(degree) };
        uninit
    }

    #[inline]
    unsafe fn prepare_assign_with_degree(
        &mut self,
        degree: usize,
    ) -> &mut super::raw::MaybeUninitPerm<Self::Point> {
        self.vec.clear();
        self.vec.reserve_exact(degree);
        // SAFETY: after clearing and reserving storage, the requirements here are the same as for
        // `prepare_new_uninit_with_degree`.
        unsafe { Self::prepare_new_uninit_with_degree(self, degree) }
    }

    #[inline]
    unsafe fn assume_assign_init(&mut self, degree: usize) {
        // SAFETY: `StorePerm` guarantees that we prepared `self` with enough capacity and that it
        // was subsequently initialized with a valid permutation
        unsafe { self.vec.set_len(degree) };
    }
}
