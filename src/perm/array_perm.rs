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

use super::iter::AllArrayPerms;

use super::{Perm, PermVal, PermValWithTemp, StorePerm};

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

    #[inline]
    fn build_from_perm_val_with_temp<V: PermValWithTemp<Self::Point>>(
        perm: V,
        temp: &mut V::Temp,
    ) -> Self
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
            perm.write_to_slice_with_temp(new_perm, temp);
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
    fn assign_perm_val_with_temp<V: PermValWithTemp<Self::Point>>(
        &mut self,
        perm: V,
        temp: &mut V::Temp,
    ) {
        self.deref_mut().assign_perm_val_with_temp(perm, temp);
    }
}
