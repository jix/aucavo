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

use super::{Perm, PermVal, PermValWithTemp, StorePerm};

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

impl<Pt: Point> fmt::Display for VecPerm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

impl<Pt: Point> gap::FmtGap for VecPerm<Pt> {
    fn fmt_gap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt_gap(f)
    }
}

impl<Pt: Point> fmt::Debug for VecPerm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), f)
    }
}

impl<Pt: Point> FromStr for VecPerm<Pt> {
    type Err = cycles::ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Perm::parse(s).try_build()
    }
}

impl<Pt: Point> gap::FromGapStr for VecPerm<Pt> {
    type Err = cycles::ParseError;

    fn from_gap_str(s: &str) -> Result<Self, Self::Err> {
        Perm::parse_gap(s).try_build()
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

    #[inline]
    fn build_from_perm_val_with_temp<V: PermValWithTemp<Self::Point>>(
        perm: V,
        temp: &mut V::Temp,
    ) -> Self
    where
        Self: Sized,
    {
        let degree = perm.degree();
        let mut vec = Vec::with_capacity(degree);

        // SAFETY: `get_unchecked_mut` is in bounds as we reserved sufficient capacity, `set_len` is
        // allowed as `PermVal` guarantees that `write_to_slice` writes a fully initialized valid
        // permutation when the passed slice has the requested size.
        unsafe {
            perm.write_to_slice_with_temp(
                vec.spare_capacity_mut().get_unchecked_mut(..degree),
                temp,
            );
            vec.set_len(degree);
        }

        Self { vec }
    }

    #[inline]
    fn assign_perm_val_with_temp<V: PermValWithTemp<Self::Point>>(
        &mut self,
        perm: V,
        temp: &mut V::Temp,
    ) {
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
            perm.write_to_slice_with_temp(data.get_unchecked_mut(..degree), temp);

            for p in data.get_unchecked_mut(degree..new_degree) {
                *p = MaybeUninit::new(Pt::from_index(degree));
                degree += 1;
            }

            self.vec.set_len(new_degree);
        }
    }
}
