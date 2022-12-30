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

use crate::{cycles, inplace::InplaceWithTemp};

use super::*;

/// Inverse of a permutation.
///
/// See [`Perm::inv`].
pub struct Inv<'a, Pt: Point>(&'a Perm<Pt>);

impl<'a, Pt: Point> Inv<'a, Pt> {
    /// Returns the inverse of a permutation.
    ///
    /// See [`Perm::inv`].
    #[inline]
    pub fn new(perm: &'a Perm<Pt>) -> Self {
        Self(perm)
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice. Here we depend on `Perm` being a valid permutation to
// ensure we overwrite every entry.
unsafe impl<Pt: Point> PermVal<Pt> for Inv<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.0.degree()
    }

    #[inline]
    unsafe fn write_into(self, output: &mut MaybeUninitPerm<Pt>) {
        raw::write_inverse_same_degree(output, self.0);
    }
}

/// Product of two permutations.
///
/// See [`Perm::prod`].
pub struct Prod<'a, Pt: Point> {
    degree: usize,
    left: &'a Perm<Pt>,
    right: &'a Perm<Pt>,
}

impl<'a, Pt: Point> Prod<'a, Pt> {
    /// Returns the product of two permutations.
    ///
    /// See [`Perm::prod`].
    #[inline]
    pub fn new(left: &'a Perm<Pt>, right: &'a Perm<Pt>) -> Self {
        Prod {
            degree: left.degree().max(right.degree()),
            left,
            right,
        }
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for Prod<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.degree
    }

    #[inline]
    unsafe fn write_into(self, output: &mut MaybeUninitPerm<Pt>) {
        raw::write_product(output, self.left, self.right);
    }
}

/// Power of a permutations.
///
/// See [`Perm::pow`].
pub struct Pow<'a, Pt: Point> {
    perm: &'a Perm<Pt>,
    exp: isize,
}

impl<'a, Pt: Point> Pow<'a, Pt> {
    /// Returns the power of a permutations.
    ///
    /// See [`Perm::pow`].
    #[inline]
    pub fn new(perm: &'a Perm<Pt>, exp: isize) -> Self {
        Pow { perm, exp }
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for Pow<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.perm.degree()
    }

    #[inline]
    unsafe fn write_into(self, _output: &mut MaybeUninitPerm<Pt>) {
        // unsafe { self.write_to_slice_with_temp(output, &mut Default::default()) }
        todo!()
    }
}

// SAFETY: `write_to_slice(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermValWithTemp<Pt> for Pow<'_, Pt> {
    type Temp = SmallPerm<Pt, 128>;

    #[inline]
    unsafe fn write_into_with_temp(
        self,
        _output: &mut MaybeUninitPerm<Pt>,
        _temp: &mut Self::Temp,
    ) {
        if self.exp != 0 {
            todo!()
        }
        todo!()
    }
}

/// Disambiguator for the [`Inplace`] impl of [`Parse`].
pub enum ParseInplace {}

/// Parses a permutation from a cycle decomposition.
///
/// See [`Perm::parse`] and [`Perm::parse_gap`].
pub struct Parse<'a, Pt: Point> {
    cycles: cycles::Parse<'a, Pt>,
}

impl<'a, Pt: Point> Parse<'a, Pt> {
    /// Parses a permutation from a cycle decomposition.
    ///
    /// See [`Perm::parse`].
    #[inline]
    pub fn new(s: &'a (impl AsRef<[u8]> + ?Sized)) -> Self {
        Self {
            cycles: cycles::Cycles::parse_decomposition(s),
        }
    }

    /// Parses a permutation from a cycle decomposition.
    ///
    /// See [`Perm::parse_gap`].
    #[inline]
    pub fn gap(s: &'a (impl AsRef<[u8]> + ?Sized)) -> Self {
        Self {
            cycles: cycles::Cycles::parse_gap(s),
        }
    }
}

impl<T: StorePerm + ?Sized> Inplace<T, ParseInplace> for Parse<'_, T::Point> {
    type Err = cycles::ParseError;

    #[inline]
    fn try_build(self) -> Result<T, Self::Err>
    where
        T: Sized,
    {
        self.try_build_with_temp(&mut Default::default())
    }

    #[inline]
    fn try_assign_to(self, output: &mut T) -> Result<(), Self::Err> {
        self.try_assign_to_with_temp(output, &mut Default::default())
    }
}

impl<T: StorePerm + ?Sized> InplaceWithTemp<T, ParseInplace> for Parse<'_, T::Point> {
    type Temp = (cycles::Cycles<T::Point>, SmallVec<[bool; 256]>);

    #[inline]
    fn try_build_with_temp(self, temp: &mut Self::Temp) -> Result<T, Self::Err>
    where
        T: Sized,
    {
        self.cycles
            .try_assign_to_with_temp(&mut temp.0, &mut temp.1)?;
        Ok(temp.0.build())
    }

    #[inline]
    fn try_assign_to_with_temp(
        self,
        output: &mut T,
        temp: &mut Self::Temp,
    ) -> Result<(), Self::Err> {
        self.cycles
            .try_assign_to_with_temp(&mut temp.0, &mut temp.1)?;
        temp.0.assign_to(output);
        Ok(())
    }
}
