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

use crate::cycles;

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

// SAFETY: `write_into_mut_ptr(output)` completly overwrites `output` with a valid permutation of
// length `degree()`. Here we depend on `Perm` being a valid permutation to ensure we overwrite
// every entry.
unsafe impl<Pt: Point> PermVal<Pt> for Inv<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.0.degree()
    }

    #[inline]
    unsafe fn write_into_mut_ptr(self, target: *mut Pt) {
        // SAFETY: writes a valid permutation of the correct length
        unsafe { raw::write_inverse(target, self.0.as_ptr(), self.0.degree()) };
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

// SAFETY: `write_into_mut_ptr(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for Prod<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.degree
    }

    #[inline]
    unsafe fn write_into_mut_ptr(self, target: *mut Pt) {
        if self.left.degree() < self.degree {
            // SAFETY: since `self.degree` is the maximum of `self.left.degree()` and
            // `self.right.degree()`, in this case `self.right.degree()` is `self.degree` so only
            // the left permutation needs to be extended to the same degree.
            unsafe {
                raw::write_product_extend_left(
                    target,
                    self.left.as_ptr(),
                    self.left.degree(),
                    self.right.as_ptr(),
                    self.degree,
                )
            };
        } else {
            // NOTE: write_product_extend_right avoids inner loop bound checks required by
            // write_product_extend_left so it is the preferred method when all degrees are the
            // same.

            // SAFETY: since `self.degree` is the maximum of `self.left.degree()` and
            // `self.right.degree()`, in this case `self.left.degree()` is `self.degree` so only the
            // right permutation potentially needs to be extended to the same degree.
            unsafe {
                raw::write_product_extend_right(
                    target,
                    self.left.as_ptr(),
                    self.right.as_ptr(),
                    self.right.degree(),
                    self.degree,
                )
            };
        }
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

// SAFETY: `write_into_mut_ptr(output)` completly overwrites `output` with a valid permutation when
// passed a `degree()` length slice.
unsafe impl<Pt: Point> PermVal<Pt> for Pow<'_, Pt> {
    #[inline]
    fn degree(&self) -> usize {
        self.perm.degree()
    }

    #[inline]
    unsafe fn write_into_mut_ptr(self, target: *mut Pt) {
        let degree = self.degree();
        // SAFETY: overwrites `target` with a valid permutation
        unsafe {
            raw::write_power(target, self.perm.as_ptr(), degree, &self.exp);
        }
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
        Ok(self.cycles.try_build()?.build())
    }

    #[inline]
    fn try_assign_to(self, output: &mut T) -> Result<(), Self::Err> {
        self.cycles.try_build()?.assign_to(output);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exp() {
        let g: VecPerm<u16> = Perm::parse_gap(
            "(1,17,28,23,3,9,6,19,30,14)(2,27,15)(5,12,24,10,8,18,21,22,16,13,29,25,7,11,20)",
        )
        .try_build()
        .unwrap();

        let gfixed: VecPerm<u16> = g.pow(1073741827).build();

        for n in -16..16 {
            let gn: VecPerm<u16> = g.pow(n).build();
            let m = n ^ 101;
            let gm: VecPerm<u16> = g.pow(m).build();

            let glarge: VecPerm<u16> = g.pow(1073741827 - n - m).build();

            let a: VecPerm<u16> = gn.prod(&glarge).build();
            let b: VecPerm<u16> = a.prod(&gm).build();

            assert_eq!(b, gfixed);
        }
    }
}
