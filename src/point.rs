//! Points in finite structures.
use std::{fmt, hash::Hash, num::ParseIntError, ops::Range, str::FromStr};

pub(crate) mod sealed {
    /// # Safety
    /// No other implementations than the one in this file are allowed.
    pub unsafe trait Sealed {}
}

pub(crate) mod specialize {

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub enum PointType {
        U8,
        U16,
        U32,
        U64,
    }
}

use specialize::PointType::*;

#[cfg(not(any(target_pointer_width = "64", target_pointer_width = "32")))]
compile_error!(
    r#"The aucavo crate only supports target_pointer_width = "32" and target_pointer_width = "64""#
);

/// Unsigned primitive integer types used to represent points in finite structures (e.g.
/// permutations).
///
/// This type should only be implemented for unsigned primitive integer types. To enforce this, this
/// trait is sealed.
pub trait Point:
    Copy
    + Clone
    + Default
    + Ord
    + Hash
    + FromStr<Err = ParseIntError>
    + fmt::Display
    + fmt::Debug
    + sealed::Sealed
    + 'static
{
    /// Maximal number of points in a finite structure using this type as point representation.
    const MAX_DEGREE: usize;

    #[doc(hidden)]
    const SPECIALIZE_POINT_TYPE: specialize::PointType;

    /// Returns the index of the point.
    ///
    /// The index is equal to the point but always a `usize`.
    fn index(self) -> usize;

    /// Returns the point with a given index.
    ///
    /// The index is equal to the point but always a `usize`. If the passed index is larger than
    /// [`Self::MAX_DEGREE`] an arbitrary but valid point is returned.
    fn from_index(index: usize) -> Self;
}

macro_rules! impl_pt {
    ($($n:ident $t:ty),*) => {
        $(
            // SAFETY: this is the single intended place implementing this trait.
            unsafe impl sealed::Sealed for $t {}

            impl Point for $t {
                const MAX_DEGREE: usize = {
                    if (<$t>::MAX as usize) < (isize::MAX as usize) / std::mem::size_of::<$t>() {
                        (<$t>::MAX as usize).wrapping_add(1)
                    } else {
                        ((isize::MAX as usize) / std::mem::size_of::<$t>())
                    }
                };

                const SPECIALIZE_POINT_TYPE: specialize::PointType = $n;

                #[inline(always)]
                fn index(self) -> usize {
                    self as usize
                }

                #[inline(always)]
                fn from_index(index: usize) -> Self {
                    index as $t
                }
            }
        )*
    };
}

impl_pt!(U8 u8, U16 u16, U32 u32);

#[cfg(target_pointer_width = "64")]
impl_pt!(U64 u64);

/// Iterator over a consecutive range of points.
pub type PointRange<Pt> = PointIter<Pt, Range<usize>>;

/// Iterator wrapper that turns an iterator over indices into an iterator over points.
pub struct PointIter<Pt, I> {
    indices: I,
    _phantom: std::marker::PhantomData<Pt>,
}

impl<Pt, I> PointIter<Pt, I> {
    /// Returns an iterator over the point's indices.
    pub fn indices(self) -> I {
        self.indices
    }
}

impl<Pt, I> PointIter<Pt, I> {
    /// Retturns an iterator over the points of the given indices.
    pub fn new(indices: I) -> Self {
        Self {
            indices,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<Pt: Point, I: Iterator<Item = usize>> Iterator for PointIter<Pt, I> {
    type Item = Pt;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(Pt::from_index)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.indices.size_hint()
    }
}

impl<Pt: Point, I: DoubleEndedIterator<Item = usize>> DoubleEndedIterator for PointIter<Pt, I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.indices.next_back().map(Pt::from_index)
    }
}

impl<Pt: Point, I: ExactSizeIterator<Item = usize>> ExactSizeIterator for PointIter<Pt, I> {
    #[inline]
    fn len(&self) -> usize {
        self.indices.len()
    }
}
