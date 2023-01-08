//! Points in finite structures.
use std::{fmt, hash::Hash, ops::Range};

pub(crate) mod sealed {
    /// # Safety
    /// No other implementations than the one in this file are allowed.
    pub unsafe trait Sealed {}
}

pub(crate) mod specialize {

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub enum PointType {
        P8,
        P16,
        P32,
        P64,
    }
}

use crate::as_slice::AsSlice;

#[cfg(not(any(target_pointer_width = "64", target_pointer_width = "32")))]
compile_error!(
    r#"The aucavo crate only supports target_pointer_width = "32" and target_pointer_width = "64""#
);

/// Unsigned primitive integer types used to represent points in finite structures (e.g.
/// permutations).
///
/// This type should only be implemented for unsigned primitive integer types. To enforce this, this
/// trait is sealed.
pub trait Point: Copy + Clone + Default + Ord + Hash + sealed::Sealed + 'static {
    /// The underlying integer type.
    ///
    /// A `Point` is a `#[repr(transparent)]` wrapper of this type.
    type IntRepr;

    /// Maximal number of points in a finite structure using this type as point representation.
    ///
    /// It is possible to construct `Point` values whose index is at or above `MAX_DEGREE`.
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
    ($($doc:literal $n:ident $t:ty),*) => {
        $(
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
            #[repr(transparent)]
            #[doc = concat!("A point type represented using ", $doc, "-bit integers.")]
            pub struct $n($t);

            // SAFETY: this is the single intended place implementing this trait.
            unsafe impl sealed::Sealed for $n {}

            impl fmt::Display for $n {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    fmt::Display::fmt(&self.index(), f)
                }
            }

            impl Point for $n {
                type IntRepr = $t;

                const MAX_DEGREE: usize = {
                    if (<$t>::MAX as usize) < (isize::MAX as usize) / std::mem::size_of::<$t>() {
                        (<$t>::MAX as usize).wrapping_add(1)
                    } else {
                        ((isize::MAX as usize) / std::mem::size_of::<$t>())
                    }
                };

                const SPECIALIZE_POINT_TYPE: specialize::PointType = specialize::PointType::$n;

                #[inline(always)]
                fn index(self) -> usize {
                    self.0 as usize
                }

                #[inline(always)]
                fn from_index(index: usize) -> Self {
                    Self(index as $t)
                }
            }
        )*
    };
}

impl_pt!("8" P8 u8);
impl_pt!("16" P16 u16);
impl_pt!("32" P32 u32);

#[cfg(target_pointer_width = "64")]
impl_pt!("64" P64 u64);

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

/// A value referencing or storing a slice of points.
pub trait AsPointSlice: AsSlice<Item = Self::Pt> {
    /// Type of the stored points.
    type Pt: Point;
}

impl<T> AsPointSlice for T
where
    T: AsSlice + ?Sized,
    T::Item: Point,
{
    type Pt = T::Item;
}
