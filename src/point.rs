use std::{fmt, hash::Hash};

pub(crate) mod sealed {
    #[allow(clippy::missing_safety_doc)]
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

pub trait Point:
    Copy + Clone + Default + Ord + Hash + fmt::Display + fmt::Debug + sealed::Sealed + 'static
{
    const MAX_DEGREE: usize;

    #[doc(hidden)]
    const SPECIALIZE_POINT_TYPE: specialize::PointType;

    /// Returns the index of the point.
    fn index(self) -> usize;

    /// Returns the point with a given index.
    fn from_index(index: usize) -> Self;
}

macro_rules! impl_pt {
    ($($n:ident $t:ty),*) => {
        $(
            unsafe impl sealed::Sealed for $t {}

            impl Point for $t {
                const MAX_DEGREE: usize = {
                    if (<$t>::MAX as usize) < (isize::MAX as usize) {
                        (<$t>::MAX as usize)
                    } else {
                        (isize::MAX as usize)
                    }
                };

                const SPECIALIZE_POINT_TYPE: specialize::PointType = specialize::PointType::$n;

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

impl_pt!(U8 u8, U16 u16, U32 u32, U64 u64);
