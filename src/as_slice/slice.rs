use super::{AsMutSlice, AsSlice};

// SAFETY: provides consistent access
unsafe impl<T> AsSlice for [T] {
    type Item = T;

    #[inline(always)]
    fn as_slice(&self) -> &[Self::Item] {
        self
    }
}

// SAFETY: provides consistent access
unsafe impl<T> AsMutSlice for [T] {
    #[inline(always)]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }
}
