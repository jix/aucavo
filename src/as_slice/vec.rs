use std::mem::MaybeUninit;

use super::{
    AsMutSlice, AsSlice, DynSlice, NewSlice, ReserveSlice, SpecializeAsDynSlice,
    SpecializeAsNewSlice, SpecializeAsReserveSlice,
};

// SAFETY: provides consistent access
unsafe impl<T> AsSlice for Vec<T> {
    type Item = T;

    #[inline(always)]
    fn as_slice(&self) -> &[Self::Item] {
        self
    }
}

// SAFETY: provides consistent access
unsafe impl<T> AsMutSlice for Vec<T> {
    #[inline(always)]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }

    specialize_impl!(specialize_as_dyn_slice: SpecializeAsDynSlice);
    specialize_impl!(specialize_as_reserve_slice: SpecializeAsReserveSlice);
    specialize_impl!(specialize_as_new_slice: SpecializeAsNewSlice);
}

// SAFETY: provides consistent access
unsafe impl<T> DynSlice for Vec<T> {
    #[inline]
    unsafe fn resize_with(
        &mut self,
        new_len: usize,
        pre: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
        post: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
    ) {
        let len = self.len();

        if new_len > len {
            self.reserve(new_len - len);
        }

        // SAFETY: setting len to 0 is always safe (worst case it leaks items)
        unsafe { self.set_len(0) };
        debug_assert!(self.spare_capacity_mut().len() >= len.max(new_len));
        // SAFETY: we didn't shrink the vec, so the capacity is at least the old len
        pre(unsafe { self.spare_capacity_mut().get_unchecked_mut(..len) });
        // SAFETY: if the new_len is larger, we reserved sufficient capacity abive
        post(unsafe { self.spare_capacity_mut().get_unchecked_mut(..new_len) });
        // SAFETY: we require `post` to fully initialize the slice (and it has this length)
        unsafe { self.set_len(new_len) };
    }

    // TODO optimized replace_with implementation
}

// SAFETY: provides consistent access
unsafe impl<T> ReserveSlice for Vec<T> {
    #[inline(always)]
    fn reserve(&mut self, additional: usize) {
        Vec::reserve(self, additional)
    }

    #[inline(always)]
    fn capacity(&self) -> usize {
        Vec::capacity(self)
    }
}

// SAFETY: provides consistent access
unsafe impl<T> NewSlice for Vec<T> {
    unsafe fn new_with(len: usize, init: impl FnOnce(&mut [MaybeUninit<Self::Item>])) -> Self {
        let mut new = Vec::with_capacity(len);
        init(new.spare_capacity_mut());
        // SAFETY: we require `init` to fully initialize its argument slice
        unsafe { new.set_len(len) };
        new
    }
}
