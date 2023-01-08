use std::{rc::Rc, sync::Arc};

use super::{
    AsMutSlice, AsSlice, DynSlice, NewSlice, ReserveSlice, SpecializeAsDynSlice,
    SpecializeAsNewSlice, SpecializeAsReserveSlice,
};

// SAFETY: provides consistent access if T does
unsafe impl<T: AsSlice + ?Sized> AsSlice for &T {
    type Item = T::Item;

    #[inline(always)]
    fn as_slice(&self) -> &[Self::Item] {
        T::as_slice(self)
    }
}

// SAFETY: provides consistent access if T does
unsafe impl<T: AsSlice + ?Sized> AsSlice for &mut T {
    type Item = T::Item;

    #[inline(always)]
    fn as_slice(&self) -> &[Self::Item] {
        T::as_slice(self)
    }
}

// SAFETY: provides consistent access if T does
unsafe impl<'a, T: AsMutSlice + ?Sized + 'a> AsMutSlice for &'a mut T {
    #[inline(always)]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        T::as_mut_slice(self)
    }

    specialize_forward!(
        ['a, T: ?Sized + 'a] [&'a mut T]
        specialize_as_dyn_slice: SpecializeAsDynSlice: DynSlice
    );
    specialize_forward!(
        ['a, T: ?Sized + 'a] [&'a mut T]
        specialize_as_reserve_slice: SpecializeAsReserveSlice: ReserveSlice
    );
}

// SAFETY: provides consistent access if T does
unsafe impl<T: DynSlice + ?Sized> DynSlice for &mut T {
    #[inline(always)]
    unsafe fn resize_with(
        &mut self,
        new_len: usize,
        pre: impl FnOnce(&mut [std::mem::MaybeUninit<Self::Item>]),
        post: impl FnOnce(&mut [std::mem::MaybeUninit<Self::Item>]),
    ) {
        // SAFETY: same safety requirements
        unsafe { T::resize_with(self, new_len, pre, post) }
    }

    #[inline(always)]
    unsafe fn replace_with(
        &mut self,
        new_len: usize,
        init: impl FnOnce(&mut [std::mem::MaybeUninit<Self::Item>]),
    ) {
        // SAFETY: same safety requirements
        unsafe { T::replace_with(self, new_len, init) }
    }
}

// SAFETY: provides consistent access if T does
unsafe impl<T: ReserveSlice + ?Sized> ReserveSlice for &mut T {
    #[inline(always)]
    fn reserve(&mut self, additional: usize) {
        T::reserve(self, additional)
    }

    #[inline(always)]
    fn capacity(&self) -> usize {
        T::capacity(self)
    }
}

macro_rules! impl_smart_ptr {
    ($name:ident, $mut_access:path $(, $($mut_bounds:tt)*)?) => {
        // SAFETY: provides consistent access if T does
        unsafe impl<T: AsSlice + Sized> AsSlice for $name<T> {
            type Item = T::Item;

            #[inline(always)]
            fn as_slice(&self) -> &[Self::Item] {
                T::as_slice(self)
            }
        }

        // SAFETY: provides consistent access if T does
        unsafe impl<T: AsMutSlice + Sized $(+ $($mut_bounds)*)?> AsMutSlice for $name<T> {
            #[inline(always)]
            fn as_mut_slice(&mut self) -> &mut [Self::Item] {
                T::as_mut_slice($mut_access(self))
            }

            specialize_forward!(
                [Target: Sized $(+ $($mut_bounds)*)?] [$name<Target>]
                specialize_as_dyn_slice: SpecializeAsDynSlice: DynSlice
            );
            specialize_forward!(
                [Target: Sized $(+ $($mut_bounds)*)?] [$name<Target>]
                specialize_as_reserve_slice: SpecializeAsReserveSlice: ReserveSlice
            );
            specialize_forward!(
                [Target: Sized $(+ $($mut_bounds)*)?] [$name<Target>]
                specialize_as_new_slice: SpecializeAsNewSlice: NewSlice
            );
        }

        // SAFETY: provides consistent access if T does
        unsafe impl<T: DynSlice + Sized $(+ $($mut_bounds)*)?> DynSlice for $name<T> {
            #[inline(always)]
            unsafe fn resize_with(
                &mut self,
                new_len: usize,
                pre: impl FnOnce(&mut [std::mem::MaybeUninit<Self::Item>]),
                post: impl FnOnce(&mut [std::mem::MaybeUninit<Self::Item>]),
            ) {
                // SAFETY: same safety requirements
                unsafe { T::resize_with($mut_access(self), new_len, pre, post) }
            }

            // TODO optimized replace_with that avoids making copies just to overwrite them
            // completely immediately after that
        }

        // SAFETY: provides consistent access if T does
        unsafe impl<T: ReserveSlice + Sized $(+ $($mut_bounds)*)?> ReserveSlice for $name<T> {
            #[inline(always)]
            fn reserve(&mut self, additional: usize) {
                T::reserve($mut_access(self), additional)
            }

            #[inline(always)]
            fn capacity(&self) -> usize {
                T::capacity(self)
            }
        }

        // SAFETY: provides consistent access if T does
        unsafe impl<T: NewSlice + Sized> NewSlice for $name<T> {
            #[inline(always)]
            unsafe fn new_with(
                len: usize,
                init: impl FnOnce(&mut [std::mem::MaybeUninit<Self::Item>]),
            ) -> Self {
                // SAFETY: same safety requirements
                unsafe { $name::new(T::new_with(len, init)) }
            }
        }
    };
}

impl_smart_ptr!(Box, Box::as_mut);
impl_smart_ptr!(Rc, Rc::make_mut, Clone);
impl_smart_ptr!(Arc, Arc::make_mut, Clone);
