//! Traits for tyypes storing or referencing slices.
//!
//! # Safety
//! Implementations of the traits in [`as_slice`][`self`] must provide a consistent access of a
//! single slice. This means that consecutive trait method calls refer to the same slice with the
//! same content, apart from the changes performed as documented in the trait or directly performed
//! on the returned slice. This restriction applies to the slice's content, implementations are
//! allowed to move the slice in memory.

use std::mem::MaybeUninit;

specialize_trait!(
    #[doc(hidden)]
    SpecializeAsDynSlice: DynSlice
);
specialize_trait!(
    #[doc(hidden)]
    SpecializeAsReserveSlice: ReserveSlice
);
specialize_trait!(
    #[doc(hidden)]
    SpecializeAsNewSlice: NewSlice
);

/// Types storing or referencing a slice.
///
/// # Safety
/// See the module level safety section for [`as_slice`][`self`].
pub unsafe trait AsSlice {
    /// The type of slice elements.
    type Item: Sized;

    /// Returns the slice.
    fn as_slice(&self) -> &[Self::Item];
}

/// Types storing or referencing a mutable slice.
///
/// # Safety
/// See the module level safety section for [`as_slice`][`self`].
pub unsafe trait AsMutSlice: AsSlice {
    /// Returns the mutable slice.
    fn as_mut_slice(&mut self) -> &mut [Self::Item];

    specialize_dispatcher!(
        #[doc(hidden)]
        specialize_as_dyn_slice: SpecializeAsDynSlice
    );
    specialize_dispatcher!(
        #[doc(hidden)]
        specialize_as_reserve_slice: SpecializeAsReserveSlice
    );
    specialize_dispatcher!(
        #[doc(hidden)]
        specialize_as_new_slice: SpecializeAsNewSlice
    );
}

/// Types storing or referencing a resizable mutable slice.
///
/// # Safety
/// See the module level safety section for [`as_slice`][`self`].
pub unsafe trait DynSlice: AsMutSlice {
    /// Resizes the slice with using caller-supplied closures to resize the slice contents.
    ///
    /// The `pre` closure is called with the current slice and is responsible for dropping any
    /// excess contents. It may leave all elements in an uninitialized state.
    ///
    /// The `post` closure is called on the resized slice. The resized slice contains as much of the
    /// slice in the state left by `pre` as does fit within the new length, followed by
    /// uninitialized elements. The `post` closure has leave a fully initialized slice.
    ///
    /// When either closure panics and the program unwinds out of `resize_with` implementations have
    /// to reset the slice to the empty slice, leaking any potentially initialized elements. If they
    /// are unable to do so, they may also abort the program.
    ///
    /// # Safety
    /// The `post` closure has leave a fully initialized slice.
    unsafe fn resize_with(
        &mut self,
        new_len: usize,
        pre: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
        post: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
    );

    /// Replaces the slice with a new slice initialized using a caller-supplied closure.
    ///
    /// # Safety
    /// The `init` closure has to leave a fully initialized slice.
    #[inline]
    unsafe fn replace_with(
        &mut self,
        new_len: usize,
        init: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
    ) {
        // SAFETY: the slice passed to pre is fully initialized, init fully initializes the slice
        // and inbetween everything is dropped.
        unsafe {
            self.resize_with(
                new_len,
                |slice| {
                    std::ptr::drop_in_place(
                        slice as *mut [MaybeUninit<Self::Item>] as *mut [Self::Item],
                    )
                },
                init,
            )
        }
    }
}

/// Types storing or referencing a resizable mutable slice with spare capacity.
///
/// # Safety
/// See the module level safety section for [`as_slice`][`self`].
pub unsafe trait ReserveSlice: DynSlice {
    /// Ensures sufficient reserve capacity for at least `additional` further elements.
    ///
    /// Behaves as [`Vec::reserve`].
    fn reserve(&mut self, additional: usize);

    /// Returns the total capacity.
    fn capacity(&self) -> usize;

    // TODO add more vec methods
    // TODO add a resize_with_spare_capacity
}

/// Types storing a mutable slice.
///
/// # Safety
/// See the module level safety section for [`as_slice`][`self`].
pub unsafe trait NewSlice: AsSlice + Sized {
    /// Allocates a new slice initialized using a caller-supplied closure.
    ///
    /// # Safety
    /// The `init` closure has to leave a fully initialized slice.
    unsafe fn new_with(len: usize, init: impl FnOnce(&mut [MaybeUninit<Self::Item>])) -> Self;

    /// Returns an empty slice.
    #[inline]
    fn new_empty() -> Self {
        // SAFETY: nothing to initialize
        unsafe { Self::new_with(0, |_| ()) }
    }
}

mod boxed_slice;
mod refs;
mod slice;
mod vec;

#[cfg(test)]
mod tests {
    use std::{rc::Rc, sync::Arc};

    use super::*;

    fn dyn_slice_push<T: DynSlice>(target: &mut T, value: T::Item) {
        // SAFETY: increases size by one and initializes last item
        unsafe {
            target.resize_with(
                target.as_slice().len() + 1,
                |_| (),
                |slice| {
                    slice.last_mut().unwrap_unchecked().write(value);
                },
            )
        }
    }

    fn dyn_slice_pop<T: DynSlice>(target: &mut T) -> Option<T::Item> {
        let mut res = None;
        if !target.as_slice().is_empty() {
            // SAFETY: does a moving read of the last item and then decreases size by one leaving
            // all remaining items still valid
            unsafe {
                target.resize_with(
                    target.as_slice().len() - 1,
                    |slice| res = Some(slice.last_mut().unwrap_unchecked().assume_init_read()),
                    |_| {},
                )
            }
        }
        res
    }

    fn generic_push_pop<T: NewSlice + DynSlice<Item = u32>>() {
        let mut data = T::new_empty();
        let mut expected = vec![];
        for len in 0..4 {
            for i in 0..len * 4 {
                dyn_slice_push(&mut data, i);
                expected.push(i);
                assert_eq!(data.as_slice(), expected);
            }

            for _ in 0..len * 4 + 2 {
                assert_eq!(dyn_slice_pop(&mut data), expected.pop());
            }
        }
    }

    #[test]
    fn vec_push_pop() {
        generic_push_pop::<Vec<u32>>();
    }

    #[test]
    fn boxed_slice_push_pop() {
        generic_push_pop::<Box<[u32]>>();
    }

    #[test]
    fn boxed_vec_push_pop() {
        generic_push_pop::<Box<Vec<u32>>>();
    }

    #[test]
    fn rc_vec_push_pop() {
        generic_push_pop::<Rc<Vec<u32>>>();
    }

    #[test]
    fn arc_vec_push_pop() {
        generic_push_pop::<Arc<Vec<u32>>>();
    }
}
