use std::mem::{replace, MaybeUninit};

use super::{AsMutSlice, AsSlice, DynSlice, NewSlice, SpecializeAsDynSlice, SpecializeAsNewSlice};

// SAFETY: provides consistent access
unsafe impl<T> AsSlice for Box<[T]> {
    type Item = T;

    #[inline(always)]
    fn as_slice(&self) -> &[Self::Item] {
        self
    }
}

// SAFETY: provides consistent access
unsafe impl<T> AsMutSlice for Box<[T]> {
    #[inline(always)]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }

    specialize_impl!(specialize_as_dyn_slice: SpecializeAsDynSlice);
    specialize_impl!(specialize_as_new_slice: SpecializeAsNewSlice);
}

// SAFETY: provides consistent access
unsafe impl<T> DynSlice for Box<[T]> {
    #[inline]
    unsafe fn resize_with(
        &mut self,
        new_len: usize,
        pre: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
        post: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
    ) {
        let len = self.len();

        // Empty vec and empty boxed slices don't allocate
        let mut boxed = boxed_maybe_uninit(replace(self, vec![].into_boxed_slice()));

        pre(&mut boxed);

        if new_len != len {
            boxed = boxed_realloc(boxed, new_len);
        }

        post(&mut boxed);

        // SAFETY: post is required to initialize all elements
        unsafe { replace(self, boxed_assume_init(boxed)) };
    }

    #[inline]
    unsafe fn replace_with(
        &mut self,
        new_len: usize,
        init: impl FnOnce(&mut [MaybeUninit<Self::Item>]),
    ) {
        // NOTE: when replacing everything, it's most likely cheaper to do a realloc rather than
        // letting realloc move data that's going to be overwritten anyway.

        let len = self.len();

        // Empty vec and empty boxed slices don't allocate
        let mut boxed = boxed_maybe_uninit(replace(self, vec![].into_boxed_slice()));

        // SAFETY: boxed is fully initialized here
        unsafe {
            std::ptr::drop_in_place(
                &mut *boxed as *mut [MaybeUninit<Self::Item>] as *mut [Self::Item],
            )
        };

        if new_len != len {
            // SAFETY: initializing a [MaybeUninit<T>] is a no-op
            boxed = unsafe { Box::<[MaybeUninit<T>]>::new_with(new_len, |_| ()) };
        }

        init(&mut boxed);

        // SAFETY: post is required to initialize all elements
        unsafe { replace(self, boxed_assume_init(boxed)) };
    }
}

#[inline(always)]
fn boxed_maybe_uninit<T>(boxed: Box<[T]>) -> Box<[MaybeUninit<T>]> {
    // SAFETY: cast from Box<[T]> into Box<[MaybeUninit<T>]> is always safe
    unsafe { Box::from_raw(Box::into_raw(boxed) as *mut [MaybeUninit<T>]) }
}

/// # Safety
/// The boxed slice has to be completely initialized before calling this.
#[inline(always)]
unsafe fn boxed_assume_init<T>(boxed: Box<[MaybeUninit<T>]>) -> Box<[T]> {
    // SAFETY: cast from Box<[MaybeUninit<T>]> into Box<[T]> is safe if all elements are initialized
    // which we require
    unsafe { Box::from_raw(Box::into_raw(boxed) as *mut [T]) }
}

fn boxed_realloc<T>(boxed: Box<[MaybeUninit<T>]>, new_len: usize) -> Box<[MaybeUninit<T>]> {
    let mut vec = Vec::from(boxed);

    if new_len > vec.len() {
        vec.reserve_exact(new_len - vec.len());
    }
    // SAFETY: we're either shrinking the length or reserved the missing capacity to get to new_len
    unsafe { vec.set_len(new_len) };

    vec.into_boxed_slice()
}

// SAFETY: provides consistent access
unsafe impl<T> NewSlice for Box<[T]> {
    unsafe fn new_with(len: usize, init: impl FnOnce(&mut [MaybeUninit<Self::Item>])) -> Self {
        // FUTURE: use new_uninit_slice when stabilized

        // SAFETY: same safety requirements
        unsafe { Vec::new_with(len, init).into_boxed_slice() }
    }
}
