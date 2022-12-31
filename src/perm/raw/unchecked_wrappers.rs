//! Wrappers to simplify code performing unchecked operations.
use std::{
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
};

use crate::point::Point;

#[repr(transparent)]
pub struct UncheckedPerm<Pt: Point>(Unchecked<Pt>);

impl<Pt: Point> Deref for UncheckedPerm<Pt> {
    type Target = Unchecked<Pt>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<Pt: Point> DerefMut for UncheckedPerm<Pt> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<Pt: Point> UncheckedPerm<Pt> {
    #[inline(always)]
    pub unsafe fn from_ptr<'a>(ptr: *const Pt, degree: usize) -> &'a Self {
        debug_assert!(degree <= Pt::MAX_DEGREE);

        // SAFETY: slice_from_raw_parts is callers responsibility
        // SAFETY: repr(transparent) slice cast
        unsafe { &*(std::ptr::slice_from_raw_parts(ptr, degree) as *const Self) }
    }

    #[inline(always)]
    pub unsafe fn from_mut_ptr<'a>(ptr: *mut Pt, degree: usize) -> &'a mut Self {
        debug_assert!(degree <= Pt::MAX_DEGREE);
        // SAFETY: slice_from_raw_parts_mut is callers responsibility
        // SAFETY: repr(transparent) slice cast
        unsafe { &mut *(std::ptr::slice_from_raw_parts_mut(ptr, degree) as *mut Self) }
    }

    #[inline(always)]
    pub unsafe fn write(&mut self, index: usize, image: Pt) {
        debug_assert!(image.index() < self.len());
        // SAFETY: callers responsibility + debug assertion
        unsafe {
            self.deref_mut().write(index, image);
        }
    }

    #[inline(always)]
    pub unsafe fn write_index(&mut self, index: usize, image_index: usize) {
        // SAFETY: callers responsibility
        unsafe { self.write(index, Pt::from_index(image_index)) };
    }
}

#[repr(transparent)]
pub struct UninitUncheckedPerm<Pt: Point>([MaybeUninit<Pt>]);
impl<Pt: Point> UninitUncheckedPerm<Pt> {
    #[inline(always)]
    pub unsafe fn from_mut_ptr<'a>(ptr: *mut Pt, degree: usize) -> &'a mut Self {
        debug_assert!(degree <= Pt::MAX_DEGREE);
        // SAFETY: slice_from_raw_parts_mut is callers responsibility
        // SAFETY: repr(transparent) slice + [Pt] -> [MaybeUninit<Pt>] cast
        unsafe {
            &mut *(std::ptr::slice_from_raw_parts_mut(ptr as *mut MaybeUninit<Pt>, degree)
                as *mut Self)
        }
    }

    #[inline(always)]
    pub unsafe fn write(&mut self, index: usize, image: Pt) {
        debug_assert!(index < self.0.len());
        debug_assert!(image.index() < self.0.len());
        // SAFETY: callers responsibility + debug assertion
        unsafe { self.0.get_unchecked_mut(index).write(image) };
    }

    #[inline(always)]
    pub unsafe fn write_index(&mut self, index: usize, image_index: usize) {
        // SAFETY: callers responsibility
        unsafe { self.write(index, Pt::from_index(image_index)) };
    }
}

#[repr(transparent)]
pub struct Unchecked<T>([T]);

impl<T: Copy> Unchecked<T> {
    #[inline(always)]
    pub unsafe fn from_mut_slice<'a>(slice: &mut [T]) -> &'a mut Self {
        // SAFETY: repr(transparent) slice cast
        unsafe { &mut *(slice as *mut [T] as *mut Self) }
    }

    #[inline(always)]
    pub unsafe fn read(&self, index: usize) -> T {
        debug_assert!(index < self.0.len());
        // SAFETY: callers responsibility + debug assertion
        unsafe { *self.0.get_unchecked(index) }
    }

    #[inline(always)]
    pub unsafe fn write(&mut self, index: usize, value: T) {
        debug_assert!(index < self.0.len());
        // SAFETY: callers responsibility + debug assertion
        unsafe { *self.0.get_unchecked_mut(index) = value };
    }

    #[inline(always)]
    pub unsafe fn get_mut<Idx>(&mut self, index: Idx) -> &mut Idx::Output
    where
        Idx: std::slice::SliceIndex<[T]>,
    {
        #[cfg(debug_assertions)]
        {
            self.0.get_mut(index).unwrap()
        }

        // SAFETY: callers responsibility + debug assertion
        #[cfg(not(debug_assertions))]
        {
            unsafe { self.0.get_unchecked_mut(index) }
        }
    }

    #[inline(always)]
    pub unsafe fn swap(&mut self, a: usize, b: usize) {
        let ptr = self.as_mut_ptr();
        debug_assert!(a < self.0.len());
        debug_assert!(b < self.0.len());
        // SAFETY: callers responsibility + debug assertion
        unsafe { std::ptr::swap(ptr.add(a), ptr.add(b)) };
    }

    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.0.as_mut_ptr()
    }

    #[cfg(debug_assertions)]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}
