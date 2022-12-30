//! Low-level primitives that implement operations on permutations.
use std::mem::MaybeUninit;

use super::Perm;
use crate::point::Point;

// SAFETY: Limit amount of code that can access fields with safety invariants
mod field_safety {
    use super::*;

    /// A potentially uninitialized permutation.
    ///
    /// Used to initialize [`Perm`] values.
    #[repr(transparent)]
    pub struct MaybeUninitPerm<Pt: Point> {
        // SAFETY: we may not provide any safe API that could write uninitialized data to
        // `MaybeUninitPerm` slice as it may be pointing into data that needs to remain initialized.
        slice: [MaybeUninit<Pt>],
    }

    impl<Pt: Point> MaybeUninitPerm<Pt> {
        /// Provides read-only access to the potentially uninitialzed points of this permutation.
        ///
        #[inline(always)]
        pub fn as_slice(&self) -> &[MaybeUninit<Pt>] {
            &self.slice
        }

        /// Provides mutable access to the potentially uninitialzed points of this permutation.
        ///
        /// # Safety
        /// From the returned slice, callers may not read values they have not overwritten themselves
        /// nor may they write any uninitialized values to it.
        #[inline(always)]
        pub unsafe fn as_mut_slice(&mut self) -> &mut [MaybeUninit<Pt>] {
            &mut self.slice
        }
    }
}

pub use field_safety::MaybeUninitPerm;

impl<Pt: Point> MaybeUninitPerm<Pt> {
    /// Returns the size of the set the permutation acts on.
    ///
    /// See also [`Perm::degree`].
    #[inline]
    pub fn degree(&self) -> usize {
        self.as_slice().len()
    }

    /// Casts a mutable slice of uninitialized points to an uninitialized permutation.
    #[inline]
    pub fn from_mut_slice(slice: &mut [MaybeUninit<Pt>]) -> &mut Self {
        assert!(slice.len() <= Pt::MAX_DEGREE);
        // SAFETY: only requirement is the assert above
        unsafe { Self::from_mut_slice_unchecked(slice) }
    }

    /// Casts a mutable slice of uninitialized points to an uninitialized permutation without
    /// checking the degree.
    ///
    /// # Safety
    /// The length of the passed slice may not exceed [`Pt::MAX_DEGREE`][`Point::MAX_DEGREE`].
    #[inline]
    pub unsafe fn from_mut_slice_unchecked(slice: &mut [MaybeUninit<Pt>]) -> &mut Self {
        // SAFETY: constructing an unsized repr(transparent) value
        unsafe { &mut *(slice as *mut [MaybeUninit<Pt>] as *mut Self) }
    }

    /// Casts a mutable slice of initialized points to an uninitialized permutation without
    /// checking the degree.
    ///
    /// # Safety
    /// The length of the passed slice may not exceed [`Pt::MAX_DEGREE`][`Point::MAX_DEGREE`].
    #[inline]
    pub unsafe fn from_init_mut_slice_unchecked(slice: &mut [Pt]) -> &mut Self {
        // SAFETY: constructing an unsized repr(transparent) value, casting Pt to MaybeUninit<Pt>
        // We never allow save code to overwrite with MaybeUninit<Pt>
        unsafe { &mut *(slice as *mut [Pt] as *mut Self) }
    }

    /// Casts a mutable reference to an uninitialized array of points to an uninitialized
    /// permutation.
    #[inline]
    pub fn from_mut_array<const N: usize>(array: &mut MaybeUninit<[Pt; N]>) -> &mut Self {
        assert!(N <= Pt::MAX_DEGREE);
        // SAFETY: only requirement is the assert above
        unsafe {
            Self::from_mut_slice_unchecked(
                (*(array as *mut MaybeUninit<[Pt; N]> as *mut [MaybeUninit<Pt>; N])).as_mut_slice(),
            )
        }
    }

    /// Casts a mutable reference to an array of points to an uninitialized permutation.
    #[inline]
    pub fn from_init_mut_array<const N: usize>(array: &mut [Pt; N]) -> &mut Self {
        assert!(N <= Pt::MAX_DEGREE);
        // SAFETY: only requirement is the assert above
        unsafe {
            Self::from_mut_slice_unchecked(
                (*(array as *mut [Pt; N] as *mut [MaybeUninit<Pt>; N])).as_mut_slice(),
            )
        }
    }

    /// Returns a write-only iterator over the potentially uninitialized points of this permutation.
    #[inline]
    pub fn iter_write(&mut self) -> IterWrite<Pt> {
        // SAFETY: IterWrite is write-only
        unsafe { IterWrite(self.as_mut_slice().iter_mut()) }
    }

    /// Initializes the point at a given index.
    #[inline]
    pub fn write_at_index(&mut self, index: usize, image: Pt) -> &mut Pt {
        // SAFETY: write only
        unsafe { self.as_mut_slice()[index].write(image) }
    }

    /// Initializes a given point.
    #[inline]
    pub fn write_at(&mut self, point: Pt, image: Pt) -> &mut Pt {
        self.write_at_index(point.index(), image)
    }

    /// Returns the fully initialized permutation.
    ///
    /// # Safety
    /// This value must have been initialized with a valid permutation before calling this.
    #[inline]
    pub unsafe fn assume_init_mut(&mut self) -> &mut Perm<Pt> {
        // SAFETY: the requirements below are exactly the ones documented above
        unsafe {
            Perm::from_mut_slice_unchecked(std::slice::from_raw_parts_mut(
                self.as_mut_slice().as_mut_ptr() as *mut Pt,
                self.degree(),
            ))
        }
    }

    /// Returns a smaller degree [`MaybeUninitPerm`] after adding identitiy padding.
    ///
    /// This can be used to initialize a larger degree permutation with code that initializes a
    /// smaller degree premutation.
    #[inline]
    pub fn pad_from_degree(&mut self, mut degree: usize) -> &mut MaybeUninitPerm<Pt> {
        // SAFETY: we only write initialized data or wrap it again in an `MaybeUninitPerm`
        let (smaller, identity_padding) = unsafe { self.as_mut_slice().split_at_mut(degree) };
        for p in identity_padding.iter_mut() {
            p.write(Pt::from_index(degree));
            degree += 1;
        }
        // SAFETY: increasing the degree would panic the `split_at_mut` above, so this does not
        // exceed `Pt::MAX_DEGREE`.
        unsafe { Self::from_mut_slice_unchecked(smaller) }
    }
}


/// A write-only iterator over the potentially uninitialized points of this permutation.
pub struct IterWrite<'a, Pt: Point>(std::slice::IterMut<'a, MaybeUninit<Pt>>);

/// Write-only reference to potentially uninitialized data.
pub struct WriteOnly<'a, T>(&'a mut MaybeUninit<T>);

impl<'a, T> WriteOnly<'a, T> {
    /// Initializes potentitally uninitialized data.
    ///
    /// This overwrites existing data without dropping it.
    #[inline]
    pub fn write(&mut self, value: T) -> &mut T {
        self.0.write(value)
    }
}

impl<'a, Pt: Point> Iterator for IterWrite<'a, Pt> {
    type Item = WriteOnly<'a, Pt>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(WriteOnly)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, Pt: Point> DoubleEndedIterator for IterWrite<'a, Pt> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(WriteOnly)
    }
}

impl<'a, Pt: Point> ExactSizeIterator for IterWrite<'a, Pt> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// Writes the identity permutation to `output`.
#[inline]
pub fn write_identity<Pt: Point>(output: &mut MaybeUninitPerm<Pt>) -> &mut Perm<Pt> {
    for (i, mut p) in output.iter_write().enumerate() {
        p.write(Pt::from_index(i));
    }

    // SAFETY: wrote a valid identity permutation above
    unsafe { output.assume_init_mut() }
}

/// Writes a copy of `perm` to `output`, panics if the degrees differ.
#[inline]
pub fn write_copy_same_degree<'a, Pt: Point>(
    output: &'a mut MaybeUninitPerm<Pt>,
    perm: &Perm<Pt>,
) -> &'a mut Perm<Pt> {
    // SAFETY: this panics when the length do not match, otherwise fully overwrites output with
    // valid data
    unsafe { output.as_mut_slice() }.copy_from_slice(
        // SAFETY: safe cast of &[Pt] to &[MaybeUninit<Pt>]
        unsafe { &*(perm.as_slice() as *const [Pt] as *const [MaybeUninit<Pt>]) },
    );

    // SAFETY: copied a valid permutation
    unsafe { output.assume_init_mut() }
}

/// Writes the inverse of `perm` to `output`, panics if the degrees differ.
#[inline]
pub fn write_inverse_same_degree<'a, Pt: Point>(
    output: &'a mut MaybeUninitPerm<Pt>,
    perm: &Perm<Pt>,
) -> &'a mut Perm<Pt> {
    // SAFETY: does not panic when the degrees match
    assert_eq!(output.degree(), perm.degree());

    // SAFETY: this cannot panic
    for (i, p) in perm.iter() {
        output.write_at(p, i);
    }

    // SAFETY: fully initialized output using the inverse of perm
    unsafe { output.assume_init_mut() }
}

/// Writes the product of `left` and `right` to `output`.
///
/// This panics if either input has a larger degree than `output`.
pub fn write_product<'a, Pt: Point>(
    output: &'a mut MaybeUninitPerm<Pt>,
    left: &Perm<Pt>,
    right: &Perm<Pt>,
) -> &'a mut Perm<Pt> {
    // SAFETY: does not panic when the output degree matches the max of left and right
    assert!(left.degree().max(right.degree()) <= output.degree());

    // SAFETY: this cannot panic
    for (i, mut p) in output.iter_write().enumerate() {
        p.write(right.image(left.image_of_index(i)));
    }

    // SAFETY: fully initialized with a valid permutation
    unsafe { output.assume_init_mut() }
}
