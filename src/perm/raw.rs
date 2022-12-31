//! Low-level unchecked primitive permutation operations.

// NOTE: previously I tried using a MaybeUninit variant of Perm for the low-level operations and
// while that could reduce the amount of unsafe code a tiny bit, it made dealing with multiple
// permutations that are expected to have the same degree really awkward, as it was not clear at all
// when you could trust the slice lengths to be the same and when you would have to perform runtime
// checks for this. When using separate pointer and degree arguments, this is clearly documented by
// sharing the degree arguments for multiple pointers. After refactoring the code in this style, I
// noticed that I found it much easier to manually check that the unsafe code is correct, even
// though a bit more of it was required overall.

use smallvec::{smallvec, SmallVec};

use crate::{bignum::Int, point::Point};

mod unchecked_wrappers;

use unchecked_wrappers::{Unchecked, UncheckedPerm, UninitUncheckedPerm};

/// Writes identitiy padding to extend a permutation from `small_degree` to `large_degree`.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to at least `large_degree` elements. The
/// values at
/// the points `small_degree..large_degree` will be overwritten. It is safe to call this before
/// initializing the points `0..small_degree`.
#[inline]
pub unsafe fn write_identity_padding<Pt: Point>(
    target: *mut Pt,
    small_degree: usize,
    large_degree: usize,
) {
    // SAFETY: writes in the documented range
    unsafe {
        let target = UninitUncheckedPerm::from_mut_ptr(target, large_degree);

        for index in small_degree..large_degree {
            target.write_index(index, index)
        }
    }
}

/// Writes an identity permutation.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation.
#[inline]
pub unsafe fn write_identity<Pt: Point>(target: *mut Pt, degree: usize) {
    // SAFETY: writes a valid permutation of the required degree.
    unsafe { write_identity_padding(target, 0, degree) }
}

/// Writes the inverse of a permutation.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation. The argument `perm` must point to a valid permutation of
/// the same degree. The pointer arguments may not overlap.
#[inline]
pub unsafe fn write_inverse<Pt: Point>(target: *mut Pt, perm: *const Pt, degree: usize) {
    // SAFETY: writes a valid permutation of the required degree if `perm` is a valid permutation of
    // the same degree
    unsafe {
        let perm = UncheckedPerm::from_ptr(perm, degree);
        let target = UncheckedPerm::from_mut_ptr(target, degree);

        for index in 0..degree {
            target.write_index(perm.read(index).index(), index);
        }
    }
}

/// Writes the product of two permutations of the same degree.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation. The arguments `left` and `right` must point to valid
/// permutations of the same degree as `target`. The `target` pointer may not overlap with other
/// arguments, while `left` and `right` are allowed to point to the same permutation.
// SAFETY: callers within this module make further assumptions on `write_product` and need to be
// manually checked before changing this implementation.
#[inline]
pub unsafe fn write_product<Pt: Point>(
    target: *mut Pt,
    left: *const Pt,
    right: *const Pt,
    degree: usize,
) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        let target = UninitUncheckedPerm::from_mut_ptr(target, degree);
        let left = UncheckedPerm::from_ptr(left, degree);
        let right = UncheckedPerm::from_ptr(right, degree);

        for index in 0..degree {
            let mid_index = left.read(index).index();
            target.write(index, right.read(mid_index));
        }
    }
}

/// Right multiplies a permutation with another permutation of the same degree in place.
///
/// # Safety
/// When called, `target_left` and `right` must be a valid pointers to permutations of degree
/// `degree` and `target_left` will be completely overwritten by their product.
#[inline]
pub unsafe fn right_multiply<Pt: Point>(target_left: *mut Pt, right: *const Pt, degree: usize) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        let target_left = UncheckedPerm::from_mut_ptr(target_left, degree);
        let right = UncheckedPerm::from_ptr(right, degree);

        for index in 0..degree {
            let mid_index = target_left.read(index).index();
            target_left.write(index, right.read(mid_index));
        }
    }
}

/// Writes the inverse of the product of two permutations of the same degree.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation. The arguments `left` and `right` must point to valid
/// permutations of the same degree as `target`. The `target` pointer may not overlap with other
/// arguments, while `left` and `right` are allowed to point to the same permutation.
#[inline]
pub unsafe fn write_inverse_product<Pt: Point>(
    target: *mut Pt,
    left: *const Pt,
    right: *const Pt,
    degree: usize,
) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        let target = UninitUncheckedPerm::from_mut_ptr(target, degree);
        let left = UncheckedPerm::from_ptr(left, degree);
        let right = UncheckedPerm::from_ptr(right, degree);

        for index in 0..degree {
            let mid_index = left.read(index).index();
            target.write_index(right.read(mid_index).index(), index);
        }
    }
}

/// Writes the product of two permutations where the right factor may have a smaller degree.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation. The arguments `left` and `right` must point to valid
/// permutations where `left` has the same degree as `target` and `right` has the same or smaller
/// degree. The `target` pointer may not overlap with other arguments, while `left` and `right` are
/// allowed to point to the same permutation.
#[inline]
pub unsafe fn write_product_extend_right<Pt: Point>(
    target: *mut Pt,
    left: *const Pt,
    right: *const Pt,
    right_degree: usize,
    degree: usize,
) {
    debug_assert!(right_degree <= degree);
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        let target = UninitUncheckedPerm::from_mut_ptr(target, degree);
        let left = UncheckedPerm::from_ptr(left, degree);
        let right = UncheckedPerm::from_ptr(right, right_degree);

        for index in 0..degree {
            let mid = left.read(index);
            let mid_index = mid.index();
            // SAFETY: requires a dynamic bounds check when accessing `right`
            target.write(
                index,
                if mid_index < right_degree {
                    right.read(mid_index)
                } else {
                    mid
                },
            );
        }
    }
}

/// Writes the product of two permutations where the left factor may have a smaller degree.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation. The arguments `left` and `right` must point to valid
/// permutations where `right` has the same degree as `target` and `left` has the same or smaller
/// degree. The `target` pointer may not overlap with other arguments, while `left` and `right` are
/// allowed to point to the same permutation.
#[inline]
pub unsafe fn write_product_extend_left<Pt: Point>(
    target: *mut Pt,
    left: *const Pt,
    left_degree: usize,
    right: *const Pt,
    degree: usize,
) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        // SAFETY: For the first `left_degree` points we can use `write_product` as the images in
        // `left` used as indices for `right` cannot exceed `left_degree`. This does not stricyl
        // fulfill the public contract of `write_product` but the implementation above contains a
        // warning about this.
        write_product(target, left, right, left_degree);

        // SAFETY: for the remaining points the first applied `left` is the identity, so computing
        // the product ends up being a copy of the remaining points in `right` after which we end up
        // with a valid permutation.
        target
            .add(left_degree)
            .copy_from_nonoverlapping(right.add(left_degree), degree - left_degree)
    }
}

#[inline]
unsafe fn write_small_positive_power<Pt: Point>(
    target: *mut Pt,
    perm: *const Pt,
    degree: usize,
    exp: usize,
) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        // SAFETY: either delegates
        match exp {
            0 => return write_identity(target, degree),
            1 => return target.copy_from_nonoverlapping(perm, degree),
            2 => return write_product(target, perm, perm, degree),
            _ => (),
        }

        let target = UninitUncheckedPerm::from_mut_ptr(target, degree);
        let perm = UncheckedPerm::from_ptr(perm, degree);

        // SAFETY: or writes a complete permutation
        for index in 0..degree {
            let mut pt = perm.read(index);

            for _ in 1..exp {
                pt = perm.read(pt.index());
            }

            target.write(index, pt);
        }
    }
}

#[inline]
unsafe fn write_small_negative_power<Pt: Point>(
    target: *mut Pt,
    perm: *const Pt,
    degree: usize,
    exp: usize,
) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        // SAFETY: either delegates
        match exp {
            0 => return write_identity(target, degree),
            1 => return write_inverse(target, perm, degree),
            2 => return write_inverse_product(target, perm, perm, degree),
            _ => (),
        }

        let target = UninitUncheckedPerm::from_mut_ptr(target, degree);
        let perm = UncheckedPerm::from_ptr(perm, degree);

        // SAFETY: or writes a complete permutation
        for index in 0..degree {
            let mut pt = perm.read(index);

            for _ in 1..exp {
                pt = perm.read(pt.index());
            }

            target.write_index(pt.index(), index);
        }
    }
}

unsafe fn write_large_power<Pt: Point>(
    target: *mut Pt,
    perm: *const Pt,
    degree: usize,
    exp: &impl Int,
) {
    // SAFETY: writes a valid permutation of the required degree
    unsafe {
        let target = UninitUncheckedPerm::from_mut_ptr(target, degree);
        let perm = UncheckedPerm::from_ptr(perm, degree);

        let mut seen: SmallVec<[bool; 256]> = smallvec![false; degree]; // TUNE
        let seen = Unchecked::from_mut_slice(&mut seen);

        for index in 0..degree {
            let pt = Pt::from_index(index);
            let mut current = perm.read(index);
            if current == pt {
                // SAFETY: fixpoints remain fixed and are written here
                target.write(index, pt);
                continue;
            } else if seen.read(index) {
                // SAFETY: points that were already written have `seen` set
                continue;
            }

            seen.write(index, true);
            seen.write(current.index(), true);

            let mut cycle_length = 2;

            loop {
                let next = perm.read(current.index());
                if next == pt {
                    break;
                }
                cycle_length += 1;
                current = next;
                seen.write(current.index(), true);
            }

            let shift = exp.mod_usize(cycle_length);

            let mut from = current;
            current = pt;

            for _ in 0..shift {
                from = perm.read(from.index());
            }

            for _ in 0..cycle_length {
                target.write(current.index(), perm.read(from.index()));

                from = perm.read(from.index());
                current = perm.read(current.index());
            }
        }
    }
}

/// Writes the power of a permutation.
///
/// # Safety
/// When called, `target` must be a valid mutable pointer to `degree` elements which will be
/// initialized with a valid permutation. The argument `perm` must point to a valid permutation of
/// the same degree. The pointer arguments may not overlap.
#[inline]
pub unsafe fn write_power<Pt: Point>(
    target: *mut Pt,
    perm: *const Pt,
    degree: usize,
    exp: &impl Int,
) {
    const fn can_be_negative<T: Int>(_: &T) -> bool {
        T::SIGNED
    }

    // SAFETY: delegates to one of the implementations
    unsafe {
        // TODO tune exponent cutoff
        if let Some(abs_exp) = exp.unsigned_abs_as_usize().filter(|&abs| abs <= 8) {
            if exp.is_negative() {
                return write_small_negative_power(target, perm, degree, abs_exp);
            } else {
                return write_small_positive_power(target, perm, degree, abs_exp);
            }
        }

        if can_be_negative(exp) {
            if let Some(exp) = exp.as_isize() {
                return write_large_power(target, perm, degree, &exp);
            }
        } else if let Some(exp) = exp.as_usize() {
            return write_large_power(target, perm, degree, &exp);
        }

        write_large_power(target, perm, degree, exp);
    }
}

/// Advances to the lexicographically next permutation in-place.
///
/// This steps lexicographically through permutations of the same degree. It returns `false` and
/// resets to the identity permutation (lexicographically first) when called on the
/// lexciographically last permutation.
///
/// # Safety
/// When called, `target` must be a mutable pointer to a valid permutation of degree `degree` which
/// is modified in-place.
pub unsafe fn lexicographical_next<Pt: Point>(target: *mut Pt, degree: usize) -> bool {
    // SAFETY: only does in-bounds swaps and reversals
    unsafe {
        if degree == 0 {
            return false;
        }

        let target = UncheckedPerm::from_mut_ptr(target, degree);

        let mut prev = target.read(degree - 1);

        let Some(a) = (0..degree - 1).rev().find(|&index| {
            let current = target.read(index);
            let found = current < prev;
            prev = current;
            found
        }) else {
            write_identity(target.as_mut_ptr(), degree);
            return false;
        };

        let a_image = target.read(a);

        let b = a
            + 1
            + target
                .get_mut(a + 2..degree)
                .partition_point(|&b_image| b_image > a_image);

        target.swap(a, b);
        target.get_mut(a + 1..degree).reverse();

        true
    }
}

/// Left-multiplies a transposition of two points in-place.
///
/// # Safety
/// When called, `target` must be a mutable pointer to a valid permutation of degree `degree` which
/// is modified in-place.
#[inline(always)]
pub unsafe fn left_multiply_transposition<Pt: Point>(target: *mut Pt, degree: usize, a: Pt, b: Pt) {
    // SAFETY: in-bounds swap
    unsafe {
        let target = UncheckedPerm::from_mut_ptr(target, degree);
        target.swap(a.index(), b.index());
    }
}
