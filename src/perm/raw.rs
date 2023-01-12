use std::mem::MaybeUninit;

use crate::point::Point;

pub unsafe fn write_identity_padding<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    from_degree: usize,
) -> &mut [MaybeUninit<Pt>] {
    // SAFETY: when `from_degree <= target.len()` as required from callers, all indexing is
    // stays in bounds
    unsafe {
        for index in from_degree..target.len() {
            target.get_unchecked_mut(index).write(Pt::from_index(index));
        }
        target.get_unchecked_mut(..from_degree)
    }
}

#[inline(always)]
pub fn write_identity<Pt: Point>(target: &mut [MaybeUninit<Pt>]) -> &mut [Pt] {
    // SAFETY: a `from_degree` value of 0 is always in bounds
    unsafe { write_identity_padding(target, 0) };

    // FUTURE: use std method for this cast
    // SAFETY: slice is fully initialized now
    unsafe { &mut *(target as *mut [MaybeUninit<Pt>] as *mut [Pt]) }
}

/// Writes the inverse of `perm` to `target`
///
/// # Safety
/// Both `perm` and `target` need to have the same length, `perm` has to be a valid permutation.
#[inline(always)]
pub unsafe fn write_inverse<Pt: Point>(target: &mut [MaybeUninit<Pt>], perm: &[Pt]) {
    debug_assert!(target.len() == perm.len());
    // SAFETY: same requirements as we have
    unsafe { write_inverse_impl(target, perm.as_ptr()) };
}

/// Writes the inverse of `perm` to `target`, non-redundant argument version
///
/// # Safety
/// Both `perm` and `target` need to have the same length, `perm` has to be a valid permutation.
unsafe fn write_inverse_impl<Pt: Point>(target: &mut [MaybeUninit<Pt>], perm: *const Pt) {
    // SAFETY: turns a -> b mappings into b -> a mappings, so writes every point exactly once
    unsafe {
        let len = target.len();
        let perm = std::slice::from_raw_parts(perm, len);

        for i in 0..len {
            target
                .get_unchecked_mut(perm.get_unchecked(i).index())
                .write(Pt::from_index(i));
        }
    }
}

/// Writes the product of `left` and `right` to `target`
///
/// # Safety
/// All of `left`, `right` and `target` need to have the same length, `left` and `right` have to be
/// a valid permutations.
// SAFETY: note that write_product_extend_left calls this without passing valid permutations
#[inline(always)]
pub unsafe fn write_product<Pt: Point>(target: &mut [MaybeUninit<Pt>], left: &[Pt], right: &[Pt]) {
    debug_assert!(target.len() == left.len());
    debug_assert!(target.len() == right.len());
    // SAFETY: same requirements as we have
    unsafe { write_product_impl(target, left.as_ptr(), right.as_ptr()) };
}

/// Writes the product of `left` and `right` to `target`, non-redundant argument version
///
/// # Safety
/// All of `left`, `right` and `target` need to have the same length, `left` and `right` have to be
/// a valid permutations.
// SAFETY: note that write_product_extend_left calls this without passing valid permutations
unsafe fn write_product_impl<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    left: *const Pt,
    right: *const Pt,
) {
    // SAFETY: pointwise composition stays in bounds for permutations when left, right and target
    // have the same length
    unsafe {
        let len = target.len();
        let left = std::slice::from_raw_parts(left, len);
        let right = std::slice::from_raw_parts(right, len);

        for i in 0..len {
            target
                .get_unchecked_mut(i)
                .write(*right.get_unchecked(left.get_unchecked(i).index()));
        }
    }
}

/// Writes the product of `left` and `right` to `target`, degree-extending `right`
///
/// # Safety
/// Both `left` and `target` need to have the same length, `right` must have a length that is not
/// larger than that, `left` and `right` have to be a valid permutations.
#[inline(always)]
pub unsafe fn write_product_extend_right<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    left: &[Pt],
    right: &[Pt],
) {
    debug_assert!(target.len() == left.len());
    debug_assert!(target.len() >= right.len());
    // SAFETY: same requirements as we have
    unsafe { write_product_extend_right_impl(target, left.as_ptr(), right) };
}

/// Writes the product of `left` and `right` to `target`, degree-extending `right`, non-redundant
/// argument version
///
/// # Safety
/// Both `left` and `target` need to have the same length, `right` must have a length that is not
/// larger than that, `left` and `right` have to be a valid permutations.
unsafe fn write_product_extend_right_impl<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    left: *const Pt,
    right: &[Pt],
) {
    // SAFETY: pointwise composition, needs a bound check when indexing into the smaller right,
    // everything else will stay in bounds for permutations
    unsafe {
        let len = target.len();
        let left = std::slice::from_raw_parts(left, len);
        let right_len = right.len();

        for i in 0..len {
            let mut pt = *left.get_unchecked(i);
            if pt.index() < right_len {
                pt = *right.get_unchecked(pt.index())
            }
            target.get_unchecked_mut(i).write(pt);
        }
    }
}

/// Writes the product of `left` and `right` to `target`, degree-extending `left`
///
/// # Safety
/// Both `right` and `target` need to have the same length, `left` must have a length that is not
/// larger than that, `left` and `right` have to be a valid permutations.
#[inline(always)]
pub unsafe fn write_product_extend_left<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    left: &[Pt],
    right: &[Pt],
) {
    debug_assert!(target.len() >= left.len());
    debug_assert!(target.len() == right.len());
    // SAFETY: same requirements as we have
    unsafe { write_product_extend_left_impl(target, left, right.as_ptr()) };
}

unsafe fn write_product_extend_left_impl<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    left: &[Pt],
    right: *const Pt,
) {
    // SAFETY: pointwise composition, for the points `0..left.len()` we can re-use the
    // `write_product` loop as everything stays in bounds, the points `left.len()..right.len()` do
    // not get moved by left, so we can copy the images from `right` directly.
    unsafe {
        let len = target.len();
        let left_len = left.len();
        let right = std::slice::from_raw_parts(right, len);

        write_product(
            target.get_unchecked_mut(..left_len),
            left,
            right.get_unchecked(..left_len),
        );

        target.get_unchecked_mut(left_len..len).copy_from_slice(
            &*(right.get_unchecked(left_len..len) as *const [Pt] as *const [MaybeUninit<Pt>]),
        )
    }
}

/// Writes the product of `left` and `right` to `target`, degree-extending either `left` or `right`
/// (but not both).
///
/// # Safety
/// Either `left` or `right` need to have the same length as `target` and the other one may not be
/// larger than that. Both `left` and `right` have to be a valid permutations.
#[inline]
pub unsafe fn write_product_extend_smaller<Pt: Point>(
    target: &mut [MaybeUninit<Pt>],
    left: &[Pt],
    right: &[Pt],
) {
    if left.len() < right.len() {
        // SAFETY: same requirements we have with the conditions checked here
        unsafe { write_product_extend_left(target, left, right) };
    } else {
        // SAFETY: same requirements we have with the conditions checked here
        unsafe { write_product_extend_right(target, left, right) };
    }
}

/// Checks whether a slice contains permutation of `0..slice.len()`.
///
/// If the length of `slice` exceeds `Pt::MAX_DEGREE` this also returns `false`, even when it
/// would be a valid permutation otherwise.
pub fn is_perm<Pt: Point>(slice: &[Pt]) -> bool {
    if slice.len() > Pt::MAX_DEGREE {
        return false;
    }
    let mut seen = vec![false; slice.len()]; // TODO temporary storage
    for &p in slice {
        if let Some(seen_p) = seen.get_mut(p.index()) {
            if std::mem::replace(seen_p, true) {
                return false;
            }
        } else {
            return false;
        }
    }
    true
}
