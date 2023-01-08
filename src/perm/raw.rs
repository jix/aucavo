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
