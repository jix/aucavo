use std::{
    borrow::Borrow,
    cmp::{self},
    fmt,
    hash::Hash,
    mem::MaybeUninit,
    ops::{Deref, DerefMut, Range},
};

use smallvec::{smallvec, SmallVec};

use crate::{cycles::Cycles, point::Point};

use self::iter::Iter;

pub mod iter;

/// A permutation.
#[repr(transparent)]
pub struct Perm<Pt: Point> {
    points: [Pt],
}

impl<Pt: Point> Perm<Pt> {
    pub const EMPTY: &'static Perm<Pt> = unsafe { &*(&[] as *const [Pt] as *const Self) };

    /// Checks whether a slice `points` contains permutation of `0..points.len()`.
    ///
    /// If the length of `points` exceeds `Pt::MAX_DEGREE` this also returns `false`, even when it would
    /// be a valid permutation otherwise.
    pub fn is_perm(points: &[Pt]) -> bool {
        assert!(points.len() <= Pt::MAX_DEGREE);
        let mut seen: SmallVec<[bool; 256]> = smallvec![false; points.len()]; // TUNE
        for &p in points {
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

    /// Creates a `Perm` reference from a slice containing the images of the first n points.
    ///
    /// Panics for non-permutation arguments.
    #[inline]
    pub fn from_slice(points: &[Pt]) -> &Self {
        assert!(Self::is_perm(points)); // SAFETY precondition check
        unsafe { Self::from_slice_unchecked(points) }
    }

    /// Creates a mutable `Perm` reference from a slice containing the images of the first n points.
    ///
    /// Panics for non-permutation arguments.
    #[inline]
    pub fn from_mut_slice(points: &mut [Pt]) -> &mut Self {
        assert!(Self::is_perm(points)); // SAFETY precondition check
        unsafe { Self::from_mut_slice_unchecked(points) }
    }

    /// Creates a `Perm` reference from a slice containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `points` must be a permutation of the points `0..points.len()`.
    #[inline]
    pub const unsafe fn from_slice_unchecked(points: &[Pt]) -> &Self {
        // SAFETY repr(transparent)
        &*(points as *const [Pt] as *const Self)
    }

    /// Creates a mutable `Perm` reference from a slice containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `points` must be a permutation of the points `0..points.len()`.
    #[inline]
    pub unsafe fn from_mut_slice_unchecked(points: &mut [Pt]) -> &mut Self {
        // SAFETY repr(transparent)
        &mut *(points as *mut [Pt] as *mut Self)
    }

    /// Returns the image of a point under the permutation.
    #[inline]
    pub fn image(&self, pt: Pt) -> Pt {
        if let Some(&pt) = self.points.get(pt.index()) {
            pt
        } else {
            pt
        }
    }

    /// Returns the image of a point under the permutation using `usize` instead of `Pt`.
    #[inline]
    pub fn index_image(&self, pt: usize) -> usize {
        if let Some(&pt) = self.points.get(pt) {
            pt.index()
        } else {
            pt
        }
    }

    /// Returns the size of the set the permutation is defined on.
    ///
    /// Unless documented otherwise, a smaller degree permutation is implicitly extended by adding
    /// fixed points when a larger degree permutation is expected.
    #[inline]
    pub fn degree(&self) -> usize {
        self.points.len()
    }

    /// Returns the set on which the permutation is defined on.
    pub fn points(&self) -> Range<Pt> {
        Pt::from_index(0)..Pt::from_index(self.degree())
    }

    /// Returns the slice containing the images of `self.points()`.
    #[inline]
    pub fn as_slice(&self) -> &[Pt] {
        &self.points
    }

    /// Returns the mutable slice containing the images of `self.points()`.
    ///
    /// # Safety
    /// A `Perm` must always be a valid permutation and users may depend on this for memory safety.
    /// The user of this method has to ensure this invariant is maintained, even in the present of
    /// panics.
    #[inline]
    pub unsafe fn as_mut_slice(&mut self) -> &mut [Pt] {
        &mut self.points
    }

    /// Updates the permutation by pre-composing a transposition of two points.
    ///
    /// Panics when either point is not contained in `self.points()`.
    #[inline]
    pub fn precompose_transposition(&mut self, transposition: [Pt; 2]) {
        let [a, b] = transposition;
        self.points.swap(a.index(), b.index());
    }

    /// Updates the permutation by pre-composing a cycle.
    ///
    /// Panics when any point of the cycle is not contained in `self.points()`.
    #[inline]
    pub fn precompose_cycle(&mut self, cycle: &[Pt]) {
        if let Some((&a, rest)) = cycle.split_first() {
            for &b in rest.iter().rev() {
                self.points.swap(a.index(), b.index());
            }
        }
    }

    /// Updates the permutation by post-composing another permutation.
    ///
    /// Panics when the argument permutation has a larger degree than this permutation.
    #[inline]
    pub fn postcompose_perm<Pt2: Point>(&mut self, other: &Perm<Pt2>) {
        if other.degree() < self.degree() {
            self.postcompose_smaller_degree_perm(other)
        } else {
            self.postcompose_same_degree_perm(other)
        }
    }

    /// Updates the permutation by post-composing another permutation of the same degree.
    ///
    /// Panics when the two permutations do not have the same degree.
    #[inline]
    fn postcompose_same_degree_perm<Pt2: Point>(&mut self, other: &Perm<Pt2>) {
        assert_eq!(other.degree(), self.degree());

        for pt in &mut self.points {
            // SAFETY no OOB possible due to same degree
            unsafe { *pt = Pt::from_index(other.points.get_unchecked(pt.index()).index()) };
        }
    }

    /// Updates the permutation by post-composing another permutation of the same or smaller degree.
    ///
    /// Panics when the argument has a larger degre.
    #[inline]
    fn postcompose_smaller_degree_perm<Pt2: Point>(&mut self, other: &Perm<Pt2>) {
        assert!(other.degree() <= self.degree());
        for pt in &mut self.points {
            // SAFETY the other set is contained in our set, so we will not escape our set
            *pt = Pt::from_index(other.index_image(pt.index()));
        }
    }

    /// Sets the permutation to the identity permutation.
    ///
    /// Does not change the degree of the permutation.
    #[inline]
    pub fn assign_identity(&mut self) {
        // TODO move this ti MaybeUninitPerm
        for (i, pt) in self.points.iter_mut().enumerate() {
            *pt = Pt::from_index(i);
        }
    }

    /// Assigns a copy of a permutation.
    ///
    /// Panics when the degree of the argument is larger than the target degree.
    #[inline]
    pub fn assign_perm<Pt2: Point>(&mut self, perm: &Perm<Pt2>) {
        MaybeUninitPerm::new_mut(self).assign_perm(perm)
    }

    /// Assigns the inverse of a permutation.
    ///
    /// Panics when the degree of the argument is larger than the target degree.
    #[inline]
    pub fn assign_inverse<Pt2: Point>(&mut self, perm: &Perm<Pt2>) {
        MaybeUninitPerm::new_mut(self).assign_inverse(perm)
    }

    /// Assigns the composition of two permutations.
    ///
    /// The application order is left-to-right following computational group theory conventions.
    ///
    /// Panics when the degree of either argument is larger than the target degree.
    #[inline]
    pub fn assign_composition<Pt2: Point, Pt3: Point>(&mut self, lhs: &Perm<Pt2>, rhs: &Perm<Pt3>) {
        MaybeUninitPerm::new_mut(self).assign_composition(lhs, rhs)
    }

    /// Returns the same permutation with trailing fixed points removed from the set.
    #[inline]
    pub fn as_min_degree(&self) -> &Self {
        self.shrink_to_degree(0)
    }

    #[inline]
    fn shrink_to_degree(&self, degree: usize) -> &Self {
        let mut shrunk = &self.points;
        while shrunk.len() > degree {
            if let Some((&last, rest)) = shrunk.split_last() {
                if last.index() != rest.len() {
                    break;
                }
                shrunk = rest;
            } else {
                break;
            }
        }

        // SAFETY we only remove fixed points, so min_degree stays a permutation
        unsafe { Self::from_slice_unchecked(shrunk) }
    }

    /// Iterates over the permutation viewed as a relation.
    ///
    /// Guarantees sorted iteration order.
    #[inline]
    pub fn iter(&self) -> Iter<Pt> {
        Iter::new(self)
    }

    /// Returns a cycle decomposition of the permutation.
    pub fn cycles(&self) -> Cycles<Pt> {
        let mut cycles = Cycles::default();

        let min_degree = self.as_min_degree();

        let mut seen: SmallVec<[bool; 256]> = smallvec![false; min_degree.degree()]; // TUNE

        // TODO indexing can be unchecked below
        for (a, mut b) in min_degree.iter() {
            if a == b || seen[a.index()] {
                continue;
            }
            seen[a.index()] = true;

            let mut next = Some(a);

            cycles.push(std::iter::from_fn(|| {
                let current = next?;
                if b == a {
                    next = None;
                } else {
                    seen[b.index()] = true;
                    next = Some(b);
                    b = min_degree.image(b);
                }
                Some(current)
            }));
        }

        cycles
    }
}

impl<Pt: Point> fmt::Display for Perm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.cycles(), f)
    }
}

impl<Pt: Point> fmt::Debug for Perm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ 0..{}", self, self.degree())
    }
}

impl<Pt: Point, Pt2: Point> PartialEq<Perm<Pt2>> for Perm<Pt> {
    #[inline(always)] // Compile time dispatch
    fn eq(&self, other: &Perm<Pt2>) -> bool {
        if Pt::SPECIALIZE_POINT_TYPE == Pt2::SPECIALIZE_POINT_TYPE {
            let other = unsafe { &*(other as *const Perm<Pt2> as *const Perm<Pt>) };
            self.homogeneous_eq(other)
        } else if Pt::SPECIALIZE_POINT_TYPE < Pt2::SPECIALIZE_POINT_TYPE {
            self.heterogeneous_eq(other)
        } else {
            other.heterogeneous_eq(self)
        }
    }
}

impl<Pt: Point> Perm<Pt> {
    #[inline]
    fn heterogeneous_eq<Pt2: Point>(&self, other: &Perm<Pt2>) -> bool {
        let mut lhs = self;
        let mut rhs = other;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs) = Self::heterogeneous_eq_cmp_fixup(lhs, rhs);
        }

        if lhs.degree() != rhs.degree() {
            return false;
        }

        // TODO check codegen, should use known equal degree
        for (l, r) in lhs.as_slice().iter().zip(rhs.as_slice().iter()) {
            if l.index() != r.index() {
                return false;
            }
        }

        true
    }

    #[inline]
    #[cold] // TUNE
    fn heterogeneous_eq_cmp_fixup<'a, Pt2: Point>(
        mut lhs: &'a Self,
        mut rhs: &'a Perm<Pt2>,
    ) -> (&'a Self, &'a Perm<Pt2>) {
        if lhs.degree() > rhs.degree() {
            lhs = lhs.shrink_to_degree(rhs.degree())
        } else {
            rhs = rhs.shrink_to_degree(lhs.degree());
        }
        (lhs, rhs)
    }

    #[inline]
    fn homogeneous_eq(&self, other: &Self) -> bool {
        let mut lhs = self;
        let mut rhs = other;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs) = Self::homogeneous_eq_fixup(lhs, rhs);
        }

        lhs.as_slice() == rhs.as_slice()
    }

    #[inline]
    #[cold] // TUNE
    fn homogeneous_eq_fixup<'a>(mut lhs: &'a Self, mut rhs: &'a Self) -> (&'a Self, &'a Self) {
        if lhs.degree() > rhs.degree() {
            (lhs, rhs) = (rhs, lhs);
        }
        rhs = rhs.shrink_to_degree(lhs.degree());
        (lhs, rhs)
    }
}

impl<Pt: Point> Eq for Perm<Pt> {}

impl<Pt: Point> Hash for Perm<Pt> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let min_degree = self.as_min_degree();
        // As Hash only has to maintain Eq not PartialEq, we don't need to worry about compatibility
        // between different Pt types.
        min_degree.as_slice().hash(state);
    }
}

impl<Pt: Point, Pt2: Point> PartialOrd<Perm<Pt2>> for Perm<Pt> {
    fn partial_cmp(&self, other: &Perm<Pt2>) -> Option<cmp::Ordering> {
        if Pt::SPECIALIZE_POINT_TYPE == Pt2::SPECIALIZE_POINT_TYPE {
            let other = unsafe { &*(other as *const Perm<Pt2> as *const Perm<Pt>) };
            Some(self.homogeneous_cmp(other))
        } else if Pt::SPECIALIZE_POINT_TYPE < Pt2::SPECIALIZE_POINT_TYPE {
            Some(self.heterogeneous_cmp(other))
        } else {
            Some(other.heterogeneous_cmp(self).reverse())
        }
    }
}

impl<Pt: Point> Ord for Perm<Pt> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.homogeneous_cmp(other)
    }
}

impl<Pt: Point> Perm<Pt> {
    #[inline]
    fn heterogeneous_cmp<Pt2: Point>(&self, other: &Perm<Pt2>) -> cmp::Ordering {
        let mut lhs = self;
        let mut rhs = other;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs) = Self::heterogeneous_eq_cmp_fixup(lhs, rhs);
        }

        let common = lhs.degree().min(rhs.degree());

        let mut result = cmp::Ordering::Equal;

        // TODO check codegen, should use known equal slice len
        for (l, r) in lhs.as_slice()[..common]
            .iter()
            .zip(rhs.as_slice()[..common].iter())
        {
            result = l.index().cmp(&r.index());
            if result.is_ne() {
                break;
            }
        }

        if result.is_eq() {
            result = lhs.degree().cmp(&rhs.degree());
        }

        result
    }

    #[inline]
    fn homogeneous_cmp(&self, other: &Self) -> cmp::Ordering {
        let mut lhs = self;
        let mut rhs = other;
        let mut flip = false;

        if lhs.degree() != rhs.degree() {
            (lhs, rhs, flip) = Self::homogeneous_cmp_fixup(lhs, rhs);
        }

        let mut result = lhs.as_slice().cmp(&rhs.as_slice()[..lhs.as_slice().len()]);

        if result.is_eq() && lhs.degree() != rhs.degree() {
            result = cmp::Ordering::Less;
        }

        if flip {
            result.reverse()
        } else {
            result
        }
    }

    #[inline]
    #[cold] // TUNE
    fn homogeneous_cmp_fixup<'a>(
        mut lhs: &'a Self,
        mut rhs: &'a Self,
    ) -> (&'a Self, &'a Self, bool) {
        let mut flip = false;
        if lhs.degree() > rhs.degree() {
            (lhs, rhs) = (rhs, lhs);
            flip = true;
        }
        rhs = rhs.shrink_to_degree(lhs.degree());
        (lhs, rhs, flip)
    }
}

/// A possibly uninitialized permutation.
///
/// # Safety
/// As we allow safe borrowing of a Perm as a MaybeUninitPerm, it's illegal to de-initialize or
/// invalidate a MaybeUninitPerm.
#[repr(transparent)]
pub struct MaybeUninitPerm<Pt: Point> {
    points: [MaybeUninit<Pt>],
}

impl<Pt: Point> MaybeUninitPerm<Pt> {
    #[inline]
    pub fn new_mut(perm: &mut Perm<Pt>) -> &mut Self {
        // SAFETY repr(transparent) and &[T] -> &[MaybeUninit<T>] cast
        unsafe { &mut *(perm as *mut Perm<Pt> as *mut MaybeUninitPerm<Pt>) }
    }

    #[inline]
    pub fn uninit_mut(slice: &mut [MaybeUninit<Pt>]) -> &mut Self {
        // SAFETY repr(transparent)
        unsafe { &mut *(slice as *mut [MaybeUninit<Pt>] as *mut MaybeUninitPerm<Pt>) }
    }

    #[inline]
    pub fn as_slice(&self) -> &[MaybeUninit<Pt>] {
        &self.points
    }

    /// Returns a mutable slice to the possibly uninitialized slice of images.
    ///
    /// # Safety
    /// As we allow safe borrowing of a Perm as a MaybeUninitPerm, it's illegal to de-initialize or
    /// invalidate a MaybeUninitPerm.
    #[inline]
    pub unsafe fn as_mut_slice(&mut self) -> &mut [MaybeUninit<Pt>] {
        &mut self.points
    }

    /// Returns the size of the set the permutation will be defined on.
    #[inline]
    pub fn degree(&self) -> usize {
        self.points.len()
    }

    /// Initializes this permutation with a copy of a permutation.
    ///
    /// Panics when the degree of the argument is larger than the target degree.
    #[inline]
    pub fn assign_perm<Pt2: Point>(&mut self, perm: &Perm<Pt2>) {
        assert!(self.degree() >= perm.degree());
        // TODO tuned variants for same degree and/or same point types
        for (i, out) in self.points.iter_mut().enumerate() {
            *out = MaybeUninit::new(Pt::from_index(perm.index_image(i)));
        }
    }

    /// Initializes this permutation with the inverse of a permutation.
    ///
    /// Panics when the degree of the argument is larger than the target degree.
    #[inline]
    pub fn assign_inverse<Pt2: Point>(&mut self, perm: &Perm<Pt2>) {
        assert!(self.degree() >= perm.degree());
        // TODO tuned variants for same degree and/or same point types
        for i in 0..self.degree() {
            self.points[perm.index_image(i)] = MaybeUninit::new(Pt::from_index(i));
        }
    }

    /// Initializes this permutation with the composition of two permutations.
    ///
    /// The application order is left-to-right following computational group theory conventions.
    ///
    /// Panics when the degree of either argument is larger than the target degree.
    #[inline]
    pub fn assign_composition<Pt2: Point, Pt3: Point>(&mut self, lhs: &Perm<Pt2>, rhs: &Perm<Pt3>) {
        assert!(self.degree() >= lhs.degree());
        assert!(self.degree() >= rhs.degree());
        // TODO tuned variants for same degree and/or same point types
        for (i, out) in self.points.iter_mut().enumerate() {
            *out = MaybeUninit::new(Pt::from_index(rhs.index_image(lhs.index_image(i))));
        }
    }
}

#[derive(Clone, Default)]
pub struct VecPerm<Pt: Point> {
    points: Vec<Pt>,
}

impl<Pt: Point> Deref for VecPerm<Pt> {
    type Target = Perm<Pt>;

    fn deref(&self) -> &Self::Target {
        // SAFETY VecPerm has the same invariants as Perm
        unsafe { Perm::from_slice_unchecked(self.points.deref()) }
    }
}

impl<Pt: Point> DerefMut for VecPerm<Pt> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY VecPerm has the same invariants as Perm
        unsafe { Perm::from_mut_slice_unchecked(self.points.deref_mut()) }
    }
}

impl<Pt: Point> Borrow<Perm<Pt>> for VecPerm<Pt> {
    fn borrow(&self) -> &Perm<Pt> {
        self.deref()
    }
}

impl<Pt: Point> ToOwned for Perm<Pt> {
    type Owned = VecPerm<Pt>;

    fn to_owned(&self) -> Self::Owned {
        // SAFETY already guaranteed to be a permutation
        unsafe { VecPerm::from_vec_unchecked(self.as_slice().to_vec()) }
    }
}

impl<Pt: Point> fmt::Display for VecPerm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

impl<Pt: Point> fmt::Debug for VecPerm<Pt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), f)
    }
}

impl<Pt: Point> VecPerm<Pt> {
    /// Creates a `Perm` reference from a `Vec` containing the images of the first n points.
    ///
    /// Panics for non-permutation arguments.
    #[inline]
    pub fn from_vec(points: Vec<Pt>) -> Self {
        assert!(Perm::is_perm(&points)); // SAFETY precondition check
        unsafe { Self::from_vec_unchecked(points) }
    }

    /// Creates a `Perm` reference from a `Vec` containing the images of the first n points.
    ///
    /// # Safety
    /// The argument `points` must be a permutation of the points `0..points.len()`.
    #[inline]
    pub const unsafe fn from_vec_unchecked(points: Vec<Pt>) -> Self {
        Self { points }
    }

    /// Largest degree permutation that can be stored in this `VecPerm` without reallocation.
    pub fn capacity(&self) -> usize {
        self.points.capacity()
    }

    /// Increase a smaller degree to the given lower bound.
    ///
    /// Does nothing when the degree is at or above the argument degree.
    pub fn grow_degree(&mut self, degree: usize) {
        if self.degree() < degree {
            assert!(degree <= Pt::MAX_DEGREE);
            self.points
                .extend((self.points.len()..degree).map(Pt::from_index));
        }
    }

    fn check_capacity_for_assign(&mut self, degree: usize) -> &mut MaybeUninitPerm<Pt> {
        self.points.clear();
        self.points.reserve(degree);
        MaybeUninitPerm::uninit_mut(&mut self.points.spare_capacity_mut()[..degree])
    }

    /// Updates the permutation by pre-composing a transposition of two points.
    ///
    /// Extends the degree when either point is not contained in `self.points()`.
    #[inline]
    pub fn precompose_transposition(&mut self, transposition: [Pt; 2]) {
        let [a, b] = transposition;
        let max = a.max(b);
        self.grow_degree(max.index() + 1);
        self.deref_mut().precompose_transposition(transposition);
    }

    /// Updates the permutation by pre-composing a cycle.
    ///
    /// Extends the degree when any point of the cycle is not contained in `self.points()`.
    #[inline]
    pub fn precompose_cycle(&mut self, cycle: &[Pt]) {
        if let Some(max) = cycle.iter().max() {
            self.grow_degree(max.index() + 1);
            self.deref_mut().precompose_cycle(cycle);
        }
    }

    /// Updates the permutation by post-composing another permutation.
    ///
    /// Extends the degree when the argument permutation has a larger degree than this permutation.
    #[inline]
    pub fn postcompose_perm<Pt2: Point>(&mut self, other: &Perm<Pt2>) {
        self.grow_degree(other.degree());
        self.deref_mut().postcompose_perm(other);
    }

    /// Sets the permutation to the identity permutation and resets the degree to zero.
    pub fn clear(&mut self) {
        self.points.clear();
    }

    /// Assigns a copy of a permutation.
    ///
    /// Extends the degree when the degree of the argument is larger than the target degree.
    #[inline]
    pub fn assign_perm<Pt2: Point>(&mut self, perm: &Perm<Pt2>) {
        let degree = self.degree();
        let assigned_degree = perm.degree();
        let uninit = self.check_capacity_for_assign(assigned_degree);
        uninit.assign_perm(perm);
        // SAFETY follows corresponding assignment
        unsafe { self.points.set_len(assigned_degree) };
        self.grow_degree(degree);
    }

    /// Assigns the inverse of a permutation.
    ///
    /// Extends the degree when the degree of the argument is larger than the target degree.
    #[inline]
    pub fn assign_inverse<Pt2: Point>(&mut self, perm: &Perm<Pt2>) {
        let degree = self.degree();
        let assigned_degree = perm.degree();
        let uninit = self.check_capacity_for_assign(assigned_degree);
        uninit.assign_inverse(perm);
        // SAFETY follows corresponding assignment
        unsafe { self.points.set_len(assigned_degree) };
        self.grow_degree(degree);
    }

    /// Assigns the composition of two permutations.
    ///
    /// The application order is left-to-right following computational group theory conventions.
    ///
    /// Extends the degree when the degree of either argument is larger than the target degree.
    #[inline]
    pub fn assign_composition<Pt2: Point, Pt3: Point>(&mut self, lhs: &Perm<Pt2>, rhs: &Perm<Pt3>) {
        let degree = self.degree();
        let assigned_degree = lhs.degree().max(rhs.degree());
        let uninit = self.check_capacity_for_assign(assigned_degree);
        uninit.assign_composition(lhs, rhs);
        // SAFETY follows corresponding assignment
        unsafe { self.points.set_len(assigned_degree) };
        self.grow_degree(degree);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! p32 { ($($x:expr),* $(,)?) => { Perm::<u32>::from_slice(&[ $($x),* ]) }; }
    macro_rules! p16 { ($($x:expr),* $(,)?) => { Perm::<u16>::from_slice(&[ $($x),* ]) }; }

    #[test]
    fn cycles_and_iter() {
        for (slice, cycle_str) in [
            (&[0, 1, 2, 3, 4, 5], "()"),
            (&[1, 2, 3, 4, 5, 0], "(0 1 2 3 4 5)"),
            (&[0, 2, 3, 4, 5, 1], "(1 2 3 4 5)"),
            (&[0, 5, 1, 2, 3, 4], "(1 5 4 3 2)"),
            (&[1, 0, 2, 4, 5, 3], "(0 1)(3 4 5)"),
            (&[5, 4, 3, 2, 1, 0], "(0 5)(1 4)(2 3)"),
        ] {
            let perm = Perm::<u32>::from_slice(slice);
            let cycles = perm.cycles();
            assert_eq!(cycles.to_string(), cycle_str);

            let mut found = vec![];
            for c in &cycles {
                for i in 0..c.len() {
                    found.push((c[i], c[(i + 1) % c.len()]));
                }
            }

            found.sort_unstable();
            assert_eq!(found, perm.iter().moved().collect::<Vec<_>>());
            found.reverse();
            assert_eq!(found, perm.iter().moved().rev().collect::<Vec<_>>());

            let mut found = vec![];
            for c in cycles.iter().rev() {
                for i in 0..c.len() {
                    found.push((c[i], c[(i + 1) % c.len()]));
                }
            }

            found.sort_unstable();
            assert_eq!(found, perm.iter().moved().collect::<Vec<_>>());
            found.reverse();
            assert_eq!(found, perm.iter().moved().rev().collect::<Vec<_>>());

            let mut from_cycles: Vec<_> = (0..6).collect();
            let from_cycles = Perm::<u32>::from_mut_slice(from_cycles.as_mut_slice());

            for c in cycles.iter().rev() {
                from_cycles.precompose_cycle(c);
            }

            assert_eq!(perm.as_slice(), from_cycles.as_slice());
        }
    }

    #[test]
    fn homogeneous_eq() {
        assert_eq!(p32![], p32![0, 1]);
        assert_ne!(p32![], p32![1, 0]);
        assert_eq!(p32![0, 1], p32![]);
        assert_ne!(p32![1, 0], p32![]);

        assert_eq!(p32![0, 1], p32![0, 1, 2, 3]);
        assert_eq!(p32![1, 0], p32![1, 0, 2, 3]);
        assert_ne!(p32![0, 1], p32![1, 0, 2, 3]);
        assert_ne!(p32![0, 1], p32![0, 2, 1, 3]);
        assert_ne!(p32![0, 1], p32![0, 1, 3, 2]);
    }

    #[test]
    fn heterogeneous_eq() {
        assert_eq!(p32![], p16![0, 1]);
        assert_ne!(p32![], p16![1, 0]);
        assert_eq!(p32![0, 1], p16![]);
        assert_ne!(p32![1, 0], p16![]);

        assert_eq!(p32![0, 1], p16![0, 1, 2, 3]);
        assert_eq!(p32![1, 0], p16![1, 0, 2, 3]);
        assert_ne!(p32![0, 1], p16![1, 0, 2, 3]);
        assert_ne!(p32![0, 1], p16![0, 2, 1, 3]);
        assert_ne!(p32![0, 1], p16![0, 1, 3, 2]);

        assert_eq!(p16![], p32![0, 1]);
        assert_ne!(p16![], p32![1, 0]);
        assert_eq!(p16![0, 1], p32![]);
        assert_ne!(p16![1, 0], p32![]);

        assert_eq!(p16![0, 1], p32![0, 1, 2, 3]);
        assert_eq!(p16![1, 0], p32![1, 0, 2, 3]);
        assert_ne!(p16![0, 1], p32![1, 0, 2, 3]);
        assert_ne!(p16![0, 1], p32![0, 2, 1, 3]);
        assert_ne!(p16![0, 1], p32![0, 1, 3, 2]);
    }

    #[test]
    fn homogeneous_cmp() {
        use cmp::Ordering::*;
        assert_eq!(p32![].cmp(p32![0, 1]), Equal);
        assert_eq!(p32![].cmp(p32![]), Equal);
        assert_eq!(p32![0, 1].cmp(p32![]), Equal);

        assert_eq!(p32![].cmp(p32![1, 0, 2]), Less);
        assert_eq!(p32![].cmp(p32![1, 0]), Less);
        assert_eq!(p32![0, 1, 2].cmp(p32![1, 0, 2]), Less);
        assert_eq!(p32![0, 1, 2].cmp(p32![1, 0]), Less);

        assert_eq!(p32![1, 0].cmp(p32![1, 0, 3, 2, 4]), Less);
        assert_eq!(p32![1, 0].cmp(p32![1, 0, 3, 2]), Less);
        assert_eq!(p32![1, 0, 2, 3, 4].cmp(p32![1, 0, 3, 2, 4]), Less);
        assert_eq!(p32![1, 0, 2, 3, 4].cmp(p32![1, 0, 3, 2]), Less);

        assert_eq!(p32![].cmp(p32![1, 0, 2]), Less);
        assert_eq!(p32![].cmp(p32![1, 0]), Less);
        assert_eq!(p32![0, 1, 2].cmp(p32![1, 0, 2]), Less);
        assert_eq!(p32![0, 1, 2].cmp(p32![1, 0]), Less);

        assert_eq!(p32![1, 0, 3, 2, 4].cmp(p32![1, 0]), Greater);
        assert_eq!(p32![1, 0, 3, 2].cmp(p32![1, 0]), Greater);
        assert_eq!(p32![1, 0, 3, 2, 4].cmp(p32![1, 0, 2, 3, 4]), Greater);
        assert_eq!(p32![1, 0, 3, 2].cmp(p32![1, 0, 2, 3, 4]), Greater);
    }

    #[test]
    fn inhomogeneous_cmp() {
        use cmp::Ordering::*;

        let c = |a: &Perm<u16>, b: &Perm<u32>| a.partial_cmp(b).unwrap();

        assert_eq!(c(p16![], p32![0, 1]), Equal);
        assert_eq!(c(p16![], p32![]), Equal);
        assert_eq!(c(p16![0, 1], p32![]), Equal);

        assert_eq!(c(p16![], p32![1, 0, 2]), Less);
        assert_eq!(c(p16![], p32![1, 0]), Less);
        assert_eq!(c(p16![0, 1, 2], p32![1, 0, 2]), Less);
        assert_eq!(c(p16![0, 1, 2], p32![1, 0]), Less);

        assert_eq!(c(p16![1, 0], p32![1, 0, 3, 2, 4]), Less);
        assert_eq!(c(p16![1, 0], p32![1, 0, 3, 2]), Less);
        assert_eq!(c(p16![1, 0, 2, 3, 4], p32![1, 0, 3, 2, 4]), Less);
        assert_eq!(c(p16![1, 0, 2, 3, 4], p32![1, 0, 3, 2]), Less);

        assert_eq!(c(p16![], p32![1, 0, 2]), Less);
        assert_eq!(c(p16![], p32![1, 0]), Less);
        assert_eq!(c(p16![0, 1, 2], p32![1, 0, 2]), Less);
        assert_eq!(c(p16![0, 1, 2], p32![1, 0]), Less);

        assert_eq!(c(p16![1, 0, 3, 2, 4], p32![1, 0]), Greater);
        assert_eq!(c(p16![1, 0, 3, 2], p32![1, 0]), Greater);
        assert_eq!(c(p16![1, 0, 3, 2, 4], p32![1, 0, 2, 3, 4]), Greater);
        assert_eq!(c(p16![1, 0, 3, 2], p32![1, 0, 2, 3, 4]), Greater);
    }
}
