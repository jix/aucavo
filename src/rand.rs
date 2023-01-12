//! Sampling random values.
use rand_core::{RngCore, SeedableRng};

use crate::point::Point;

/// A non-cryptographic pesudo-random number generator with a tiny state.
///
/// Currently implements the wyrand algorithm, but this may change in the future.
#[derive(Default)]
pub struct TinyRng {
    state: u64,
}

impl SeedableRng for TinyRng {
    type Seed = [u8; 8];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut new = Self {
            state: u64::from_le_bytes(seed),
        };
        new.next_u64();
        new
    }
}

impl RngCore for TinyRng {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        // Based on https://github.com/lemire/testingRNG/blob/master/source/wyrand.h
        let state = self.state;
        self.state = self.state.wrapping_add(0xa0761d6478bd642f);
        let xored = state ^ 0xe7037ed1a0b428db;
        let wide_prod = (state as u128) * (xored as u128);
        (wide_prod as u64) ^ ((wide_prod >> 64) as u64)
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        rand_core::impls::fill_bytes_via_next(self, dest)
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

/// `RngCore` extension trait to sample points and permutations.
#[allow(clippy::missing_safety_doc)] // can't be implemented by users
pub unsafe trait Sample: RngCore {
    /// Returns a random index sampled uniformly from `0..degree`.
    ///
    /// Returns `0` when the range is empty.
    #[inline]
    fn next_index(&mut self, degree: usize) -> usize {
        // Based on
        // https://lemire.me/blog/2019/06/06/nearly-divisionless-random-integer-generation-on-various-systems/
        let s: u64 = degree as u64;
        let mut x = self.next_u64();
        let mut m = (x as u128) * (s as u128);
        let mut l = m as u64;
        if l < s {
            let t = s.wrapping_neg() % s;
            while l < t {
                x = self.next_u64();
                m = (x as u128) * (s as u128);
                l = m as u64;
            }
        }

        (m >> 64) as usize
    }

    /// Returns a random point with an index sampled uniformly from `0..degree`.
    ///
    /// Returns `Pt::from_index(0)` when the range is empty.
    #[inline(always)]
    fn next_point<Pt: Point>(&mut self, degree: usize) -> Pt {
        assert!(degree <= Pt::MAX_DEGREE);
        Pt::from_index(self.next_index(degree))
    }

    /// Uniformly samples a random permutation of a given degree.
    #[inline(always)]
    fn next_perm<Pt: Point>(&mut self, degree: usize) -> crate::perm::ops::Random<Pt, Self> {
        crate::perm::ops::Random::<Pt, Self>::new(degree, self)
    }
}

// SAFETY: the default implementation does return indices that are in-bounds (unless the range is
// empty)
unsafe impl<T: RngCore> Sample for T {}

#[cfg(test)]
mod tests {
    use crate::{perm::Perm, point::P32};

    use super::*;

    #[test]
    fn random_perms() {
        let mut v: Perm<Vec<P32>> = Default::default();
        let mut r = TinyRng::default();

        for i in 1..=5 {
            let degree = i * i * 5;
            for _ in 0..10 {
                v.assign(r.next_perm(degree));
                Perm::from_images_ref(v.images()).unwrap();
            }
        }
    }
}
