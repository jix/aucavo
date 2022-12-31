//! Traits for arbitrary-precision integer types supported by Aucavo.
use std::fmt;

/// Read-only integer operations.
pub trait Int: fmt::Display + fmt::Debug {
    /// Whether values of this type can be negative.
    const SIGNED: bool;

    /// Returns the integer as a `usize`, if possible.
    fn as_usize(&self) -> Option<usize>;

    /// Returns the integer as an `isize`, if possible.
    fn as_isize(&self) -> Option<isize>;

    /// Returns the integer's absolute value as a `usize`, if possible.
    fn unsigned_abs_as_usize(&self) -> Option<usize>;

    /// Returns `true` when the integer is strictly negative.
    fn is_negative(&self) -> bool;

    /// Returns the euclidean divison remainder when dividing the integer by `n`.
    ///
    /// The returned values is always in the range `0..n`, but as this trait can be implemented in
    /// safe code, you may not depend on this for safety.
    fn mod_usize(&self, n: usize) -> usize;
}

impl Int for usize {
    const SIGNED: bool = false;

    fn as_usize(&self) -> Option<usize> {
        Some(*self)
    }

    fn as_isize(&self) -> Option<isize> {
        (*self).try_into().ok()
    }

    fn unsigned_abs_as_usize(&self) -> Option<usize> {
        Some(*self)
    }

    fn is_negative(&self) -> bool {
        false
    }

    fn mod_usize(&self, n: usize) -> usize {
        self % n
    }
}

impl Int for isize {
    const SIGNED: bool = false;

    fn as_usize(&self) -> Option<usize> {
        (*self).try_into().ok()
    }

    fn as_isize(&self) -> Option<isize> {
        Some(*self)
    }

    fn unsigned_abs_as_usize(&self) -> Option<usize> {
        Some(self.unsigned_abs())
    }

    fn is_negative(&self) -> bool {
        *self < 0
    }

    fn mod_usize(&self, n: usize) -> usize {
        let abs_res = self.unsigned_abs() % n;

        if *self < 0 && abs_res != 0 {
            n - abs_res
        } else {
            abs_res
        }
    }
}

#[cfg(feature = "use-num-bigint")]
mod use_num_bigint {
    use super::Int;

    impl Int for num_bigint::BigInt {
        const SIGNED: bool = true;

        fn as_usize(&self) -> Option<usize> {
            self.try_into().ok()
        }

        fn as_isize(&self) -> Option<isize> {
            self.try_into().ok()
        }

        fn unsigned_abs_as_usize(&self) -> Option<usize> {
            self.magnitude().try_into().ok()
        }

        fn is_negative(&self) -> bool {
            self.sign() == num_bigint::Sign::Minus
        }

        fn mod_usize(&self, n: usize) -> usize {
            let mut res = self % n;
            if res.is_negative() {
                res += n;
            }
            res.as_usize().unwrap()
        }
    }

    impl Int for num_bigint::BigUint {
        const SIGNED: bool = false;

        fn as_usize(&self) -> Option<usize> {
            self.try_into().ok()
        }

        fn as_isize(&self) -> Option<isize> {
            self.try_into().ok()
        }

        fn unsigned_abs_as_usize(&self) -> Option<usize> {
            self.try_into().ok()
        }

        fn is_negative(&self) -> bool {
            false
        }

        fn mod_usize(&self, n: usize) -> usize {
            (self % n).as_usize().unwrap()
        }
    }
}
