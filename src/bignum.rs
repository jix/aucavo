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

macro_rules! delegate_int_impl {
    ($from:ty, $to:ty) => {
        impl Int for $from {
            const SIGNED: bool = <$to as Int>::SIGNED;

            fn as_usize(&self) -> Option<usize> {
                (*self as $to).as_usize()
            }

            fn as_isize(&self) -> Option<isize> {
                (*self as $to).as_isize()
            }

            fn unsigned_abs_as_usize(&self) -> Option<usize> {
                (*self as $to).unsigned_abs_as_usize()
            }

            fn is_negative(&self) -> bool {
                (*self as $to).is_negative()
            }

            fn mod_usize(&self, n: usize) -> usize {
                (*self as $to).mod_usize(n)
            }
        }
    };
}

delegate_int_impl!(u32, usize);
delegate_int_impl!(u16, usize);
delegate_int_impl!(u8, usize);

delegate_int_impl!(i32, isize);
delegate_int_impl!(i16, isize);
delegate_int_impl!(i8, isize);

#[cfg(target_pointer_width = "64")]
delegate_int_impl!(u64, usize);
#[cfg(target_pointer_width = "64")]
delegate_int_impl!(i64, isize);

impl<T: Int> Int for &T {
    const SIGNED: bool = T::SIGNED;

    fn as_usize(&self) -> Option<usize> {
        (*self).as_usize()
    }

    fn as_isize(&self) -> Option<isize> {
        (*self).as_isize()
    }

    fn unsigned_abs_as_usize(&self) -> Option<usize> {
        (*self).unsigned_abs_as_usize()
    }

    fn is_negative(&self) -> bool {
        (*self).is_negative()
    }

    fn mod_usize(&self, n: usize) -> usize {
        (*self).mod_usize(n)
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
