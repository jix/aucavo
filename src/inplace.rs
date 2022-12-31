//! Operations that construct their result in-place.

use std::convert::Infallible;

/// Helper trait for automatically unwrapping infallible methods.
///
/// For traits with an associated `Err` type, and `try_xyz(...) -> Result<Xyz, Self::Err>` methods,
/// this trait can be used as a bound on `Self:Err` to provide `xyz(...) -> Xyz` methods.
///
/// This is used for such methods on [`Inplace`].
pub trait IsInfallible: Sized {
    /// Unwrap the always present `Ok` value of an infallible result.
    fn unwrap_infallible<T>(result: Result<T, Self>) -> T;
}

impl IsInfallible for Infallible {
    #[inline(always)]
    fn unwrap_infallible<T>(result: Result<T, Self>) -> T {
        // SAFETY: Since Infallible has no variants, `result` is guaranteed to be `Ok`.
        unsafe { result.unwrap_unchecked() }
    }
}

/// An operation that constructs its result in-place.
///
/// This trait allows writing operations that can both a) construct their result in-place,
/// overwriting a previous value, reusing allocated resources or b) build the result as a new value.
///
/// To implement an operation returning a result in this way, you create a new specific return type
/// that implements this trait for one or several `Output` types.
///
/// When the output type is `Sized` both options, in-place construction and building new values are
/// supported. For unsized types only in-place assignment is available.
///
/// When several operations return values that can be stored by the same set of distinct but
/// compatible types (e.g. permutations as provided by [`crate::perm`]), it is possible to use a
/// custom trait describing the interface between value-producing operations and value-storing
/// types. This trait can then be equipped with a blanket-impl for this `Inplace` trait to provide
/// the same uniform interface. To allow this without running into trait-coherence issues, the
/// `Inplace` trait has a generic `Choice` type parameter. This `Choice` type is not used by the
/// trait, but it allows otherwise potentially-overlapping blanket implementations to use a differen
/// type. On the call-site this type parameter can usually be inferred. In case of an actual overlap
/// it can be used to disambiguate between implementations.
pub trait Inplace<Output: ?Sized, Choice>: Sized {
    /// The error type of this operation.
    type Err;

    /// Returns the result as a newly constructed value.
    ///
    /// Available for operations where [`Self::Err`] is [`Infallible`].
    #[inline(always)]
    fn build(self) -> Output
    where
        Output: Sized,
        Self::Err: IsInfallible,
    {
        IsInfallible::unwrap_infallible(self.try_build())
    }

    /// Constructs the result in `output`, overwriting a previous value, reusing its resources.
    ///
    /// Available for operations where [`Self::Err`] is [`Infallible`].
    #[inline(always)]
    fn assign_to(self, output: &mut Output)
    where
        Self::Err: IsInfallible,
    {
        IsInfallible::unwrap_infallible(self.try_assign_to(output))
    }

    /// Returns the result as a newly constructed value or returns an error.
    fn try_build(self) -> Result<Output, Self::Err>
    where
        Output: Sized;

    /// Constructs the result in `output`, overwriting a previous value or returns an error.
    ///
    /// When an error is returned, implementations may leave output in an arbitrary state as long as
    /// that state still allows overwriting the value with a subsequent successive assignment.
    fn try_assign_to(self, output: &mut Output) -> Result<(), Self::Err>;
}

/// Universal extension trait to support `target.assign(operation())` syntax.
///
/// This trait has a blanket impl for all `T` and provides an [`assign`][`Self::assign`] method
/// which delegates to [`Inplace::assign_to`], switching the order of `self` and the argument. This
/// allows you to keep the target of the assignment on the left as it would be for a direct `target
/// = ...` assignment.
pub trait AssignInplace {
    /// Assign the result of `operation` in-place, overwriting a previous value, reusing resources.
    ///
    /// Delegates to [`Inplace::assign_to`], switching the order of `self` and `operation`.
    #[inline(always)]
    fn assign<Choice>(&mut self, operation: impl Inplace<Self, Choice, Err = Infallible>) {
        operation.assign_to(self);
    }

    /// Assign the result of `operation` in-place, overwriting a previous value or returns an error.
    ///
    /// Delegates to [`Inplace::try_assign_to`], switching the order of `self` and `operation`.
    #[inline(always)]
    fn try_assign<Choice, I: Inplace<Self, Choice>>(&mut self, value: I) -> Result<(), I::Err> {
        value.try_assign_to(self)
    }
}

impl<T: ?Sized> AssignInplace for T {}
