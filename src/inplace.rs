//! Operations that construct their result in-place.

use std::{convert::Infallible, marker::PhantomData};

/// Helper trait for automatically unwrapping infallible methods.
///
/// For traits with an associated `Err` type, and `try_xyz(...) -> Result<Xyz, Self::Err>` methods,
/// this trait can be used as a bound on `Self:Err` to provide `xyz(...) -> Xyz` methods.
///
/// This is used for such methods on [`Inplace`] and [`InplaceWithTemp`].
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
/// The trait [`InplaceWithTemp`] extends [`Inplace`] to allow explicit re-use of temporary storage
/// required to perform operations.
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

/// An operation that constructs its result in-place that can reuse or share temporary storage.
///
/// Some operations require allocation of temporary data. When multiple such operations are
/// performed it's often possible to reuse allocated storage for such temporary data. This trait
/// extends [`Inplace`] with methods that allow supplying such existing temporary storage.
///
/// Calling [`Self::with_temp`] bundles an operation with its temporary storage. The bundled wrapper
/// still implements `Inplace` and provides a nicer syntax when using [`AssignInplace::assign`].
pub trait InplaceWithTemp<Output: ?Sized, Choice>: Inplace<Output, Choice> {
    /// Type used to store temporary data.
    type Temp: Default;

    /// Returns the result as a newly constructed value using provided storage for temporary data.
    ///
    /// Callers may use any existing value for `temp` and implementations are not required to make
    /// any guarantees of the resulting value in `temp`. When implementations require certain
    /// invariants they can use a type for [`Self::Temp`] that enforces those.
    #[inline(always)]
    fn build_with_temp(self, temp: &mut Self::Temp) -> Output
    where
        Output: Sized,
        Self::Err: IsInfallible,
    {
        IsInfallible::unwrap_infallible(self.try_build_with_temp(temp))
    }

    /// Constructs the result in `output`, overwriting a previous value using provided storage for
    /// temporary data.
    ///
    /// Callers may use any existing value for `temp` and implementations are not required to make
    /// any guarantees of the resulting value in `temp`. When implementations require certain
    /// invariants they can use a type for [`Self::Temp`] that enforces those.
    #[inline(always)]
    fn assign_to_with_temp(self, output: &mut Output, temp: &mut Self::Temp)
    where
        Self::Err: IsInfallible,
    {
        IsInfallible::unwrap_infallible(self.try_assign_to_with_temp(output, temp))
    }

    /// Returns the result as a newly constructed value or returns an error while using provided
    /// storage for temporary data.
    fn try_build_with_temp(self, temp: &mut Self::Temp) -> Result<Output, Self::Err>
    where
        Output: Sized;

    /// Constructs the result in `output`, overwriting a previous value or returns an error while
    /// using provided storage for temporary data.
    fn try_assign_to_with_temp(
        self,
        output: &mut Output,
        temp: &mut Self::Temp,
    ) -> Result<(), Self::Err>;

    /// Supplies temporary storage needed to compute the result.
    ///
    /// The value returned by `with_temp` also implements [`Inplace`] so `returned.build()` becomes
    /// `returned.with_temp(temp).build()` and `output.assign(returned)` becomes
    /// `output.assign(returned.with_temp(temp))`.
    #[inline]
    fn with_temp(self, temp: &mut Self::Temp) -> WithTemp<Self, Self::Temp>
    where
        Self: Sized,
    {
        WithTemp {
            inplace: self,
            temp,
        }
    }
}

/// Bundles an in-place assignable result with temporary storage required to compute that result.
///
/// See also [`Inplace::with_temp`] and [`InplaceWithTemp`].
pub struct WithTemp<'a, I, T> {
    inplace: I,
    temp: &'a mut T,
}

/// Disambiguator for the [`Inplace`] impl for [`WithTemp`].
pub struct WithTempChoice<T> {
    _never: Infallible,
    _phantom: PhantomData<T>,
}

impl<I, Output, Choice> Inplace<Output, WithTempChoice<Choice>> for WithTemp<'_, I, I::Temp>
where
    I: InplaceWithTemp<Output, Choice>,
{
    type Err = I::Err;
    #[inline]
    fn build(self) -> Output
    where
        Output: Sized,
        Self::Err: IsInfallible,
    {
        self.inplace.build_with_temp(self.temp)
    }

    #[inline]
    fn assign_to(self, output: &mut Output)
    where
        Self::Err: IsInfallible,
    {
        self.inplace.assign_to_with_temp(output, self.temp)
    }

    #[inline]
    fn try_build(self) -> Result<Output, Self::Err>
    where
        Output: Sized,
    {
        self.inplace.try_build_with_temp(self.temp)
    }

    #[inline]
    fn try_assign_to(self, output: &mut Output) -> Result<(), Self::Err> {
        self.inplace.try_assign_to_with_temp(output, self.temp)
    }
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
