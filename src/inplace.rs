//! In-place assignment of returned values.
//!

use std::{convert::Infallible, marker::PhantomData};

/// In-place assignment of returned values.
///
/// This trait allows returning values that support both: a) overwriting assignment in-place,
/// reusing allocated resources or b) construction of newly allocated values.
///
/// To implement a function returning a value in this way, you create a new specific return type
/// that implements this trait for one or several `Output` types.
///
/// When the output type is `Sized` both options, in-place assignment and construction are
/// supported. For unsized types only in-place assignment is available.
///
/// When several functions return values that can be stored by the same set of distinct but
/// compatible types (e.g. permutations as provided by [`crate::perm`]), it is possible to use a
/// custom trait describing the interface between value-producing operations and value-storing
/// types. This trait can then be equipped with a blanket-impl for this `Inplace` trait to provide
/// the same uniform interface. To allow this without running into trait-coherence issues, the
/// `Inplace` trait has a generic `Choice` type parameter. This `Choice` type is not used by the
/// trait, but it allows otherwise potentially-overlapping blanket implementations to use a differen
/// type. On the call-site this type parameter can usually be inferred. In case of an actual overlap
/// it can be used to disambiguate between implementations.
pub trait Inplace<Output: ?Sized, Choice> {
    /// Returns the result as a newly constructed value.
    fn build(self) -> Output
    where
        Output: Sized;

    /// Assigns to `output` in-place, overwriting a previous value, reusing its resources.
    fn assign_to(self, output: &mut Output);

    /// Supplies temporary storage needed to compute the result.
    ///
    /// The value returned by `with_temp` also implements [`Inplace`] so `returned.build()` becomes
    /// `returned.with_temp(temp).build()` and `output.assign(returned)` becomes
    /// `output.assign(returned.with_temp(temp))`.
    ///
    /// This is only available if the returned valued implements the `InplaceWithTemp` trait where
    /// this functionality is implemented. This method and this trait and the [`WithTemp`] wrapper
    /// type only provide a more ergonomic API to supply temporary storage.
    #[inline]
    fn with_temp(self, temp: &mut Self::Temp) -> WithTemp<Self, Self::Temp>
    where
        Self: InplaceWithTemp<Output, Choice> + Sized,
    {
        WithTemp {
            inplace: self,
            temp,
        }
    }
}

/// In-place assignment of returned values with provided storage for temporary data.
///
/// Some computations require allocation of temporary data. When multiple such operations are
/// performed it's often possible to reuse allocated storage for such temporary data. This trait
/// extends [`Inplace`] with methods that allow supplying such existing temporary storage.
///
/// Callers should prefer `Inplace::with_temp`
pub trait InplaceWithTemp<Output: ?Sized, Choice>: Inplace<Output, Choice> {
    /// Type used to store temporary data.
    type Temp: Default;

    /// Returns the result as a newly constructed value using provided storage for temporary data.
    ///
    /// Callers may use any existing value for `temp` and implementations are not required to make
    /// any guarantees of the resulting value in `temp`. When implementations require certain
    /// invariants they can use a type for [`Self::Temp`] that enforces those.
    fn build_with_temp(self, temp: &mut Self::Temp) -> Output
    where
        Output: Sized;

    /// Assigns to `output` in-place, overwriting a previous value, reusing its resources and
    /// using provided storage for temporary data.
    ///
    /// Callers may use any existing value for `temp` and implementations are not required to make
    /// any guarantees of the resulting value in `temp`. When implementations require certain
    /// invariants they can use a type for [`Self::Temp`] that enforces those.
    fn assign_to_with_temp(self, output: &mut Output, temp: &mut Self::Temp);
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
    #[inline]
    fn build(self) -> Output
    where
        Output: Sized,
    {
        self.inplace.build_with_temp(self.temp)
    }

    #[inline]
    fn assign_to(self, output: &mut Output) {
        self.inplace.assign_to_with_temp(output, self.temp)
    }
}

/// Universal extension trait to support `target.assign(operation())` syntax.
///
/// This trait has a blanket impl for all `T` and provides an [`assign`][`Self::assign`] method
/// which delegates to [`Inplace::assign_to`], switching the order of `self` and the argument. This
/// allows you to keep the target of the assignment on the left as it would be for a direct `target
/// = ...` assignment.
pub trait AssignInplace {
    /// Assign `value` in-place, overwriting a previous value, reusing resources.
    ///
    /// Delegates to [`Inplace::assign_to`], switching the order of `self` and `value`.
    #[inline(always)]
    fn assign<Choice>(&mut self, value: impl Inplace<Self, Choice>) {
        value.assign_to(self);
    }
}

impl<T: ?Sized> AssignInplace for T {}
