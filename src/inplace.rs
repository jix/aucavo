//! In-place assignment of returned values.
//!

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
}

/// Universal extension trait to support `target.assign(operation())` syntax.
///
/// This trait has a blanket impl for all `T` and provides an [`assign`][`Self::assign`] method
/// which delegates to [`Inplace::assign_to`], switching the order of `self` and the argument. This
/// allows you to keep the target of the assignment on the left as it would be for a direct `target
/// = ...` assignment.
pub trait AssignInplace<Choice> {
    /// Assign `value` in-place, overwriting a previous value, reusing resources.
    ///
    /// Delegates to [`Inplace::assign_to`], switching the order of `self` and `value`.
    #[inline(always)]
    fn assign(&mut self, value: impl Inplace<Self, Choice>) {
        value.assign_to(self);
    }
}

impl<Choice, T: ?Sized> AssignInplace<Choice> for T {}
