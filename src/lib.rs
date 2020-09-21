//! This library will contain various computational group theory routines.
#![warn(missing_docs)]

/// Construct a `TmpVec`.
///
/// This macro forwards all arguments to [`smallvec!`][smallvec::smallvec], but ascribes the
/// resulting type to be a [`TmpVec`].
macro_rules! tmpvec {
    // By using these rules instead of a single rule with a token tree, we should get better error
    // reporting.
    ($elem:expr; $n:expr) => { { let tmp: TmpVec<_> = smallvec::smallvec![$elem; $n]; tmp } };
    ($($x:expr),*$(,)*) => { { let tmp: TmpVec<_> = smallvec::smallvec![$($x),*]; tmp } };
}

pub mod perm;

/// SmallVec alias used in various routines that need temporary storage.
///
/// Using a [`SmallVec`][smallvec::SmallVec] instead of a vec for buffers in local variables avoids
/// allocations if only little storage is needed. The size parameter of the `SmallVec` represents a
/// trade-off between stack usage and allocations overhead. Making it larger avoids more allocations
/// but also increases stack usage of any function using this. The cost of an allocation grows only
/// very slowly with increasing buffer sizes, certainly a lot slower than any non-trivial work
/// performed with the buffer. Hence increasing the size parameter has diminishing returns for
/// reducing allocation overhead. At the same time increasing stack usage not only increases the
/// danger of stack overflows, but also reduces memory locality of local variable accesses.
///
/// The current parameter was selected after performing some preliminary micro-benchmarks. It might
/// require some tuning after additional benchmarking. We also might want to introduce different
/// choices, depending on the size of `T` and how much work is performed in proportion to the actual
/// buffer size.
type TmpVec<T> = smallvec::SmallVec<[T; 128]>;
