//! Aucavo is a computational group theory library for Rust.
//!
//! Currently an early work on progress.

#![warn(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![allow(clippy::comparison_chain)]

mod point;

pub use point::{Point, PointIter, PointRange};

pub mod inplace;
pub mod perm;
