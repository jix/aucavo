//! Aucavo is a computational group theory library for Rust.
//!
//! Currently an early work on progress.

#![deny(unsafe_op_in_unsafe_fn)]

#![warn(missing_docs)]
#![warn(clippy::undocumented_unsafe_blocks)]

#![allow(clippy::comparison_chain)]

pub mod cycles;
pub mod gap;
pub mod inplace;
pub mod perm;
pub mod point;
